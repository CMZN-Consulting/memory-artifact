import MemoryArtifact.Root

/-!
# The view, and serving

(31) Knowledge is not a thing in the store; it is a view, computed from the log at every startDay (design record section 2).
The serving half of this file is the lookup contract of design record section 5: a return is the queried infos
themselves, byte exact, capped at `cap` tokens, paged by span, with a cursor that says how much has been served.
-/

namespace MemoryArtifact

/-- (31) Knowledge: the derived infos of the writer that are not retired and are in the closure of the current root
(design record section 2: "the closure of the current root over derivation and relation edges, restricted to entries
the writer derived and no later edge retired"). It is knowledge as of the start of the next day: the root is the one
`startDay` appends, the memory is the one after it, and what the writer writes today becomes knowledge at the next
start of day, as the record says ("computed at every roll from history and relations"). Definition 31 says "the
derived infos" without "of the writer"; the model follows section 2, which the DA's brief names. -/
def view (Γ : Ctx) (m : Memory) : List Info :=
  let m' := startDay Γ m
  let reach := m'.closure [(root Γ m).hash]
  m'.entries.filter (fun x => decide (x.hash ∈ reach) && decide (¬m'.retired x))

/-! ## Serving: what a lookup returns -/

/-- A code for each kind, so that an info's canonical form names its kind. -/
def Kind.code : Kind → Nat
  | .night => 0 | .aside => 1 | .keep => 2 | .correction => 3 | .consolidation => 4 | .proposal => 5
  | .root => 6 | .group => 7 | .page => 8 | .dayRecord => 9 | .cursor => 10 | .notice => 11 | .answer => 12
  | .framing => 13 | .heard => 14 | .tool => 15
  | .edge .same => 20 | .edge .continues => 21 | .edge .corrects => 22 | .edge .contradicts => 23
  | .edge .supersedes => 24 | .edge .cites => 25
  | .ret .infos => 30 | .ret .span => 31 | .ret .nothing => 32 | .ret .refusal => 33 | .ret .digest => 34
  | .ret .acknowledgement => 35
  | .shelf .passage => 40 | .shelf .way => 41 | .shelf .readersPage => 42

/-- The canonical form of an info: its id, its envelope, the pointers it carries and its data, byte exact (design record
section 5: "each with its envelope and id"; an edge or a keep says what it joins or keeps). -/
def Info.canon (i : Info) : Data :=
  i.hash :: i.writer :: i.day :: i.kind.code :: i.pointers.length :: (i.pointers ++ i.data)

/-- The canonical forms of a list of infos, one after the other. -/
def canonAll (xs : List Info) : Data := xs.flatMap Info.canon

/-- Paging is by span: a stream of tokens cut into pages of at most `cap` tokens, so that an info longer than the cap is
served in pieces with offsets into its canonical form. -/
def pagesOf (cap : Nat) (d : Data) : List Data := chunks cap d

/-- The infos of the closure of a set of hashes: what a lookup "and what came of it" returns. -/
def Memory.closureInfos (m : Memory) (start : List Hash) : List Info := (m.closure start).filterMap m.resolve

/-- A closure served: its canonical form, paged by the cap. -/
def serve (Γ : Ctx) (m : Memory) (start : List Hash) : List Data :=
  pagesOf Γ.p.cap (canonAll (m.closureInfos start))

/-- (16) The part of an info's canonical form that a span names: `len` tokens from `start`. -/
def Span.slice (x : Info) (s : Span) : Data := (x.canon.drop s.start).take s.len

/-- (16, 17) A span served by pages of at most `cap` tokens. -/
def Span.pages (cap : Nat) (x : Info) (s : Span) : List Data := pagesOf cap (s.slice x)

/-- (17) Serve one more page of a span: the cursor advances by the cap, and never past the end of the span. -/
def Cursor.advance (cap : Nat) (c : Cursor) : Cursor :=
  { c with served := min c.span.len (c.served + cap) }

/-- (17) The cursor has served the whole span. -/
def Cursor.done (c : Cursor) : Prop := c.served = c.span.len

/-- Serve `n` pages of a span, starting from nothing served. -/
def Cursor.serveN (cap : Nat) (s : Span) : Nat → Cursor
  | 0 => { span := s, served := 0 }
  | n + 1 => (Cursor.serveN cap s n).advance cap

/-! ## The two lookups -/

/-- (52) What a lookup is given: a pointer, a span or words. -/
inductive Query where
  | ptr (p : Pointer)
  | span (s : Span)
  | words (w : Data)

/-- The infos a query names. -/
def Query.matches (q : Query) (i : Info) : Bool :=
  match q with
  | .ptr p => i.hash == p
  | .span s => i.hash == s.target
  | .words w => decide (w <:+: i.data)

/-- (53) Recall: a lookup over the hippocampus. It returns the infos themselves, never a digest and never a rewrite. -/
def recall (m : Memory) (q : Query) : List Info := m.hippocampus.filter q.matches

/-- (54) Reach: a lookup over the store. -/
def reach (m : Memory) (q : Query) : List Info := (m.storePrivate ++ m.storeShared).filter q.matches

end MemoryArtifact
