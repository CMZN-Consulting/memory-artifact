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
  | .question => 16 | .handOver => 17 | .stop => 18 | .call => 19 | .recipe => 26 | .given => 27 | .outcome => 28
  | .task => 29 | .say => 36 | .filed => 37 | .policy => 44
  | .edge .same => 20 | .edge .continues => 21 | .edge .corrects => 22 | .edge .contradicts => 23
  | .edge .supersedes => 24 | .edge .cites => 25
  | .ret .infos => 30 | .ret .span => 31 | .ret .nothing => 32 | .ret .refusal => 33 | .ret .digest => 34
  | .ret .acknowledgement => 35
  | .shelf .passage => 40 | .shelf .way => 41 | .shelf .readersPage => 42 | .shelf .recipes => 43

/-- The canonical form of an info: its id, its envelope, its place in the log (the arrival number), the pointers it carries
and its data, byte exact (design record section 5: "each with its envelope and id"; an edge or a keep says what it joins
or keeps; T9: the served item carries its place in the log). -/
def Info.canon (i : Info) : Data :=
  i.hash :: i.writer :: i.day :: i.kind.code :: i.seq :: i.pointers.length :: (i.pointers ++ i.data)

/-- The canonical forms of a list of infos, one after the other. -/
def canonAll (xs : List Info) : Data := xs.flatMap Info.canon

/-- Paging is by span: a stream of tokens cut into pages of at most `pg` tokens, so that an info longer than a page is
served in pieces with offsets into its canonical form. (`pg` is `Params.page`: what a return holds after its arrival
number.) -/
def pagesOf (pg : Nat) (d : Data) : List Data := chunks pg d

/-- The infos of the closure of a set of hashes: what a lookup "and what came of it" returns. -/
def Memory.closureInfos (m : Memory) (start : List Hash) : List Info := (m.closure start).filterMap m.resolve

/-- A closure served: its canonical form, paged by the page size. -/
def serve (Γ : Ctx) (m : Memory) (start : List Hash) : List Data :=
  pagesOf Γ.p.page (canonAll (m.closureInfos start))

/-- (16) The part of an info's canonical form that a span names: `len` tokens from `start`. -/
def Span.slice (x : Info) (s : Span) : Data := (x.canon.drop s.start).take s.len

/-- (16, 17) A span served by pages of at most `pg` tokens. -/
def Span.pages (pg : Nat) (x : Info) (s : Span) : List Data := pagesOf pg (s.slice x)

/-- (17) Serve one more page of a span: the cursor advances by a page, and never past the end of the span. -/
def Cursor.advance (pg : Nat) (c : Cursor) : Cursor :=
  { c with served := min c.span.len (c.served + pg) }

/-- (17) The cursor has served the whole span. -/
def Cursor.done (c : Cursor) : Prop := c.served = c.span.len

/-- Serve `n` pages of a span, starting from nothing served. -/
def Cursor.serveN (pg : Nat) (s : Span) : Nat → Cursor
  | 0 => { span := s, served := 0 }
  | n + 1 => (Cursor.serveN pg s n).advance pg

/-- (52) What a lookup is given: a pointer, a span or words. -/
inductive Query where
  | ptr (p : Pointer)
  | span (s : Span)
  | words (w : Data)
  deriving DecidableEq, Repr

/-- An info holds the words when there is at least one word and every word of the query is a token of its data (the
lexical side of a lookup by words; an empty query holds nothing). -/
def Info.holdsWords (words : Data) (i : Info) : Bool := !words.isEmpty && words.all (fun w => i.data.contains w)

end MemoryArtifact
