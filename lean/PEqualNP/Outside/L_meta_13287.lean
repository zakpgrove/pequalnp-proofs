import PEqualNP.Defs

-- The signed circuit certificate and the four-input cofactor are adapted from edmoreno’s proof of L-meta-12152.
-- Pinning inputs 4 and 5 to true leaves a relabeling of that cofactor. Each pinned input is essential.
namespace PEqualNP.Outside.L_meta_13287.Certificate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- ============================================================
-- 1. Polymorphic Wire / Reach / Run / Contraction (free NOT)
-- ============================================================

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d = 0 then combine false a b
  else if d = 1 then combine true a b
  else if d = 2 then combine false a (inv b)
  else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ inv v ∈ pool

def supply {R} (pool xs : List (Wire R)) : Prop := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R),
      Reach roots p bank ∧ Available bank a ∧ Available bank b ∧ c = combine op a b :: bank

theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl

theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool)
    (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p + 1) (combine op a b :: bank) :=
  ⟨op, bank, a, b, h, ha, hb, rfl⟩

theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p + 1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero => obtain rfl := h; exact start
  | succ p ih => obtain ⟨op, bank, a, b, h, ha, hb, rfl⟩ := h; exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x :: xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧
      Run goal s (comb op a b :: kept ka a (kept kb b rest))

theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _

theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h
    exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩

theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)}
    (op : Nat) (hd : op < 4) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) :
    Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩

theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs),
      motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : op < 4) (ka kb : Bool)
      (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s + 1) (a :: b :: rest) (Run.two op hd ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, p, h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_append {R} (a b : List (Wire R)) : mass (a ++ b) = mass a + mass b := by simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a) = a := by funext r; simp [inv]

theorem cost_inv {R} (a : Wire R) : cost (inv a) = cost a := by
  have hiff : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a
  · simp only [cost, if_pos h, if_pos (hiff.mpr h)]
  · simp only [cost, if_neg h, if_neg (fun x => h (hiff.mp x))]

theorem avail_inv {R} {bank : List (Wire R)} {a} (h : Available bank a) : Available bank (inv a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr ((inv_inv' a).symm ▸ h))
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

theorem op_four {d : Nat} (h : d < 4) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega

theorem comb_prime {R} {bank : List (Wire R)} {d a b} (hd : d < 4)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  rcases op_four hd with rfl | rfl | rfl | rfl
  · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨false, a, inv b, rfl, ha, avail_inv hb, rfl, cost_inv b⟩
  · exact ⟨false, inv a, b, rfl, avail_inv ha, hb, cost_inv a, rfl⟩

theorem extend_comb {R} (roots : List (Wire R)) {p bank a b} (d) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (comb d a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  obtain ⟨op, x, y, e, hx, hy, cx, cy⟩ := comb_prime hd ha hb
  rw [e, ← cx, ← cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons, restrict_kept, restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons, List.length_cons, cost, if_pos ha, ih (fun x hx => hc x (by simp [hx]))]
    omega

-- Circuit execution directly to Reach (for any row type R)
def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def evalWire {R} (w : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map fun i => (w.getD i (fun _ => false)) r)

def execWires {R} (gs : List Gate) (w : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun l g => l ++ [evalWire l g]) w

theorem execWires_at {R} (gs : List Gate) (w : List (Wire R)) (r : R) :
    (execWires gs w).map (fun f => f r) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execWires gs (w ++ [evalWire w g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons, List.map_append, List.map_singleton]
    congr 2; congr 1; unfold evalWire; congr 1
    apply List.map_congr_left; intro i _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? <;> rfl

theorem avail_getD {R} {bank w : List (Wire R)} (hs : supply bank w) (i : Nat) :
    Available bank (w.getD i (fun _ => false)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (Or.inl ⟨false, rfl⟩)
  | some f => exact hs f (List.mem_of_getElem? h)

theorem circuit_reach {R} (roots : List (Wire R)) (gs : List Gate) (w : List (Wire R))
    (p : Nat) (bank : List (Wire R))
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hr : Reach roots p bank) (hs : supply bank w) :
    ∃ q next, q ≤ p + gs.countP (fun g => !isNot g) ∧ Reach roots q next ∧ supply next (execWires gs w) := by
  induction gs generalizing w p bank with
  | nil => exact ⟨p, bank, by simp, hr, hs⟩
  | cons g gs ih =>
    obtain ⟨ho, hl⟩ := legal g (by simp)
    have hstep : ∃ p' bank', p' ≤ p + (if isNot g then 0 else 1) ∧
        Reach roots p' bank' ∧ supply bank' (w ++ [evalWire w g]) := by
      have addAvail {v : Wire R} (hv : Available bank v) :
          ∃ p' bank', p' ≤ p + (if isNot g then 0 else 1) ∧ Reach roots p' bank' ∧ supply bank' (w ++ [v]) :=
        ⟨p, bank, by omega, hr, fun a ha => by rcases List.mem_append.mp ha with h | h; exact hs a h; exact List.mem_singleton.mp h ▸ hv⟩
      obtain ⟨op, l⟩ := g
      rcases ho with rfl | rfl | rfl
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨true, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          cases l with
          | nil =>
            have eq : evalWire w ⟨.and, [i]⟩ = w.getD i (fun _ => false) := by
              funext r; simp [evalWire, GateOp.eval]
            rw [eq]; exact addAvail (avail_getD hs i)
          | cons j l =>
            cases l with
            | cons _ _ => simp at hl
            | nil =>
              have eq : evalWire w ⟨.and, [i, j]⟩ = combine false (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) := by
                funext r; simp [evalWire, GateOp.eval, combine]
              rw [eq]
              refine ⟨p + 1, _, by simp [isNot], Reach.two false hr (avail_getD hs i) (avail_getD hs j), ?_⟩
              intro a ha; rcases List.mem_append.mp ha with h | h
              · exact available_cons _ (hs a h)
              · rw [List.mem_singleton.mp h]; exact Or.inl (by simp)
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨false, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          cases l with
          | nil =>
            have eq : evalWire w ⟨.or, [i]⟩ = w.getD i (fun _ => false) := by
              funext r; simp [evalWire, GateOp.eval]
            rw [eq]; exact addAvail (avail_getD hs i)
          | cons j l =>
            cases l with
            | cons _ _ => simp at hl
            | nil =>
              have eq : evalWire w ⟨.or, [i, j]⟩ = combine true (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) := by
                funext r; simp [evalWire, GateOp.eval, combine]
              rw [eq]
              refine ⟨p + 1, _, by simp [isNot], Reach.two true hr (avail_getD hs i) (avail_getD hs j), ?_⟩
              intro a ha; rcases List.mem_append.mp ha with h | h
              · exact available_cons _ (hs a h)
              · rw [List.mem_singleton.mp h]; exact Or.inl (by simp)
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨true, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          have eq : evalWire w ⟨.not, i :: l⟩ = inv (w.getD i (fun _ => false)) := by
            funext r; simp [evalWire, GateOp.eval, inv]
          rw [eq]; exact addAvail (avail_inv (avail_getD hs i))
    obtain ⟨p', bank', hp', hr', hs'⟩ := hstep
    obtain ⟨q, next, hq, hreq, hsup⟩ := ih (w ++ [evalWire w g]) p' bank' (fun a ha => legal a (by simp [ha])) hr' hs'
    refine ⟨q, next, ?_, hreq, hsup⟩
    rw [List.countP_cons]; cases hn : isNot g <;> simp [hn] at hp' ⊢ <;> omega

-- ============================================================
-- 2. BitVec N (polymorphic for N=64 and N=128) Live & Lower
-- ============================================================

section BitVecEngine
variable {N : Nat} [NeZero N]

def zeroBV : BitVec N := 0
def oneBV : BitVec N := BitVec.allOnes N
def negBV (a : BitVec N) : BitVec N := ~~~a
def binBV (d : Nat) (a b : BitVec N) : BitVec N :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else if d = 2 then a &&& ~~~b else ~~~a &&& b
def properBV (a : BitVec N) : Prop := a ≠ zeroBV ∧ a ≠ oneBV
def flipOp (d : Nat) := if d = 2 then 3 else if d = 3 then 2 else d
def bitBV (i : Fin N) (a : BitVec N) : Bool := a.getLsbD i.val

theorem bitBV_zero (i : Fin N) : bitBV i (zeroBV (N := N)) = false := by simp [bitBV, zeroBV]
theorem bitBV_one (i : Fin N) : bitBV i (oneBV (N := N)) = true := by
  unfold bitBV oneBV; rw [BitVec.getLsbD_allOnes]; simp
theorem bitBV_neg (i : Fin N) (a : BitVec N) : bitBV i (negBV a) = !(bitBV i a) := by
  simp [bitBV, negBV, i.isLt]
theorem bitBV_bin (i : Fin N) (d : Nat) (a b : BitVec N) :
    bitBV i (binBV d a b) =
      (if d = 0 then bitBV i a && bitBV i b else if d = 1 then bitBV i a || bitBV i b else
       if d = 2 then bitBV i a && !(bitBV i b) else !(bitBV i a) && bitBV i b) := by
  unfold binBV; split_ifs <;> simp [bitBV, i.isLt]
theorem bitBV_ext {a b : BitVec N} (h : ∀ i : Fin N, bitBV i a = bitBV i b) : a = b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j, hj⟩

theorem binBV_flip {d : Nat} (h : d < 4) (a b : BitVec N) :
    binBV d a b = binBV (flipOp d) b a := by
  rcases op_four h with rfl | rfl | rfl | rfl <;> simp [binBV, flipOp, BitVec.and_comm, BitVec.or_comm]
theorem flipOp_lt {d : Nat} (h : d < 4) : flipOp d < 4 := by
  rcases op_four h with rfl | rfl | rfl | rfl <;> decide

def nrmBV (a : BitVec N) : BitVec N := if a.getLsbD 0 then negBV a else a
theorem nrmBV_bit0 (a : BitVec N) : (nrmBV a).getLsbD 0 = false := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases h : a.getLsbD 0 <;>
    simp only [nrmBV, negBV, h, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_not, hpos, decide_true, Bool.true_and, Bool.not_true]
theorem nrmBV_id {a : BitVec N} (h : a.getLsbD 0 = false) : nrmBV a = a := by simp [nrmBV, h]
theorem nrmBV_neg (a : BitVec N) : nrmBV (negBV a) = nrmBV a := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases h : a.getLsbD 0 <;>
    simp only [nrmBV, negBV, h, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_not, hpos, decide_true, Bool.true_and, Bool.not_true, Bool.not_false, BitVec.not_not]
theorem properBV_neg {a : BitVec N} (h : properBV (negBV a)) : properBV a := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h.2 (by simp [negBV, zeroBV, oneBV])
  · rintro rfl; exact h.1 (by simp [negBV, zeroBV, oneBV])
theorem properBV_nrm {a : BitVec N} (h : properBV (nrmBV a)) : properBV a := by
  unfold nrmBV at h
  split at h
  · exact properBV_neg h
  · exact h
theorem nrmBV_ne_one (a : BitVec N) : nrmBV a ≠ oneBV := by
  intro h; have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 := nrmBV_bit0 a; rw [h] at h1; simp [oneBV, hpos] at h1

def primeBV (d : Bool) (a b : BitVec N) : BitVec N := if d then a ||| b else a &&& b
theorem bitBV_prime (i : Fin N) (d : Bool) (a b : BitVec N) :
    bitBV i (primeBV d a b) = (if d then bitBV i a || bitBV i b else bitBV i a && bitBV i b) := by
  cases d <;> simp [primeBV, bitBV]

theorem nrmBV_prime (d : Bool) (a b : BitVec N) :
    ∃ e, e < 4 ∧ nrmBV (primeBV d a b) = binBV e (nrmBV a) (nrmBV b) := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨if d then (if a.getLsbD 0 then (if b.getLsbD 0 then 0 else 2) else (if b.getLsbD 0 then 3 else 1))
    else (if a.getLsbD 0 then (if b.getLsbD 0 then 1 else 3) else (if b.getLsbD 0 then 2 else 0)), ?_, ?_⟩
  · split_ifs <;> omega
  · apply bitBV_ext; intro i
    cases d <;> cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
      simp only [nrmBV, primeBV, binBV, negBV, bitBV, ha, hb, BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_not, i.isLt, hpos, decide_true, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true, Bool.false_eq_true,
        Bool.not_true, Bool.not_false, ite_true, ite_false, show (3 : Nat) ≠ 2 by decide,
        OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.one_ne_zero] <;>
      cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> rfl

def LiveBV (target : BitVec N) : Nat → Finset (BitVec N) → Prop
  | 0, S => S = {target} ∧ properBV target
  | k + 1, S => ∃ (U : Finset (BitVec N)) (a b : BitVec N) (d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ properBV a ∧ properBV b ∧ a ≠ b ∧
      binBV d a b ∉ insert a (insert b U) ∧ LiveBV target k (insert (binBV d a b) U)

theorem LiveBV.stop {target : BitVec N} (hp : properBV target) : LiveBV target 0 {target} := ⟨rfl, hp⟩
theorem LiveBV.binary {target : BitVec N} {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat}
    (hd : d < 4) (ha : properBV a) (hb : properBV b) (hab : a ≠ b)
    (hfresh : binBV d a b ∉ insert a (insert b U)) (tail : LiveBV target k (insert (binBV d a b) U)) :
    LiveBV target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

theorem LiveBV.ind {target : BitVec N} {motive : ∀ (k : Nat) (S : Finset (BitVec N)), LiveBV target k S → Prop}
    (stop : ∀ (hp : properBV target), motive 0 {target} (LiveBV.stop hp))
    (binary : ∀ {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat} (hd : d < 4)
      (ha : properBV a) (hb : properBV b) (hab : a ≠ b)
      (hfresh : binBV d a b ∉ insert a (insert b U)) (tail : LiveBV target k (insert (binBV d a b) U)),
      motive k (insert (binBV d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBV.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset (BitVec N)} (h : LiveBV target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih => obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h; exact binary hd ha hb hab hf tail (ih tail)

theorem liveBV_proper {target : BitVec N} {k S} (h : LiveBV target k S) : ∀ a ∈ S, properBV a := by
  induction h using LiveBV.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveBV_size {target : BitVec N} {k S} (h : LiveBV target k S) : S.card ≤ k + 1 := by
  induction h using LiveBV.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : binBV d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def representedBV (w : List (BitVec N)) (v : BitVec N) : Prop := v ∈ w ∨ ¬properBV v
def ReprBV (w : List (BitVec N)) (v : BitVec N) : Prop := representedBV w (nrmBV v)
def witnessBV (w : List (BitVec N)) (z : BitVec N) : Prop :=
  ∃ d a b, d < 4 ∧ a ∈ w ∧ b ∈ w ∧ properBV a ∧ properBV b ∧ a ≠ b ∧ z = binBV d a b

private lemma binBV_laws (a : BitVec N) :
    binBV 0 a oneBV = a ∧ binBV 1 a zeroBV = a ∧
    binBV 0 a zeroBV = zeroBV ∧ binBV 1 a oneBV = oneBV ∧
    binBV 0 a a = a ∧ binBV 1 a a = a ∧ binBV 2 a a = zeroBV ∧ binBV 3 a a = zeroBV ∧
    binBV 2 a zeroBV = a ∧ binBV 3 zeroBV a = a ∧ binBV 2 zeroBV a = zeroBV ∧ binBV 3 a zeroBV = zeroBV ∧
    binBV 0 zeroBV a = zeroBV ∧ binBV 1 zeroBV a = a ∧
    binBV 0 oneBV a = a ∧ binBV 1 oneBV a = oneBV := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bitBV_ext <;> intro i <;>
    simp [bitBV_bin, bitBV_zero, bitBV_one]

private lemma operandBV_cases {w : List (BitVec N)} {a : BitVec N} (h : representedBV w a) :
    a = zeroBV ∨ a = oneBV ∨ a ∈ w ∧ properBV a := by
  by_cases hz : a = zeroBV; · exact Or.inl hz
  by_cases ho : a = oneBV; · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

private lemma binBV_rep {w : List (BitVec N)} {a b : BitVec N} (d : Nat) (hd : d < 4)
    (ha : representedBV w a) (hb : representedBV w b) (no : a ≠ oneBV ∧ b ≠ oneBV) :
    representedBV w (binBV d a b) ∨ witnessBV w (binBV d a b) := by
  have rz : representedBV w zeroBV := Or.inr (fun h => h.1 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := binBV_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := binBV_laws b
  by_cases he : a = b
  · subst b; left
    rcases op_four hd with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operandBV_cases ha with rfl | rfl | ⟨ham, hap⟩
  · left; rcases op_four hd with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · exact absurd rfl no.1
  rcases operandBV_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · left; rcases op_four hd with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · exact absurd rfl no.2
  exact Or.inr ⟨d, a, b, hd, ham, hbm, hap, hbp, he, rfl⟩

theorem primeBV_rep {w : List (BitVec N)} {a b : BitVec N} (d : Bool)
    (ha : ReprBV w a) (hb : ReprBV w b) :
    ReprBV w (primeBV d a b) ∨ witnessBV w (nrmBV (primeBV d a b)) := by
  obtain ⟨e, he, eq⟩ := nrmBV_prime d a b
  unfold ReprBV; rw [eq]
  exact binBV_rep e he ha hb ⟨nrmBV_ne_one a, nrmBV_ne_one b⟩

theorem reprBV_const {w : List (BitVec N)} {v : BitVec N} (h : v = zeroBV ∨ v = oneBV) : ReprBV w v := by
  refine Or.inr fun hp => ?_
  have := properBV_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

private lemma pullBV_gate {target : BitVec N} {w : List (BitVec N)} {z : BitVec N} {k S c}
    (h : LiveBV target k S) (hz : representedBV w z ∨ (c = 1 ∧ witnessBV w z))
    (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ LiveBV target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha; rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveBV_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binBV d a b)
        have ht : LiveBV target k (insert (binBV d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
          obtain ⟨hne, hmv⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : binBV d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, LiveBV.binary hd pa pb hab hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha

def observeBV (a : BitVec N) : Wire (Fin N) := fun r => bitBV r a
def tableBV (f : Wire (Fin N)) : BitVec N :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem bitBV_table (f : Wire (Fin N)) (r : Fin N) : bitBV r (tableBV f) = f r := by
  simp only [bitBV, tableBV, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]
theorem tableBV_observe (v : BitVec N) : tableBV (observeBV v) = v :=
  bitBV_ext fun r => bitBV_table (observeBV v) r
theorem observeBV_table (f : Wire (Fin N)) : observeBV (tableBV f) = f :=
  funext fun r => bitBV_table f r
theorem obsBV_neg (a : BitVec N) : observeBV (negBV a) = inv (observeBV a) :=
  funext fun r => bitBV_neg r a
theorem obsBV_bin (d : Nat) (a b : BitVec N) : observeBV (binBV d a b) = comb d (observeBV a) (observeBV b) := by
  funext r; simp only [observeBV, bitBV_bin, comb]; split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α) (hn : l.Nodup) (ha : a ∉ l) :
    (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin {α : Type} [DecidableEq α] (k : Bool) (a : α) (l : List α) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by cases k <;> simp [kept]

theorem list_runBV {T : BitVec N} {k S} (h : LiveBV T k S) (v : List (BitVec N))
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observeBV T) k (v.map observeBV) := by
  classical
  induction h using LiveBV.ind generalizing v with
  | stop _ =>
    have eq : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simpa [eqv])
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd _ _ hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : binBV d a b ∉ tail := fun hz =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (binBV d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((binBV d a b :: kept ka a (kept kb b rest)).map observeBV) at progress
    rw [List.map_cons, map_kept, map_kept, obsBV_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j; by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem tableBV_inv (f : Wire (Fin N)) : tableBV (inv f) = negBV (tableBV f) := by
  rw [← tableBV_observe (negBV (tableBV f)), obsBV_neg, observeBV_table]
theorem tableBV_prime (d : Bool) (f g : Wire (Fin N)) :
    tableBV (combine d f g) = primeBV d (tableBV f) (tableBV g) := by
  apply bitBV_ext; intro r; rw [bitBV_table, bitBV_prime, bitBV_table, bitBV_table]; cases d <;> rfl

theorem availableBV_rep {bank : List (Wire (Fin N))} {a} (h : Available bank a) :
    ReprBV ((bank.map tableBV).map nrmBV) (tableBV a) := by
  rcases h with hm | ⟨b, rfl⟩ | hm
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply reprBV_const; cases b
    · exact Or.inl (bitBV_ext fun i => (bitBV_table _ i).trans (bitBV_zero i).symm)
    · exact Or.inr (bitBV_ext fun i => (bitBV_table _ i).trans (bitBV_one i).symm)
  · refine Or.inl ?_; rw [← nrmBV_neg, ← tableBV_inv a]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reachBV_live_sub {roots : List (Wire (Fin N))} {p bank}
    (h : Reach roots p bank) {T k S} (run : LiveBV T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map tableBV).map nrmBV) :
    ∃ l V, l ≤ p + k ∧ LiveBV T l V ∧ ∀ a ∈ V, a ∈ (roots.map tableBV).map nrmBV := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, tableBV_prime] at sub
    have rep := primeBV_rep d (availableBV_rep ha) (availableBV_rep hb)
    obtain ⟨k', S', hk, run', sub'⟩ := pullBV_gate (c := 1) run (rep.imp id (fun h => ⟨rfl, h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩

def plainWordBV (a : BitVec N) : Bool := !(a.getLsbD 0)
theorem nrmBV_map {w : List (BitVec N)} (h : w.all plainWordBV = true) : w.map nrmBV = w := by
  have e : w.map nrmBV = w.map id := List.map_congr_left fun a ha =>
    nrmBV_id (by simpa [plainWordBV] using List.all_eq_true.mp h a ha)
  rw [e, List.map_id]

theorem reachBV_live {roots : List (BitVec N)} {p bank T}
    (hp : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true)
    (h : Reach (roots.map observeBV) p bank) (hit : Available bank (observeBV T)) :
    ∃ k S, k ≤ p ∧ LiveBV T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := availableBV_rep hit
  rw [tableBV_observe] at hm
  unfold ReprBV at hm
  rw [nrmBV_id (by simpa [plainWordBV] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := reachBV_live_sub h (LiveBV.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map observeBV).map tableBV = roots := by
    simp [List.map_map, Function.comp_def, tableBV_observe]
  rw [e, nrmBV_map nR] at hs
  exact hs

theorem liveBV_row_diff {T : BitVec N} {k S} (h : LiveBV T k S) {r s : Fin N}
    (diff : bitBV r T ≠ bitBV s T) : ∃ a ∈ S, bitBV r a ≠ bitBV s a := by
  induction h using LiveBV.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d _ _ _ _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bitBV r a = bitBV s a
      · refine ⟨b, by simp, fun beq => hd (by rw [bitBV_bin, bitBV_bin, aeq, beq])⟩
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem rawBV_required {T : BitVec N} {k S} (h : LiveBV T k S) (roots : List (BitVec N)) (a : BitVec N)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Fin N) (diff : bitBV r T ≠ bitBV s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bitBV r v = bitBV s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := liveBV_row_diff h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def LowerBV (roots : List (BitVec N)) (T : BitVec N) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observeBV) p bank → Available bank (observeBV T) → L ≤ p

def ImpossibleBV (T : BitVec N) (cap : Nat) (S : Finset (BitVec N)) : Prop :=
  ∀ k, k ≤ cap → ¬LiveBV T k S

def EssentialBV (T : BitVec N) (roots : List (BitVec N)) (a : BitVec N) : Prop :=
  ∃ r s : Fin N, bitBV r T ≠ bitBV s T ∧ ∀ v ∈ roots, v ≠ a → bitBV r v = bitBV s v

theorem lowerBV_impossible {roots : List (BitVec N)} {T : BitVec N} {L : Nat}
    (hp : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true)
    (essential : ∀ a ∈ roots, EssentialBV T roots a)
    (noRun : ImpossibleBV T L roots.toFinset) : LowerBV roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := reachBV_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := essential _ hm
    exact rawBV_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observeBV_proper {v : BitVec N} (hv : properBV v) : ¬Constant (observeBV v) := by
  rintro ⟨b, h⟩
  have hr : representedBV ([] : List (BitVec N)) v := by
    cases b
    · exact Or.inr fun hp => hp.1 (bitBV_ext fun i => (congrFun h i).trans (bitBV_zero i).symm)
    · exact Or.inr fun hp => hp.2 (bitBV_ext fun i => (congrFun h i).trans (bitBV_one i).symm)
  exact (hr.resolve_left (by simp)) hv

end BitVecEngine

theorem lowerBV_slice {N M : Nat} [NeZero N] [NeZero M]
    {roots : List (BitVec N)} {other : List (BitVec M)} {T : BitVec N} {G : BitVec M}
    (pT : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true) (pG : properBV G)
    (r : Fin M → Fin N) (eq : restrictRows r (observeBV T) = observeBV G)
    (covered : ∀ a ∈ roots, Available (other.map observeBV) (restrictRows r (observeBV a)))
    (singles : Finset (BitVec N)) (necessary : ∀ a ∈ singles, EssentialBV T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictRows r (observeBV a)))
    (L : Nat) (prior : LowerBV other G L) : LowerBV roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k, S, hk, run, sub⟩ := reachBV_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs; obtain ⟨i, j, hd, hiso⟩ := necessary a hs
    exact rawBV_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := list_runBV run front nd fe
  have supp : supply (other.map observeBV) ((front.map observeBV).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (eq ▸ observeBV_proper pG) Reach.start supp (L := L) (eq ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observeBV).map (restrictRows r)) := by
    simp only [front, List.map_append, mass_append]
    let xs := (singles.toList.map observeBV).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass xs + _; rw [sz]; omega
  omega

-- ============================================================
-- 3. 6-variable (BitVec 64) Engine, Slices, Pools & CutCheck
-- ============================================================

abbrev Sig := BitVec 64
abbrev Row := Fin 64

def x0 : Sig := 0xaaaaaaaaaaaaaaaa#64
def x1 : Sig := 0xcccccccccccccccc#64
def x2 : Sig := 0xf0f0f0f0f0f0f0f0#64
def x3 : Sig := 0xff00ff00ff00ff00#64
def x4 : Sig := 0xffff0000ffff0000#64
def x5 : Sig := 0xffffffff00000000#64
def allVars6 : List Sig := [x0, x1, x2, x3, x4, x5]

def rawOf (vmask : Nat) : List Sig :=
  ([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
    if vmask.testBit i then some (allVars6.getD i 0) else none

theorem rawOf_nodup (m : Nat) : (rawOf m).Nodup := by
  unfold rawOf
  have h : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      (([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
        if (match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5)
        then some (allVars6.getD i 0) else none).Nodup := by decide +kernel
  exact h (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3) (m.testBit 4) (m.testBit 5)

def rename6 (f : Row → Row) (a : Sig) : Sig := tableBV fun r => bitBV (f r) a
theorem bit6_rename (f : Row → Row) (a : Sig) (r : Row) : bitBV r (rename6 f a) = bitBV (f r) a :=
  bitBV_table _ _
theorem observe6_rename (f : Row → Row) (a : Sig) : observeBV (rename6 f a) = restrictRows f (observeBV a) := by
  funext r; exact bit6_rename f a r
theorem rename6_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename6 f (binBV d a b) = binBV d (rename6 f a) (rename6 f b) := by
  apply bitBV_ext; intro r; simp only [bit6_rename, bitBV_bin]
theorem rename6_const (f : Row → Row) : rename6 f zeroBV = zeroBV ∧ rename6 f oneBV = oneBV := by
  constructor <;> apply bitBV_ext <;> intro r
  · exact (bit6_rename f zeroBV r).trans ((bitBV_zero _).trans (bitBV_zero r).symm)
  · exact (bit6_rename f oneBV r).trans ((bitBV_one _).trans (bitBV_one r).symm)
theorem rename6_inj (f : Row → Row) (onto : Function.Surjective f) : Function.Injective (rename6 f) := by
  intro a b h; apply bitBV_ext; intro j
  obtain ⟨r, hr⟩ := onto j
  have he := congrArg (bitBV r) h
  rw [bit6_rename, bit6_rename, hr] at he; exact he

theorem live6_rename {T : Sig} {k S} (h : LiveBV T k S) (f : Row → Row) (onto : Function.Surjective f) :
    LiveBV (rename6 f T) k (S.image (rename6 f)) := by
  have inj := rename6_inj f onto
  obtain ⟨fz, fo⟩ := rename6_const f
  have pp (v : Sig) (p : properBV v) : properBV (rename6 f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)), fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using LiveBV.ind with
  | stop hp => simpa using LiveBV.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename6 f (binBV d a b) ∉ (insert a (insert b U)).image (rename6 f) := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, rename6_bin] at fresh ih ⊢
    exact LiveBV.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

def rowPerm (p : List Nat) (r : Row) : Row :=
  let v := ([0, 1, 2, 3, 4, 5] : List Nat).foldl
    (fun acc i => if r.val.testBit (p.getD i 0) then acc ||| (1 <<< i) else acc) 0
  ⟨v % 64, Nat.mod_lt _ (by decide)⟩

def sigPerm (p : List Nat) (a : Sig) : Sig := rename6 (rowPerm p) a

def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (63 ^^^ (z ||| o))) ||| (o &&& 63)) % 64, Nat.mod_lt _ (by decide)⟩

def subcube6 (z o : Nat) : Sig :=
  tableBV fun r => ((r.val &&& z) == 0) && ((r.val &&& o) == (o &&& 63))

def properB (T : Sig) : Bool := T != zeroBV && T != oneBV
theorem proper_of {T : Sig} (h : properB T = true) : properBV T := by
  simpa only [properB, properBV, Bool.and_eq_true, bne_iff_ne] using h

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),
    (∀ r, bitBV (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observeBV) (restrictRows f (observeBV a))) ∧
    ¬Constant (restrictRows f (observeBV T)) ∧
    LowerBV roots (rename6 f T) L

def masked (d a : Sig) : Sig := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zeroBV || m == d || (pool.map (masked d)).any (fun v => v == m) ||
    (let c := masked d (negBV a); (pool.map (masked d)).any (fun v => v == c))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = masked d b) : restrictRows f (observeBV a) = restrictRows f (observeBV b) := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = bitBV (f r) b
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = zeroBV) : restrictRows f (observeBV a) = fun _ => false := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = false; rw [bitBV_zero] at h
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observeBV a) = fun _ => true := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = true; rw [dom r] at h
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) : Prop :=
  ∀ a ∈ pool, Available bank (restrictRows f (observeBV a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bitBV (f r) d = true) (sup : poolSupply f bank pool)
    (h : availableB d pool a = true) : Available bank (restrictRows f (observeBV a)) := by
  simp only [availableB, List.any_map, Function.comp_def, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with ((hz | ho) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one dom ho⟩)
  · exact masked_eq dom he ▸ sup v hv
  · have h := avail_inv (masked_eq dom he ▸ sup v hv)
    rw [obsBV_neg] at h
    have e : inv (restrictRows f (inv (observeBV a))) = restrictRows f (observeBV a) := by
      funext r; simp [inv, restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) : Sig := binBV c.1 c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) : Bool :=
  decide (c.1 < 4) && availableB d pool c.2.1 && availableB d pool c.2.2

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bitBV (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime valid.1.1 (availableB_sound dom hs valid.1.2)
    (availableB_sound dom hs valid.2)
  refine ⟨_, Reach.two op hp hx hy, ?_⟩
  intro a hm; rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal, obsBV_bin, restrict_comb, e]; exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c :: cs => if choiceOK d pool c then makePool d (choiceVal c :: pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bitBV (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok; split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction

def isMaskedConst (d a : Sig) : Bool := masked d a == zeroBV || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bitBV (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConst d) ≤ mass ((ws.map observeBV).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConst d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observeBV a)) := by
        have hh : masked d a = zeroBV ∨ masked d a = d := by
          simpa only [isMaskedConst, Bool.or_eq_true, beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false, masked_zero dom hz⟩
        · exact ⟨true, masked_one dom ho⟩
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

abbrev BoundPool := Sig × Nat × Nat × List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bitBV (f r) c.1 = true) ∧ ¬Constant (restrictRows f (observeBV T)) ∧
    LowerBV roots (rename6 f T) c.2.1 ∧
    Reach (roots.map observeBV) c.2.2.1 bank ∧ poolSupply f bank c.2.2.2

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T (d, lb, cs.length, ws) := by
  obtain ⟨f, roots, dom, sup, nc, prior⟩ := h
  obtain ⟨bank, hr, hs⟩ := makePool_sound dom (Reach.start (roots := roots.map observeBV)) sup cs build
  exact ⟨f, roots, bank, dom, nc, prior, by simpa using hr, hs⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.1 c.2.2.2 a = true)
    (buy : if paid then choiceOK c.1 c.2.2.2 choice = true else availableB c.1 c.2.2.2 (choiceVal choice) = true)
    (bound : k + c.2.2.1 + paid.toNat < c.2.1 + (choiceVal choice :: rest).countP (isMaskedConst c.1))
    (nd : (choiceVal choice :: rest).Nodup) :
    ImpossibleBV T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  let ws := choiceVal choice :: rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observeBV) n out)
      (zs : poolSupply f out ws) (le : n = c.2.2.1 + paid.toNat) : False := by
    have covered : supply out ((ws.map observeBV).map (restrictRows f)) := by
      intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact zs _ ha
    have lo' : ∀ q bs, Reach (roots.map observeBV) q bs → Available bs (restrictRows f (observeBV T)) → c.2.1 ≤ q := by
      simpa only [LowerBV, observe6_rename] using lo
    have b := projected_bound f (list_runBV run ws nd rfl) nc reach covered lo'
    have cm := count_constants dom ws
    change k + c.2.2.1 + paid.toNat < c.2.1 + ws.countP (isMaskedConst c.1) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h; rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h; rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · exact availableB_sound dom (fun v hu => hc v (List.mem_cons_of_mem _ hu)) (known _ hm)

-- ============================================================
-- 4. Cut Checking (ess, K3, P4, C5, and lifts) on BitVec 64
-- ============================================================

structure CutSpec where
  z : Nat
  o : Nat
  L : Nat
  kind : Nat
  dropZ : Nat
  perm : List Nat
  dom : Sig

def essentialCheck6 (G : Sig) (roots : List Sig) (a : Sig) : Bool :=
  (List.range 64).any fun r =>
    let r1 : Row := ⟨r % 64, Nat.mod_lt _ (by decide)⟩
    (List.range 64).any fun s =>
      let r2 : Row := ⟨s % 64, Nat.mod_lt _ (by decide)⟩
      (bitBV r1 G != bitBV r2 G) && roots.all (fun w => w == a || bitBV r1 w == bitBV r2 w)

theorem essentialCheck6_sound {G : Sig} {roots : List Sig} {a : Sig}
    (h : essentialCheck6 G roots a = true) : EssentialBV G roots a := by
  simp only [essentialCheck6, List.any_eq_true, Bool.and_eq_true, bne_iff_ne,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨r, _, s, _, hdiff, hiso⟩ := h
  exact ⟨⟨r % 64, _⟩, ⟨s % 64, _⟩, hdiff, fun w hw hne => (hiso w hw).resolve_left hne⟩

def freeWord6 (roots : List Sig) (w : Sig) : Bool :=
  w == zeroBV || w == oneBV || roots.contains w

theorem freeWord6_sound {roots : List Sig} {w : Sig} (h : freeWord6 roots w = true) :
    Available (roots.map observeBV) (observeBV w) := by
  simp only [freeWord6, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h
  rcases h with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false, funext bitBV_zero⟩)
  · exact Or.inr (Or.inl ⟨true, funext bitBV_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

theorem lower6_count {roots : List Sig} {G : Sig} (pG : properBV G)
    (nG : plainWordBV G = true) (nR : roots.all plainWordBV = true)
    (es : List Sig) (nd : es.Nodup) (he : es.all (essentialCheck6 G roots) = true) :
    LowerBV roots G (es.length - 1) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := reachBV_live pG nG nR hr hit
  have le : es.toFinset.card ≤ S.card := by
    apply Finset.card_le_card; intro a ha
    have ha' := List.mem_toFinset.mp ha
    obtain ⟨r, s, hd, iso⟩ := essentialCheck6_sound (List.all_eq_true.mp he a ha')
    exact rawBV_required run roots a sub r s hd iso
  rw [List.toFinset_card_of_nodup nd] at le
  have hsz := liveBV_size run
  omega

def checkCut (vmask : Nat) (T : Sig) (c : CutSpec)
    (baseOf : Nat → List Sig × Sig × Nat) : Bool :=
  let raw := rawOf vmask
  let d := subcube6 c.z c.o
  let f := fixRow c.z c.o
  let G := rename6 f T
  let freeMask := vmask &&& (63 ^^^ (c.z ||| c.o))
  let freeRaw := rawOf freeMask
  let domOk := (List.range 64).all fun r => bitBV (f ⟨r % 64, Nat.mod_lt _ (by decide)⟩) d
  let rawOk := raw.all (fun a => freeWord6 freeRaw (rename6 f a))
  (c.dom == d) && domOk && properB G && rawOk && plainWordBV G && freeRaw.all plainWordBV &&
  (if c.kind == 0 then
     let es := freeRaw.filter (essentialCheck6 G freeRaw)
     decide (c.L ≤ es.length - 1)
   else
     let (bRoots, bT, bL) := baseOf c.kind
     let g : Row → Row := fun r => fixRow c.dropZ 0 (rowPerm c.perm r)
     properB bT &&
     (rename6 g G == bT) &&
     freeRaw.all (fun a => freeWord6 bRoots (rename6 g a)) &&
     decide (c.L ≤ bL))

theorem checkCut_sound {vmask : Nat} {T : Sig} {c : CutSpec}
    {baseOf : Nat → List Sig × Sig × Nat}
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (ok : checkCut vmask T c baseOf = true) :
    Slice (rawOf vmask) T c.dom c.L := by
  unfold checkCut at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hdomEq, domOk⟩, pG⟩, rawOk⟩, nG⟩, nFR⟩, hbody⟩ := ok
  rw [beq_iff_eq.mp hdomEq]
  let f := fixRow c.z c.o
  let G := rename6 f T
  let freeMask := vmask &&& (63 ^^^ (c.z ||| c.o))
  let freeRaw := rawOf freeMask
  have hdom : ∀ r : Row, bitBV (f r) (subcube6 c.z c.o) = true := by
    intro r
    have h := List.all_eq_true.mp domOk r.val (List.mem_range.mpr r.isLt)
    have hmod : (⟨r.val % 64, Nat.mod_lt _ (by decide)⟩ : Row) = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
    simpa [hmod] using h
  have hraw : ∀ a ∈ rawOf vmask, Available (freeRaw.map observeBV) (restrictRows f (observeBV a)) := by
    intro a ha; rw [← observe6_rename]
    exact freeWord6_sound (List.all_eq_true.mp rawOk a ha)
  have hnc : ¬Constant (restrictRows f (observeBV T)) := by
    rw [← observe6_rename]; exact observeBV_proper (proper_of pG)
  refine ⟨f, freeRaw, hdom, hraw, hnc, ?_⟩
  by_cases hk : c.kind = 0
  · simp only [hk, beq_self_eq_true, ite_true, decide_eq_true_eq] at hbody
    let es := freeRaw.filter (essentialCheck6 G freeRaw)
    have hnd : es.Nodup := (rawOf_nodup freeMask).filter _
    have hes : es.all (essentialCheck6 G freeRaw) = true := by
      apply List.all_eq_true.mpr; intro a ha; exact (List.mem_filter.mp ha).2
    have hlo := lower6_count (proper_of pG) nG nFR es hnd hes
    intro p bank hr ha; exact le_trans hbody (hlo p bank hr ha)
  · have hkn : (c.kind == 0) = false := beq_false_of_ne hk
    simp only [hkn, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbody
    obtain ⟨⟨⟨pbT, hEq⟩, hCov⟩, hLe⟩ := hbody
    let b := baseOf c.kind
    let g : Row → Row := fun r => fixRow c.dropZ 0 (rowPerm c.perm r)
    have hlo := lowerBV_slice (proper_of pG) nG nFR (proper_of pbT) g
      ((observe6_rename g G).symm.trans (congrArg observeBV hEq))
      (fun a ha => by rw [← observe6_rename]; exact freeWord6_sound (List.all_eq_true.mp hCov a ha))
      ∅ (fun _ h => absurd h (Finset.notMem_empty _)) (fun _ h => absurd h (Finset.notMem_empty _))
      b.2.2 (hb c.kind hk)
    simp only [Finset.card_empty, Nat.add_zero] at hlo
    intro p bank hr ha; exact le_trans hLe (hlo p bank hr ha)

-- ============================================================
-- 5. BTree, BST, Strict Nat Kernel Checker & Soundness
-- ============================================================

inductive BTree (α : Type) where
  | leaf (a : α)
  | node (l r : BTree α)

def BTree.get {α} : BTree α → Nat → α
  | .leaf a, _ => a
  | .node l r, p => if p &&& 1 == 0 then l.get (p >>> 1) else r.get (p >>> 1)

def BTree.all {α} (f : α → Bool) : BTree α → Bool
  | .leaf a => f a
  | .node l r => l.all f && r.all f

theorem BTree.get_all {α} {f : α → Bool} {t : BTree α} (h : t.all f = true) (p : Nat) :
    f (t.get p) = true := by
  induction t generalizing p with
  | leaf a => exact h
  | node l r ihl ihr =>
    simp only [BTree.all, Bool.and_eq_true] at h
    unfold BTree.get; split
    · exact ihl h.1 _
    · exact ihr h.2 _

inductive BST where
  | e
  | l (k v : Nat)
  | n (k v : Nat) (l r : BST)

abbrev BE := BST.e
abbrev BL := BST.l
abbrev BN := BST.n

def BST.find : BST → Nat → Option (Nat × Nat)
  | .e, _ => none
  | .l k v, x => if Nat.beq x k then some (v >>> 7, v &&& 127) else none
  | .n k v left right, x =>
    if Nat.beq x k then some (v >>> 7, v &&& 127)
    else if Nat.ble x k then left.find x else right.find x

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl

noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x :: xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) :
    forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x :: xs)) = _
    rw [force_eq, ih]; rfl

def zN (op x y : Nat) : Nat :=
  cond (Nat.beq op 0) (Nat.land x y)
    (cond (Nat.beq op 1) (Nat.lor x y)
      (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))

theorem zN_mask (op : Nat) (d a b : Sig) :
    zN op (Nat.land a.toNat d.toNat) (Nat.land b.toNat d.toNat) = Nat.land (binBV op a b).toNat d.toNat := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  rw [tn, tn, tn]; unfold zN
  by_cases h0 : op = 0
  · subst h0; change Nat.land _ _ = _; rw [tn]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, ite_true, BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op = 1
  · subst h1; change Nat.lor _ _ = _; rw [tor]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, Nat.one_ne_zero, ite_true, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0 = false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1 = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op = 2
  · subst h2; change Nat.xor _ (Nat.land _ _) = _; rw [tn, tx]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_true, ite_false,
      BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2 = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0, e1, e2]; change Nat.xor _ (Nat.land _ _) = _; rw [tn, tx]; congr 1; apply bitBV_ext; intro r
  simp only [binBV, bitBV, h0, h1, h2, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl

theorem nat_testBit_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i
theorem nat_testBit_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i
theorem nat_testBit_xor (a b i : Nat) : (Nat.xor a b).testBit i = Bool.xor (a.testBit i) (b.testBit i) :=
  Nat.testBit_xor a b i

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (binBV op a b).toNat := by
  have e (v : Sig) : Nat.land v.toNat (oneBV (N := 64)).toNat = v.toNat := by
    change v.toNat &&& (oneBV (N := 64)).toNat = v.toNat
    rw [← BitVec.toNat_and]; congr 1; exact BitVec.and_allOnes
  have := zN_mask op oneBV a b; rwa [e, e, e] at this

theorem zN_testBit (op x y i : Nat) :
    (zN op x y).testBit i =
      (if op = 0 then x.testBit i && y.testBit i
       else if op = 1 then x.testBit i || y.testBit i
       else if op = 2 then x.testBit i && !(y.testBit i)
       else !(x.testBit i) && y.testBit i) := by
  unfold zN
  by_cases h0 : op = 0
  · subst h0; simp [nat_testBit_land]
  by_cases h1 : op = 1
  · subst h1; simp [nat_testBit_lor]
  have e0 : Nat.beq op 0 = false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1 = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op = 2
  · subst h2; simp only [e0, e1, Bool.cond_false, Bool.cond_true, Nat.beq_refl, nat_testBit_xor, nat_testBit_land,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_false, ite_true]
    cases x.testBit i <;> cases y.testBit i <;> rfl
  have e2 : Nat.beq op 2 = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  simp only [e0, e1, e2, Bool.cond_false, nat_testBit_xor, nat_testBit_land, h0, h1, h2, ite_false]
  cases x.testBit i <;> cases y.testBit i <;> rfl

abbrev CovN := Nat × Nat × Nat

def addCovN (z : Nat) (c : CovN) : CovN :=
  (Nat.lor z c.1,
   Nat.lor (Nat.xor z (Nat.land z c.1)) (Nat.xor c.2.1 (Nat.land c.2.1 z)),
   Nat.lor (Nat.land z c.2.1) (Nat.xor c.2.2 (Nat.land c.2.2 z)))

def covOfCols : List Nat → CovN
  | [] => (0, 0, 0)
  | z :: zs => addCovN z (covOfCols zs)

def takeOneN (c : CovN) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.1 (Nat.land c.2.1 a))
def takeTwoN (c : CovN) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.land c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b))))
def restCovN (c : CovN) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOneN c b)
  else if kb then takeOneN c a else takeTwoN c a b

theorem addCovN_swap (c : CovN) (a b : Nat) : addCovN a (addCovN b c) = addCovN b (addCovN a c) := by
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  all_goals
    simp only [addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl

theorem takeOneN_add (c : CovN) (a : Nat) : takeOneN (addCovN a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOneN, addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl

theorem takeTwoN_add (c : CovN) (a b : Nat) : takeTwoN (addCovN a (addCovN b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwoN, addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl

theorem covOfCols_perm {l r : List Nat} (h : l.Perm r) : covOfCols l = covOfCols r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCovN a) ih
  | swap a b _ => exact addCovN_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

def orList : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.lor x (orList xs)

theorem covOfCols_fst (l : List Nat) : (covOfCols l).1 = orList l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [covOfCols, addCovN, orList, ih]

theorem orList_testBit (l : List Nat) (i : Nat) :
    (orList l).testBit i = true ↔ ∃ x ∈ l, x.testBit i = true := by
  induction l with
  | nil => simp [orList]
  | cons x xs ih => simp [orList, Nat.testBit_lor, ih]

abbrev DWire := Sig × Nat × Nat
def dcol (w : DWire) : Nat := Nat.xor w.2.1 w.2.2
def dbin (op : Nat) (a b : DWire) : DWire := (binBV op a.1 b.1, zN op a.2.1 b.2.1, zN op a.2.2 b.2.2)

def Faithful (pos neg : List Row) (w : DWire) : Prop :=
  (∀ i : Nat, i < pos.length →
    w.2.1.testBit i = bitBV (pos.getD i ⟨0, by decide⟩) w.1 ∧
    w.2.2.testBit i = bitBV (neg.getD i ⟨0, by decide⟩) w.1) ∧
  w.2.1 < 2 ^ pos.length ∧ w.2.2 < 2 ^ pos.length

theorem zN_lt_pow {W op x y : Nat} (hx : x < 2 ^ W) (hy : y < 2 ^ W) : zN op x y < 2 ^ W := by
  have hi : ∀ i ≥ W, (zN op x y).testBit i = false := by
    intro i hi
    have h1 : x.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
    have h2 : y.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
    rw [zN_testBit, h1, h2]; split_ifs <;> rfl
  by_contra! hge
  have hlt : W ≤ Nat.log2 (zN op x y) := by
    have hp : zN op x y ≠ 0 := by
      have : 0 < 2 ^ W := Nat.pow_pos (by decide)
      omega
    exact (Nat.le_log2 hp).mpr hge
  have htb := Nat.testBit_log2 (show zN op x y ≠ 0 by have : 0 < 2 ^ W := Nat.pow_pos (by decide); omega)
  rw [hi _ hlt] at htb; exact Bool.noConfusion htb

theorem faithful_dbin {pos neg : List Row} {a b : DWire} (op : Nat)
    (ha : Faithful pos neg a) (hb : Faithful pos neg b) : Faithful pos neg (dbin op a b) := by
  refine ⟨fun i hi => ?_, zN_lt_pow ha.2.1 hb.2.1, zN_lt_pow ha.2.2 hb.2.2⟩
  obtain ⟨ha1, ha2⟩ := ha.1 i hi
  obtain ⟨hb1, hb2⟩ := hb.1 i hi
  simp only [dbin, zN_testBit, bitBV_bin, ha1, ha2, hb1, hb2, and_self]

theorem faithful_zero (pos neg : List Row) : Faithful pos neg (zeroBV, 0, 0) :=
  ⟨fun i _ => by simp [bitBV_zero], Nat.pow_pos (by decide), Nat.pow_pos (by decide)⟩

def CritOK (T : Sig) (pos neg : List Row) : Prop :=
  ∀ i : Nat, i < pos.length →
    bitBV (pos.getD i ⟨0, by decide⟩) T ≠ bitBV (neg.getD i ⟨0, by decide⟩) T

def allOnesNat (W : Nat) : Nat := (1 <<< W) - 1

theorem dcol_lt {pos neg : List Row} {w : DWire} (h : Faithful pos neg w) : dcol w < 2 ^ pos.length := by
  have hi : ∀ i ≥ pos.length, (dcol w).testBit i = false := by
    intro i hi
    have h1 : w.2.1.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.2.1 (Nat.pow_le_pow_right (by decide) hi))
    have h2 : w.2.2.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.2.2 (Nat.pow_le_pow_right (by decide) hi))
    simp [dcol, Nat.testBit_xor, h1, h2]
  by_contra! hge
  have hp : dcol w ≠ 0 := by have : 0 < 2 ^ pos.length := Nat.pow_pos (by decide); omega
  have htb := Nat.testBit_log2 hp
  rw [hi _ ((Nat.le_log2 hp).mpr hge)] at htb; exact Bool.noConfusion htb

theorem orList_lt {W : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ W) : orList l < 2 ^ W := by
  have hi : ∀ i ≥ W, (orList l).testBit i = false := by
    intro i hi; apply Bool.eq_false_iff.mpr; intro ht
    obtain ⟨x, hx, hxt⟩ := (orList_testBit l i).mp ht
    have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hl x hx) (Nat.pow_le_pow_right (by decide) hi))
    rw [hf] at hxt; exact Bool.noConfusion hxt
  by_contra! hge
  have hp : orList l ≠ 0 := by have : 0 < 2 ^ W := Nat.pow_pos (by decide); omega
  have htb := Nat.testBit_log2 hp
  rw [hi _ ((Nat.le_log2 hp).mpr hge)] at htb; exact Bool.noConfusion htb

theorem live6_cover_eq {T : Sig} {k} {ws : List DWire} {pos neg : List Row}
    (hcrit : CritOK T pos neg) (hf : ∀ w ∈ ws, Faithful pos neg w)
    (h : LiveBV T k (ws.map Prod.fst).toFinset) :
    orList (ws.map dcol) = allOnesNat pos.length := by
  have hlt : orList (ws.map dcol) < 2 ^ pos.length :=
    orList_lt fun x hx => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact dcol_lt (hf w hw)
  apply Nat.eq_of_testBit_eq; intro i
  simp only [allOnesNat, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · simp only [hi, decide_true]
    obtain ⟨v, hv, hdiff⟩ := liveBV_row_diff h (hcrit i hi)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    apply (orList_testBit _ i).mpr
    refine ⟨dcol w, List.mem_map_of_mem hw, ?_⟩
    obtain ⟨h1, h2⟩ := (hf w hw).1 i hi
    simp only [dcol, Nat.testBit_xor, h1, h2]
    cases hx : bitBV (pos.getD i ⟨0, by decide⟩) w.1 <;>
      cases hy : bitBV (neg.getD i ⟨0, by decide⟩) w.1 <;> simp_all
  · simp only [hi, decide_false]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))

def delOne {α} [BEq α] (ws : List α) (a : α) (keep : Bool) : List α :=
  if keep then ws else ws.erase a
def delTwo {α} [BEq α] (ws : List α) (a b : α) (ka kb : Bool) : List α :=
  delOne (delOne ws a ka) b kb

theorem delOne_sub {α} [BEq α] [LawfulBEq α] (ws : List α) (a : α) (k : Bool) :
    (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem delTwo_sub {α} [BEq α] [LawfulBEq α] (ws : List α) (a b : α) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)

theorem delTwo_len {α} [BEq α] [LawfulBEq α] (ws : List α) (a b : α) (ka kb : Bool)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;>
    simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]

theorem delTwo_cov {ws : List DWire} {a b : DWire} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    orList ((delTwo ws a b ka kb).map dcol) = restCovN (covOfCols (ws.map dcol)) (dcol a) (dcol b) ka kb := by
  rw [← covOfCols_fst]
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb
  · have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hm))
    change (covOfCols (((ws.erase a).erase b).map dcol)).1 = takeTwoN _ _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeTwoN_add _ _ _).symm
  · have hp : ws.Perm (a :: ws.erase a) := List.perm_cons_erase ha
    change (covOfCols ((ws.erase a).map dcol)).1 = takeOneN _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeOneN_add _ _).symm
  · have hp : ws.Perm (b :: ws.erase b) := List.perm_cons_erase hb
    change (covOfCols ((ws.erase b).map dcol)).1 = takeOneN _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeOneN_add _ _).symm
  · rfl

abbrev NodeData := Nat × Nat × List Nat
def lf (p0 : Nat) (hs : List Nat) : BTree NodeData := .leaf (p0, 0, hs)
def lf2 (p0 p1 : Nat) (hs : List Nat) : BTree NodeData := .leaf (p0, p1, hs)
abbrev nd := @BTree.node NodeData
def mkRows (l : List Nat) : List Row := l.map fun x => ⟨x % 64, Nat.mod_lt _ (by decide)⟩

def unpackH1 (h : Nat) : List (Nat × Nat) :=
  if Nat.beq h 0 then [] else
  let a := ((h &&& 255) - 1, (h >>> 8) &&& 255)
  let h1 := h >>> 16
  if Nat.beq h1 0 then [a] else
  let b := ((h1 &&& 255) - 1, (h1 >>> 8) &&& 255)
  let h2 := h1 >>> 16
  if Nat.beq h2 0 then [a, b] else
  [a, b, ((h2 &&& 255) - 1, (h2 >>> 8) &&& 255)]

def unpackHints (hs : List Nat) : List (Nat × Nat) := hs.flatMap unpackH1

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w :: ws => if bits &&& 1 == 1 then w :: selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws

theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons _ _ ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons _ _ ih =>
    rw [List.map_cons, selectLive, selectLive]
    split
    · rw [List.map_cons, ih]
    · exact ih _

def decodeDBank : Nat → Nat → List DWire → List DWire
  | 0, _, ws => ws
  | n + 1, ops, ws =>
    let a := ws.getD (ops &&& 15) (zeroBV, 0, 0)
    let b := ws.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)
    decodeDBank n (ops >>> 10) (ws ++ [dbin ((ops >>> 8) &&& 3) a b])

theorem decodeDBank_faithful {pos neg : List Row} (n ops : Nat) (ws : List DWire)
    (hb : ∀ w ∈ ws, Faithful pos neg w) :
    ∀ w ∈ decodeDBank n ops ws, Faithful pos neg w := by
  have getF {l : List DWire} (hl : ∀ w ∈ l, Faithful pos neg w) (i : Nat) :
      Faithful pos neg (l.getD i (zeroBV, 0, 0)) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => exact faithful_zero pos neg
    | some v => exact hl v (List.mem_of_getElem? h)
  induction n generalizing ops ws with
  | zero => exact hb
  | succ n ih =>
    apply ih; intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hb w h
    · obtain rfl := List.mem_singleton.mp h
      exact faithful_dbin _ (getF hb _) (getF hb _)

noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0, _, ws => ws
  | n + 1, ops, ws =>
    force (zN ((ops >>> 8) &&& 3) (ws.getD (ops &&& 15) 0) (ws.getD ((ops >>> 4) &&& 15) 0)) fun z =>
      decodeN n (ops >>> 10) (ws ++ [z])

theorem decodeN_eq (F : Sig → Nat) (F0 : F zeroBV = 0) (Fb : ∀ op a b, F (binBV op a b) = zN op (F a) (F b))
    (n ops : Nat) (ds : List DWire) :
    (decodeDBank n ops ds).map (fun w => F w.1) = decodeN n ops (ds.map fun w => F w.1) := by
  have gd (l : List DWire) (i : Nat) :
      (l.map fun w => F w.1).getD i 0 = F (l.getD i (zeroBV, 0, 0)).1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[i]? with
    | none => exact F0.symm
    | some _ => rfl
  induction n generalizing ops ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN, force_eq, decodeDBank, ih, gd, gd, ← Fb, List.map_append]; rfl

def chosenSteps (bank : List DWire) : Nat → Nat → Nat → List Choice
  | _, _, 0 => []
  | ops, paid, n + 1 =>
    if Nat.beq paid 0 then [] else
    let rest := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then rest else
      ((ops >>> 8) &&& 3, (bank.getD (ops &&& 15) (zeroBV, 0, 0)).1,
        (bank.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)).1) :: rest

def kwN (v : Nat) : Nat :=
  let n := v % 134217689
  (n * (n + 971)) % 134217689

noncomputable def anyEq (m : Nat) (l : List Nat) : Bool :=
  List.rec false (fun v _ ih => or (Nat.beq m v) ih) l

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l = true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l) = true ↔ _
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]

def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (anyEq (Nat.xor d m) pm)
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)

theorem masked_comp (d x : Sig) : masked d (negBV x) = d ^^^ masked d x := by
  apply bitBV_ext; intro r
  simp only [masked, negBV, bitBV, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    r.isLt, decide_true, Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl

theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]; exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConst d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zeroBV) := by
    have z0 : (zeroBV (N := 64)).toNat = 0 := by simp [zeroBV]
    rw [← beq_toNat, z0]
  rw [nconst, e, beq_toNat]; rfl
theorem anyEq_masked (x d : Sig) (pool : List Sig) :
    anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v == x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih, nmask_eq, beq_toNat, List.map_cons, List.any_cons, Bool.beq_comm]
theorem navail_eq (d a : Sig) (pool : List Sig) :
    navail d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (negBV a)).toNat := by
    rw [masked_comp]; exact (BitVec.toNat_xor _ _).symm
  rw [navail, nconst_eq, nmask_eq, x, anyEq_masked, anyEq_masked]
  simp only [availableB, isMaskedConst]

abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat

noncomputable def quickSpec (k : Nat) (ws : List DWire) (p : BoundPool) : QS :=
  let d := p.1.toNat
  let pm := p.2.2.2.map (nmask d)
  let ms := ws.map (fun w : DWire => nmask d w.1)
  (d, ms.countP (nconst d), p.2.1, Nat.add k p.2.2.1,
    (ms.map fun m => cond (navail d pm m) 0 1).sum, ms, pm)

noncomputable def forcePool {β : Type} (k : Nat) (ws : List DWire) (p : BoundPool) (f : QS → β) : β :=
  force p.1.toNat fun d => forceMap (nmask d) p.2.2.2 fun pm =>
  forceMap (fun w : DWire => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.2.1 fun l => force (Nat.add k p.2.2.1) fun t =>
  force (ms.map fun m => cond (navail d pm m) 0 1).sum fun v => f (d, c, l, t, v, ms, pm)

theorem forcePool_eq {β : Type} (k ws p) (f : QS → β) : forcePool k ws p f = f (quickSpec k ws p) := by
  simp only [forcePool, force_eq, forceMap_eq]; rfl

noncomputable def forcePools {β : Type} (k : Nat) (ws : List DWire) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool k ws p fun q => ih fun qs => f (q :: qs)) ps

theorem forcePools_eq {β : Type} (k ws ps) (f : List QS → β) :
    forcePools k ws ps f = f (ps.map (quickSpec k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool k ws p (fun q => forcePools k ws ps fun qs => f (q :: qs)) = _
    rw [forcePool_eq, ih]; rfl

noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.1 s.2.2.2.2.2.2
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))

theorem delTwo_sum {α} [BEq α] [LawfulBEq α] (f : α → Nat) {ws : List α} {a b : α}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List α} {x : α} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons, List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha; have e2 := er hb; have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo, delOne, Bool.false_eq_true, ite_true, ite_false, cond_true, cond_false] <;> omega

theorem keptCount {α} [BEq α] [LawfulBEq α] (p : α → Bool) (ws : List α) (a b : α) (ka kb : Bool) :
    ws.countP p - (if ka then 0 else (p a).toNat) - (if kb then 0 else (p b).toNat) ≤
    (delTwo ws a b ka kb).countP p := by
  have lb (l : List α) (x : α) (k : Bool) : l.countP p ≤ (delOne l x k).countP p + (if k then 0 else (p x).toNat) := by
    cases k
    · simp only [delOne, Bool.false_eq_true, ite_false, List.countP_erase]
      split
      next h => simp [h.2]; omega
      next => omega
    · simp [delOne]
  have h1 := lb ws a ka; have h2 := lb (delOne ws a ka) b kb
  simp only [delTwo]; omega

theorem fastCost_sound {raw T} {p : BoundPool} (vp : ValidPool raw T p)
    {k : Nat} {ws : List DWire} {i j op : Nat} {ka kb : Bool}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) (hop : op < 4)
    (nd : (ws.map Prod.fst).Nodup)
    (hfresh : binBV op (ws[i]).1 (ws[j]).1 ∉ ws.map Prod.fst)
    (hfc : fastCost (quickSpec k ws p) i j op ka kb = true) :
    ImpossibleBV T k (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
  have ha : ws[i] ∈ ws := List.getElem_mem hi
  have hb : ws[j] ∈ ws := List.getElem_mem hj
  have hne1 : (ws[i]).1 ≠ (ws[j]).1 := fun e => hij ((List.Nodup.getElem_inj_iff nd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
  have hne : ws[i] ≠ ws[j] := fun e => hne1 (congrArg Prod.fst e)
  let a := ws[i]; let b := ws[j]; let rest := delTwo ws a b ka kb
  have hsub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : (binBV op a.1 b.1 :: rest.map Prod.fst).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hfresh ((hsub.map _).subset hm), nd.sublist (hsub.map _)⟩
  have gget (t : Nat) (ht : t < ws.length) :
      (ws.map (fun w : DWire => nmask p.1.toNat w.1)).getD t 0 = nmask p.1.toNat (ws[t]).1 := by
    simp [List.getD_eq_getElem?_getD, ht]
  have su : ((ws.map (fun w : DWire => nmask p.1.toNat w.1)).map
      fun m => cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) m) 0 1).sum =
      (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum := by
    rw [List.map_map]; refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
    change cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat w.1)) 0 1 = _
    rw [navail_eq]
  have nloss_e (w : DWire) (kp : Bool) :
      nloss p.1.toNat (nmask p.1.toNat w.1) kp = if kp then 0 else (isMaskedConst p.1 w.1).toNat := by
    rw [nloss, nconst_eq]
    cases kp
    · cases isMaskedConst p.1 w.1 <;> rfl
    · rfl
  simp only [fastCost, quickSpec, force_eq, gget i hi, gget j hj, su, List.countP_map, Function.comp_def,
    nconst_eq, nloss_e] at hfc
  change and (Nat.beq (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum
    (Nat.add (cond ka 0 (cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat a.1)) 0 1))
      (cond kb 0 (cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat b.1)) 0 1)))) _ = true at hfc
  have zeq : zN op (nmask p.1.toNat a.1) (nmask p.1.toNat b.1) = nmask p.1.toNat (binBV op a.1 b.1) := zN_mask op p.1 a.1 b.1
  rw [zeq, nconst_eq, navail_eq, navail_eq, navail_eq] at hfc
  simp only [Nat.add_eq, Nat.sub_eq, Nat.succ_eq_add_one, Bool.and_eq_true, Nat.beq_eq] at hfc
  obtain ⟨hu, hcond⟩ := hfc
  have hsum := delTwo_sum (fun w : DWire => cond (availableB p.1 p.2.2.2 w.1) 0 1) ha hb hne ka kb
  change (rest.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum =
      (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum -
      cond ka 0 (cond (availableB p.1 p.2.2.2 a.1) 0 1) -
      cond kb 0 (cond (availableB p.1 p.2.2.2 b.1) 0 1) at hsum
  rw [hu] at hsum
  have hzero : (rest.map fun w : DWire => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum = 0 := by omega
  have hknown : ∀ v ∈ rest.map Prod.fst, availableB p.1 p.2.2.2 v = true := by
    intro _ hm; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
    have hv := List.sum_eq_zero_iff.mp hzero _ (List.mem_map_of_mem hw)
    cases e : availableB p.1 p.2.2.2 w.1
    · simp [e] at hv
    · rfl
  have hkc := keptCount (fun w : DWire => isMaskedConst p.1 w.1) ws a b ka kb
  have hcm : (binBV op a.1 b.1 :: rest.map Prod.fst).countP (isMaskedConst p.1) =
      rest.countP (fun w : DWire => isMaskedConst p.1 w.1) + (isMaskedConst p.1 (binBV op a.1 b.1)).toNat := by
    simp only [List.countP_cons, List.countP_map, Function.comp_def]
    cases isMaskedConst p.1 (binBV op a.1 b.1) <;> simp
  have ca : isMaskedConst p.1 (binBV op a.1 b.1) = true → availableB p.1 p.2.2.2 (binBV op a.1 b.1) = true := by
    intro h; simp only [availableB, isMaskedConst, Bool.or_eq_true] at h ⊢; exact Or.inl (Or.inl h)
  let ch : Choice := (op, a.1, b.1)
  have hcv : choiceVal ch = binBV op a.1 b.1 := rfl
  generalize hC : (ws.countP (fun w => isMaskedConst p.1 w.1) - (if ka then 0 else (isMaskedConst p.1 a.1).toNat) -
      (if kb then 0 else (isMaskedConst p.1 b.1).toNat)) = C at hcond hkc
  change C ≤ rest.countP (fun w => isMaskedConst p.1 w.1) at hkc
  cases h1 : Nat.ble (k + p.2.2.1 + 1) (p.2.1 + C)
  · rw [h1] at hcond
    cases h2 : Nat.ble (k + p.2.2.1) (p.2.1 + C)
    · rw [h2] at hcond; simp at hcond
    · rw [h2] at hcond
      have hl2 := Nat.ble_eq.mp h2
      simp only [Bool.cond_true, Bool.cond_false] at hcond
      have haz := ca hcond
      exact valid_exclude vp k (rest.map Prod.fst) ch false hknown haz (by rw [hcv, hcm, hcond]; simp; omega) ndc
  · rw [h1] at hcond
    have hl1 := Nat.ble_eq.mp h1
    simp only [Bool.cond_true, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at hcond
    rcases hcond with haz | ⟨hl2, haa, hbb⟩
    · exact valid_exclude vp k (rest.map Prod.fst) ch false hknown haz (by rw [hcv, hcm]; simp; omega) ndc
    · have hcok : choiceOK p.1 p.2.2.2 ch = true := by simp [choiceOK, ch, hop, haa, hbb]
      exact valid_exclude vp k (rest.map Prod.fst) ch true hknown hcok (by rw [hcv, hcm]; simp; omega) ndc

-- Forest & fastNodeOK
structure Forest where
  vmask : Nat
  target : Sig
  cap : Nat
  pos : List Row
  neg : List Row
  rawCols : List (Nat × Nat)
  autos : List (List Nat)
  cuts : List CutSpec
  levels : Nat → Option (BTree NodeData)
  maps : Nat → BST

def Forest.rawD (g : Forest) : List DWire :=
  (rawOf g.vmask).zipWith (fun s c => (s, c.1, c.2)) g.rawCols

def Forest.nodeWires (g : Forest) (nd : NodeData) : List DWire :=
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  selectLive liveMask (decodeDBank depth ops g.rawD)

def Forest.nodeVals (g : Forest) (nd : NodeData) : List Sig :=
  (g.nodeWires nd).map Prod.fst

def rawPermN (vmask : Nat) (perm : List Nat) : List Nat :=
  ([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
    if vmask.testBit i then some (allVars6.getD (perm.getD i 0) 0).toNat else none

noncomputable def fastPermState (g : Forest) (k : Nat) (tag : Nat) : Option (List Nat) :=
  ((g.maps k).find tag).bind fun (path, ai) =>
  (g.levels (k - 1)).bind fun tree =>
  (g.autos[ai]?).map fun perm =>
    let x := tree.get path
    selectLive ((x.1 >>> 4) &&& 65535) (decodeN (x.1 &&& 15) ((x.1 >>> 20) + (x.2.1 <<< 40)) (rawPermN g.vmask perm))

def rowPermSurjB (p : List Nat) : Bool :=
  (List.range 64).all fun y =>
    (List.range 64).any fun x =>
      (rowPerm p ⟨x % 64, Nat.mod_lt _ (by decide)⟩).val == y

theorem rowPermSurjB_sound {p : List Nat} (h : rowPermSurjB p = true) :
    Function.Surjective (rowPerm p) := by
  intro y
  have hy := List.all_eq_true.mp h y.val (List.mem_range.mpr y.isLt)
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hy
  exact ⟨⟨x % 64, Nat.mod_lt _ (by decide)⟩, Fin.ext (beq_iff_eq.mp hx)⟩

def autoCheck (T : Sig) (p : List Nat) : Bool :=
  rowPermSurjB p && (sigPerm p T == T) &&
  ([0, 1, 2, 3, 4, 5] : List Nat).all (fun i => sigPerm p (allVars6.getD i 0) == allVars6.getD (p.getD i 0) 0)

theorem autoCheck_rotate {T : Sig} {p : List Nat} (hok : autoCheck T p = true)
    {k : Nat} {ws : List Sig} (himp : ImpossibleBV T k ws.toFinset) :
    ImpossibleBV T k (ws.map (sigPerm p)).toFinset := by
  simp only [autoCheck, Bool.and_eq_true, beq_iff_eq] at hok
  have hsurj := rowPermSurjB_sound hok.1.1
  have hbij : Function.Bijective (rowPerm p) := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  obtain ⟨invF, hinvL, hinvR⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hinvSurj : Function.Surjective invF := fun r => ⟨rowPerm p r, hinvL r⟩
  have hinvSig (a : Sig) : rename6 invF (sigPerm p a) = a := by
    apply bitBV_ext; intro r; rw [bit6_rename, sigPerm, bit6_rename, hinvR]
  have hTinv : rename6 invF T = T := by conv => lhs; rw [← hok.1.2]; exact hinvSig T
  intro t ht hlive
  have hrun := live6_rename hlive invF hinvSurj
  rw [hTinv] at hrun
  have hback : (ws.map (sigPerm p)).toFinset.image (rename6 invF) = ws.toFinset := by
    ext a; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; simpa only [hinvSig] using hw
    · intro ha; exact ⟨_, ⟨a, ha, rfl⟩, hinvSig a⟩
  rw [hback] at hrun
  exact himp t ht hrun

theorem zipWith_fst_map {α β γ : Type} (f : α → β → γ) (g : γ → α) (h : ∀ a b, g (f a b) = a)
    (xs : List α) (ys : List β) (hlen : xs.length = ys.length) :
    (xs.zipWith f ys).map g = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys => simp [h, ih ys (by simpa using hlen)]

theorem filterMap_map_eq {α β γ : Type} (l : List α) (p : α → Bool) (f : α → β) (g : β → γ) :
    (l.filterMap fun x => if p x then some (f x) else none).map g =
    l.filterMap fun x => if p x then some (g (f x)) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases p a <;> simp [ih]

theorem fastPermState_sound (g : Forest) (k tag : Nat) {ys : List Nat}
    (hlen : (rawOf g.vmask).length = g.rawCols.length)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : ∀ tree, g.levels (k - 1) = some tree → ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (h : fastPermState g k tag = some ys) :
    ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV g.target (k - 1) xs.toFinset := by
  unfold fastPermState at h
  cases hf : (g.maps k).find tag with
  | none => simp [hf] at h
  | some pr =>
    obtain ⟨path, ai⟩ := pr
    simp only [hf, Option.bind_some] at h
    cases hl : g.levels (k - 1) with
    | none => simp [hl] at h
    | some tree =>
      simp only [hl, Option.bind_some] at h
      cases ha : g.autos[ai]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha, Option.map_some, Option.some.injEq] at h
        have hok := hauto perm (List.mem_of_getElem? ha)
        have hok' := hok
        simp only [autoCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok'
        rcases hnd : tree.get path with ⟨p0, p1, hpacked⟩
        rw [hnd] at h
        refine ⟨(g.nodeVals (p0, p1, hpacked)).map (sigPerm perm), ?_, ?_⟩
        · let F (a : Sig) : Nat := (sigPerm perm a).toNat
          have F0 : F zeroBV = 0 := by
            change (rename6 (rowPerm perm) zeroBV).toNat = 0
            rw [(rename6_const _).1]; simp [zeroBV]
          have Fb (op a b) : F (binBV op a b) = zN op (F a) (F b) := by
            change (sigPerm perm (binBV op a b)).toNat = zN op (sigPerm perm a).toNat (sigPerm perm b).toNat
            rw [zN_full, sigPerm, rename6_bin]; rfl
          have hrawF : g.rawD.map (fun w => F w.1) = rawPermN g.vmask perm := by
            have h1 : g.rawD.map Prod.fst = rawOf g.vmask :=
              zipWith_fst_map _ Prod.fst (fun _ _ => rfl) _ _ hlen
            rw [show g.rawD.map (fun w => F w.1) = (g.rawD.map Prod.fst).map F by rw [List.map_map]; rfl, h1]
            unfold rawOf rawPermN
            rw [filterMap_map_eq]
            apply List.filterMap_congr; intro i hi
            split; · congr 1; exact congrArg BitVec.toNat (hok'.2 i hi)
            · rfl
          rw [← h]; unfold Forest.nodeVals Forest.nodeWires
          rw [List.map_map, List.map_map, selectLive_map]
          change selectLive ((p0 >>> 4) &&& 65535) (decodeN (p0 &&& 15) ((p0 >>> 20) + (p1 <<< 40)) (rawPermN g.vmask perm)) =
            selectLive ((p0 >>> 4) &&& 65535) ((decodeDBank (p0 &&& 15) ((p0 >>> 20) + (p1 <<< 40)) g.rawD).map fun w => F w.1)
          rw [decodeN_eq F F0 Fb, hrawF]
        · exact autoCheck_rotate hok (hnd ▸ hprev tree hl path)

def buildRule (g : Forest) (ops depth : Nat) (bank : List DWire) (ci paid : Nat) : Option BoundPool :=
  (g.cuts[ci]?).bind fun c =>
    let cs := chosenSteps bank ops paid depth
    (makePool c.dom (rawOf g.vmask) cs).map fun pool => (c.dom, c.L, cs.length, pool)

theorem buildRule_sound (g : Forest)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L)
    {ops depth bank ci paid p} (h : buildRule g ops depth bank ci paid = some p) :
    ValidPool (rawOf g.vmask) g.target p := by
  unfold buildRule at h
  cases hc : g.cuts[ci]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.bind_some] at h
    cases hm : makePool c.dom (rawOf g.vmask) (chosenSteps bank ops paid depth) with
    | none => simp [hm] at h
    | some pool =>
      simp only [hm, Option.map_some, Option.some.injEq] at h
      subst p
      exact build_valid (hcuts c (List.mem_of_getElem? hc)) _ hm

-- Fast Nat-based link check (zero allocation of child list!)
noncomputable def linkAt (fl : Nat → Option (List Nat)) (wsN : List Nat) (totH : Nat)
    (x y zVal : Nat) (ka kb : Bool) : Bool :=
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq zVal ys)
      (and (wsN.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
        (ys.all fun v => or (Nat.beq v zVal) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v wsN)))))
    (fl (Nat.add (kwN zVal) (Nat.sub (Nat.sub totH (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))

theorem unique_fst {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haT <;> rcases List.mem_cons.mp hb with rfl | hbT
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbT))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haT))
    · exact ih ht haT hbT

theorem mem_delOne {α} [BEq α] [LawfulBEq α] {v : List α} (nd : v.Nodup) (a w : α) (k : Bool) :
    w ∈ delOne v a k ↔ w ∈ v ∧ (w ≠ a ∨ k = true) := by
  cases k <;> simp [delOne, nd.mem_erase_iff, and_comm]

theorem kept_value {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo, List.mem_map, mem_delOne wn, mem_delOne dn]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨_, hw.1.1, rfl⟩, hw.1.2.imp (fun ne eq => ne (unique_fst nd hw.1.1 ha eq)) id,
      hw.2.imp (fun ne eq => ne (unique_fst nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w, hm, rfl⟩, h1, h2⟩
    exact ⟨w, ⟨⟨hm, h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
      h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩, rfl⟩

theorem linkAt_sound {T : Sig} {k : Nat} {fl : Nat → Option (List Nat)}
    {ws : List DWire} {i j op : Nat} {ka kb : Bool}
    (nd : (ws.map Prod.fst).Nodup) (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV T k xs.toFinset)
    (h : linkAt fl (ws.map fun w => w.1.toNat) ((ws.map fun w => kwN w.1.toNat).sum)
          (ws[i]).1.toNat (ws[j]).1.toNat (binBV op (ws[i]).1 (ws[j]).1).toNat ka kb = true) :
    ImpossibleBV T k (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
  let a := ws[i]; let b := ws[j]; let z := binBV op a.1 b.1
  have ha : a ∈ ws := List.getElem_mem hi
  have hb : b ∈ ws := List.getElem_mem hj
  have hne1 : a.1 ≠ b.1 := fun e => hij ((List.Nodup.getElem_inj_iff nd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
  have hne : a ≠ b := fun e => hne1 (congrArg Prod.fst e)
  unfold linkAt at h
  generalize Nat.add (kwN z.toNat) _ = tag at h
  cases hf : fl tag with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs, rfl, himp⟩ := hfl tag ys hf
    rw [hf] at h
    simp only [forceMap_eq, List.map_id', Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      anyEq_iff, Nat.beq_eq, Bool.not_eq_true'] at h
    obtain ⟨h1, h2, h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w, hw, e⟩ := List.mem_map.mp hv; exact BitVec.toNat_inj.mp e ▸ hw
    have hset : (z :: (delTwo ws a b ka kb).map Prod.fst).toFinset = xs.toFinset := by
      ext v; simp only [List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hv)
        · exact back h1
        · obtain ⟨hw, va, vb⟩ := (kept_value nd ha hb ka kb v).mp hv
          obtain ⟨w, hm, rfl⟩ := List.mem_map.mp hw
          rcases h2 _ (List.mem_map_of_mem hm) with ⟨hka, e⟩ | ⟨hkb, e⟩ | hm2
          · rcases va with va | va
            · exact absurd (BitVec.toNat_inj.mp e) va
            · simp [va] at hka
          · rcases vb with vb | vb
            · exact absurd (BitVec.toNat_inj.mp e) vb
            · simp [vb] at hkb
          · exact back hm2
      · intro hv
        rcases h3 _ (List.mem_map_of_mem hv) with e | ⟨⟨hva, hvb⟩, hm⟩
        · exact Or.inl (BitVec.toNat_inj.mp e)
        · refine Or.inr ((kept_value nd ha hb ka kb v).mpr ⟨?_, ?_, ?_⟩)
          · obtain ⟨w, hw, e⟩ := List.mem_map.mp hm
            exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
          · rcases hva with rfl | hne'
            · exact Or.inr rfl
            · exact Or.inl fun e => by subst e; rw [Nat.beq_refl] at hne'; exact Bool.noConfusion hne'
          · rcases hvb with rfl | hne'
            · exact Or.inr rfl
            · exact Or.inl fun e => by subst e; rw [Nat.beq_refl] at hne'; exact Bool.noConfusion hne'
    rwa [hset]

-- The unified fast kernel node checker!
noncomputable def checkMove (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsC : List Nat)
    (i j op xi yi ci cj cz : Nat) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if Nat.ble (Nat.succ k) len then true else
  force (restCovN cov ci cj ka kb) fun rs =>
  if !(Nat.beq (Nat.lor rs cz) allW) then true else
  force (zN op xi yi) fun zVal =>
  if or (Nat.beq zVal 0) (or (Nat.beq zVal 18446744073709551615) (anyEq zVal wsN)) then true else
  or (qs.any fun s => fastCost s i j op ka kb)
     (linkAt fl wsN totH xi yi zVal ka kb)

noncomputable def checkPairOp (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i j op : Nat) : Bool :=
  force (wsP.getD i 0) fun pi => force (wsP.getD j 0) fun pj =>
  force (wsQ.getD i 0) fun qi => force (wsQ.getD j 0) fun qj =>
  force (Nat.xor (zN op pi pj) (zN op qi qj)) fun cz =>
  let xi := wsN.getD i 0; let yi := wsN.getD j 0
  let ci := wsC.getD i 0; let cj := wsC.getD j 0
  let f := checkMove fl qs k n allW totH cov wsN wsC i j op xi yi ci cj cz
  and (and (f false false) (f true false)) (and (f false true) (f true true))

noncomputable def checkPair (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i j : Nat) : Bool :=
  let f := checkPairOp fl qs k n allW totH cov wsN wsP wsQ wsC i j
  and (and (f 0) (f 1)) (and (f 2) (f 3))

noncomputable def checkPairsFrom (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i : Nat) : List Nat → Bool
  | [] => true
  | j :: js => and (checkPair fl qs k n allW totH cov wsN wsP wsQ wsC i j)
                   (checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC i js)

noncomputable def checkAllPairs (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) : List Nat → Bool
  | [] => true
  | i :: js => and (checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC i js)
                   (checkAllPairs fl qs k n allW totH cov wsN wsP wsQ wsC js)

noncomputable def fastNodeOK (g : Forest) (k : Nat) (nd : NodeData) : Bool :=
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  let vals := ws.map Prod.fst
  and (decide vals.Nodup) (and (!(vals.contains g.target))
    (if Nat.beq k 0 then true else
      let hints := unpackHints nd.2.2
      let pools := hints.filterMap fun h => buildRule g ops depth bank h.1 h.2
      forceMap (fun w : DWire => w.1.toNat) ws fun wsN =>
      forceMap (fun w : DWire => w.2.1) ws fun wsP =>
      forceMap (fun w : DWire => w.2.2) ws fun wsQ =>
      forceMap dcol ws fun wsC =>
      force (wsN.map kwN).sum fun totH =>
      let cov := covOfCols wsC
      let allW := allOnesNat g.pos.length
      forcePools (k - 1) ws pools fun qs =>
      checkAllPairs (fastPermState g k) qs k ws.length allW totH cov wsN wsP wsQ wsC (List.range ws.length)))

-- Enum step & fastNodeOK soundness!
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  binBV d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, d < 4 → ∀ ka kb, a ≠ b → binBV d a b ∉ ws →
      properBV (binBV d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleBV T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleBV T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using LiveBV.ind with
  | stop _ => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : binBV d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := liveBV_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U); let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (binBV d a b) U := by
      change (binBV d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := liveBV_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by cases k <;> simp [kept]

theorem binary_front {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    (binBV d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv' := List.mem_map_of_mem (f := Prod.fst) hb
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    kept_value nd ha hb, keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, binBV_flip hd a b]
  tauto

theorem checkAllPairs_at {fl qs k n allW totH cov wsN wsP wsQ wsC}
    {js : List Nat} (h : checkAllPairs fl qs k n allW totH cov wsN wsP wsQ wsC js = true)
    {i j : Nat} (hi : i ∈ js) (hj : j ∈ js) (hij : i ≠ j) :
    checkPair fl qs k n allW totH cov wsN wsP wsQ wsC i j = true ∨
    checkPair fl qs k n allW totH cov wsN wsP wsQ wsC j i = true := by
  have from_at {a : Nat} {l : List Nat} (hl : checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC a l = true)
      {b : Nat} (hb : b ∈ l) : checkPair fl qs k n allW totH cov wsN wsP wsQ wsC a b = true := by
    induction l with
    | nil => simp at hb
    | cons x l ih =>
      simp only [checkPairsFrom, Bool.and_eq_true] at hl
      rcases List.mem_cons.mp hb with rfl | hbT
      · exact hl.1
      · exact ih hl.2 hbT
  induction js with
  | nil => simp at hi
  | cons a js ih =>
    simp only [checkAllPairs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hi with rfl | hiT
    · exact Or.inl (from_at h.1 ((List.mem_cons.mp hj).resolve_left (Ne.symm hij)))
    · rcases List.mem_cons.mp hj with rfl | hjT
      · exact Or.inr (from_at h.1 hiT)
      · exact ih h.2 hiT hjT

theorem fastNodeOK_sound (g : Forest) (k : Nat) (nd : NodeData)
    (hlen : (rawOf g.vmask).length = g.rawCols.length)
    (hcrit : CritOK g.target g.pos g.neg)
    (hrawF : ∀ w ∈ g.rawD, Faithful g.pos g.neg w)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : k > 0 → ∀ tree, g.levels (k - 1) = some tree →
      ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (hok : fastNodeOK g k nd = true) :
    ImpossibleBV g.target k (g.nodeVals nd).toFinset := by
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  let hints := unpackHints nd.2.2
  unfold fastNodeOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hok
  obtain ⟨hnd, hout, hbody⟩ := hok
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  change ImpossibleBV g.target k (ws.map Prod.fst).toFinset
  by_cases hk0 : k = 0
  · subst hk0; intro t ht hlive
    have : t = 0 := by omega
    subst this; obtain ⟨hS, _⟩ := hlive
    exact hout (List.mem_toFinset.mp (by rw [hS]; exact Finset.mem_singleton_self _))
  have hkpos : k > 0 := by omega
  have hk0b : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun h => hk0 (Nat.eq_of_beq_eq_true h)
  simp only [hk0b, Bool.false_eq_true, ite_false, forceMap_eq, force_eq, forcePools_eq] at hbody
  let pools := hints.filterMap fun h => buildRule g ops depth bank h.1 h.2
  have hpv : ∀ p ∈ pools, ValidPool (rawOf g.vmask) g.target p := by
    intro p hp; obtain ⟨h', _, heq⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g hcuts heq
  have hfl : ∀ tag ys, fastPermState g k tag = some ys →
      ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV g.target (k - 1) xs.toFinset :=
    fun tag ys hs => fastPermState_sound g k tag hlen hauto (hprev hkpos) hs
  have hwsF : ∀ w ∈ ws, Faithful g.pos g.neg w := fun w hw =>
    decodeDBank_faithful depth ops g.rawD hrawF w ((selectLive_sub liveMask bank).subset hw)
  -- Helper: check one ordered pair (i, j)
  have onePair (i j op : Nat) (ka kb : Bool)
      (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) (hop : op < 4)
      (hfr : binBV op (ws[i]).1 (ws[j]).1 ∉ ws.map Prod.fst)
      (hpr : properBV (binBV op (ws[i]).1 (ws[j]).1))
      (hcp : checkPair (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map fun w => w.2.1)
        (ws.map fun w => w.2.2) (ws.map dcol) i j = true) :
      ImpossibleBV g.target (k - 1) (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
    simp only [checkPair, Bool.and_eq_true] at hcp
    have hcop : checkPairOp (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map fun w => w.2.1)
        (ws.map fun w => w.2.2) (ws.map dcol) i j op = true := by
      rcases op_four hop with rfl | rfl | rfl | rfl
      · exact hcp.1.1
      · exact hcp.1.2
      · exact hcp.2.1
      · exact hcp.2.2
    simp only [checkPairOp, force_eq, Bool.and_eq_true] at hcop
    have hcm : checkMove (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map dcol) i j op
        ((ws.map fun w => w.1.toNat).getD i 0) ((ws.map fun w => w.1.toNat).getD j 0)
        ((ws.map dcol).getD i 0) ((ws.map dcol).getD j 0)
        (Nat.xor (zN op ((ws.map fun w => w.2.1).getD i 0) ((ws.map fun w => w.2.1).getD j 0))
                 (zN op ((ws.map fun w => w.2.2).getD i 0) ((ws.map fun w => w.2.2).getD j 0))) ka kb = true := by
      cases ka <;> cases kb
      · exact hcop.1.1
      · exact hcop.2.1
      · exact hcop.1.2
      · exact hcop.2.2
    have gN (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.1.toNat).getD t 0 = (ws[t]).1.toNat := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gP (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.2.1).getD t 0 = (ws[t]).2.1 := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gQ (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.2.2).getD t 0 = (ws[t]).2.2 := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gC (t : Nat) (ht : t < ws.length) : (ws.map dcol).getD t 0 = dcol ws[t] := by
      simp [List.getD_eq_getElem?_getD, ht]
    rw [gN i hi, gN j hj, gP i hi, gP j hj, gQ i hi, gQ j hj, gC i hi, gC j hj] at hcm
    unfold checkMove at hcm
    simp only [force_eq] at hcm
    -- Prove ImpossibleBV directly!
    intro t ht hlive
    have ha : ws[i] ∈ ws := List.getElem_mem hi
    have hb : ws[j] ∈ ws := List.getElem_mem hj
    have hne1 : (ws[i]).1 ≠ (ws[j]).1 := fun e => hij ((List.Nodup.getElem_inj_iff hnd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
    have hne : ws[i] ≠ ws[j] := fun e => hne1 (congrArg Prod.fst e)
    let rest := delTwo ws ws[i] ws[j] ka kb
    let zD := dbin op ws[i] ws[j]
    have hsub : rest.Sublist ws := delTwo_sub ws ws[i] ws[j] ka kb
    have hndc : (zD.1 :: rest.map Prod.fst).Nodup :=
      List.nodup_cons.mpr ⟨fun hm => hfr ((hsub.map _).subset hm), hnd.sublist (hsub.map _)⟩
    have hsz := liveBV_size hlive
    change (zD.1 :: rest.map Prod.fst).toFinset.card ≤ t + 1 at hsz
    rw [List.toFinset_card_of_nodup hndc] at hsz
    have hlenC : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = (zD.1 :: rest.map Prod.fst).length := by
      rw [List.length_cons, List.length_map, delTwo_len ws ws[i] ws[j] ka kb ha hb hne, Nat.add_comm 1]
    have hbleF : Nat.ble (Nat.succ k) (1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1))) = false := by
      apply Bool.eq_false_iff.mpr; intro hb; have := Nat.ble_eq.mp hb; omega
    rw [hbleF] at hcm; simp only [Bool.false_eq_true, ite_false] at hcm
    -- Cover check must pass!
    have hcovAll := live6_cover_eq hcrit
      (fun w hw => by rcases List.mem_cons.mp hw with rfl | hwr; exact faithful_dbin op (hwsF _ ha) (hwsF _ hb); exact hwsF _ (hsub.subset hwr))
      (show LiveBV g.target t ((zD :: rest).map Prod.fst).toFinset from hlive)
    simp only [List.map_cons, orList] at hcovAll
    rw [delTwo_cov ha hb hne ka kb] at hcovAll
    have hcovAll' : Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD) = allOnesNat g.pos.length :=
      (Nat.lor_comm _ _).trans hcovAll
    have hcovEq : Nat.beq (Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD)) (allOnesNat g.pos.length) = true :=
      Nat.beq_eq.mpr hcovAll'
    change (if !(Nat.beq (Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD)) (allOnesNat g.pos.length)) then true else _) = true at hcm
    rw [hcovEq] at hcm; simp only [Bool.not_true, ite_false] at hcm
    -- zVal is proper and fresh!
    rw [zN_full] at hcm
    have hz0 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat 0 = false := by
      apply Bool.eq_false_iff.mpr; intro he
      exact hpr.1 (BitVec.toNat_inj.mp (by simpa [zeroBV] using Nat.eq_of_beq_eq_true he))
    have hz1 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat 18446744073709551615 = false := by
      apply Bool.eq_false_iff.mpr; intro he
      have hall : (oneBV (N := 64)).toNat = 18446744073709551615 := by decide +kernel
      exact hpr.2 (BitVec.toNat_inj.mp (by rw [hall]; exact Nat.eq_of_beq_eq_true he))
    have hzFresh : anyEq (binBV op (ws[i]).1 (ws[j]).1).toNat (ws.map fun w => w.1.toNat) = false := by
      apply Bool.eq_false_iff.mpr; intro hm
      obtain ⟨w, hw, he⟩ := List.mem_map.mp ((anyEq_iff _ _).mp hm)
      exact hfr (BitVec.toNat_inj.mp he.symm ▸ List.mem_map_of_mem hw)
    rw [hz0, hz1, hzFresh] at hcm
    simp only [Bool.or_false, Bool.false_eq_true, ite_false, Bool.or_eq_true, List.any_eq_true] at hcm
    rcases hcm with ⟨_, hqm, hfc⟩ | hlk
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hqm
      exact fastCost_sound (hpv p hp) hi hj hij hop hnd hfr hfc t ht hlive
    · have hsum : ((ws.map fun w : DWire => w.1.toNat).map kwN).sum = (ws.map fun w : DWire => kwN w.1.toNat).sum := by
        rw [List.map_map]; rfl
      rw [hsum] at hlk
      exact linkAt_sound hnd hi hj hij hfl hlk t ht hlive
  -- Apply enum_step!
  apply enum_step hnd hout
  intro a ha b hb d hd ka kb hab hfr hpr _
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
  have hij : i ≠ j := fun e => hab (by subst e; rfl)
  rcases checkAllPairs_at hbody (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij with hcp | hcp
  · rw [← binary_front hnd (List.getElem_mem hi) (List.getElem_mem hj) hab]
    exact onePair i j d ka kb hi hj hij hd hfr hpr hcp
  · rw [childTwo_swap _ hnd _ _ d hd ka kb, ← binary_front hnd (List.getElem_mem hj) (List.getElem_mem hi) (Ne.symm hab)]
    exact onePair j i (flipOp d) kb ka hj hi (Ne.symm hij) (flipOp_lt hd)
      (binBV_flip (N := 64) hd _ _ ▸ hfr) (binBV_flip (N := 64) hd _ _ ▸ hpr) hcp

-- Forest validity & induction over levels!
def graphValid (g : Forest) (baseOf : Nat → List Sig × Sig × Nat) : Bool :=
  ((rawOf g.vmask).length == g.rawCols.length) &&
  (List.range g.pos.length).all (fun i =>
    bitBV (g.pos.getD i ⟨0, by decide⟩) g.target != bitBV (g.neg.getD i ⟨0, by decide⟩) g.target) &&
  g.rawD.all (fun w =>
    (List.range g.pos.length).all (fun i =>
      (w.2.1.testBit i == bitBV (g.pos.getD i ⟨0, by decide⟩) w.1) &&
      (w.2.2.testBit i == bitBV (g.neg.getD i ⟨0, by decide⟩) w.1)) &&
    decide (w.2.1 < 2 ^ g.pos.length) && decide (w.2.2 < 2 ^ g.pos.length)) &&
  g.cuts.all (fun c => checkCut g.vmask g.target c baseOf) &&
  g.autos.all (fun p => autoCheck g.target p)

def levelsChecked (g : Forest) : Prop :=
  ∀ k ≤ g.cap, ∀ tree, g.levels k = some tree → tree.all (fastNodeOK g k) = true

theorem forest_all (g : Forest) (baseOf : Nat → List Sig × Sig × Nat)
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (hg : graphValid g baseOf = true) (hl : levelsChecked g) :
    ∀ k ≤ g.cap, ∀ tree, g.levels k = some tree → ∀ p, ImpossibleBV g.target k (g.nodeVals (tree.get p)).toFinset := by
  unfold graphValid at hg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨hlen, hcrit⟩, hrawF⟩, hcuts⟩, hautos⟩ := hg
  have hcrit' : CritOK g.target g.pos g.neg := fun i hi => hcrit i (List.mem_range.mpr hi)
  have hrawF' : ∀ w ∈ g.rawD, Faithful g.pos g.neg w := fun w hw => by
    have := hrawF w hw; exact ⟨fun i hi => this.1.1 i (List.mem_range.mpr hi), this.1.2, this.2⟩
  have hcuts' : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L :=
    fun c hc => checkCut_sound hb (hcuts c hc)
  intro k
  induction k with
  | zero =>
    intro hk tree htree p
    exact fastNodeOK_sound g 0 (tree.get p) hlen hcrit' hrawF' hcuts' hautos (by omega)
      (BTree.get_all (hl 0 hk tree htree) p)
  | succ k ih =>
    intro hk tree htree p
    exact fastNodeOK_sound g (k + 1) (tree.get p) hlen hcrit' hrawF' hcuts' hautos
      (fun _ t ht q => ih (by omega) t ht q)
      (BTree.get_all (hl (k + 1) hk tree htree) p)

def rootCheck (g : Forest) : Bool :=
  properB g.target && plainWordBV g.target && (rawOf g.vmask).all plainWordBV &&
  (rawOf g.vmask).all (essentialCheck6 g.target (rawOf g.vmask)) &&
  match g.levels g.cap with
  | none => false
  | some tree =>
    let vals := g.nodeVals (tree.get 0)
    vals.all (fun v => (rawOf g.vmask).contains v) && (rawOf g.vmask).all (fun v => vals.contains v)

theorem lower_forest (g : Forest) (baseOf : Nat → List Sig × Sig × Nat)
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (hg : graphValid g baseOf = true) (hl : levelsChecked g) (hr : rootCheck g = true) :
    LowerBV (rawOf g.vmask) g.target (g.cap + 1) := by
  unfold rootCheck at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨hp, hpt⟩, hpr⟩, hess⟩, hroot⟩ := hr
  cases hlev : g.levels g.cap with
  | none => simp [hlev] at hroot
  | some tree =>
    simp only [hlev, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hroot
    have himp := forest_all g baseOf hb hg hl g.cap (Nat.le_refl _) tree hlev 0
    have heq : (g.nodeVals (tree.get 0)).toFinset = (rawOf g.vmask).toFinset := by
      ext v; simp only [List.mem_toFinset]; exact ⟨hroot.1 v, hroot.2 v⟩
    rw [heq] at himp
    exact lowerBV_impossible (proper_of hp) hpt hpr
      (fun a ha => essentialCheck6_sound (List.all_eq_true.mp hess a ha)) himp

-- ============================================================
-- 6. Certificate Data, Verification, Monotone Witness & Main
-- ============================================================
noncomputable section CertData
def tF1 : Sig := 0xffffff00ff000000#64
def F1P : List Row := mkRows [24,24,24,40,40,40,48,48,48]
def F1N : List Row := mkRows [8,16,32,8,16,32,8,16,32]
def F1R : List (Nat × Nat) := [(63,73),(455,146),(504,292)]
def F1A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,2,4,3,5],[0,1,2,4,5,3],[0,1,2,5,3,4],[0,1,2,5,4,3]]
def F1C : List CutSpec := []
def F1T3 : BTree NodeData := lf 0x70 []
def F1L : Nat → Option (BTree NodeData) | 3 => some F1T3 | _ => none
def F1M : Nat → BST | _ => BE
def tF2 : Sig := 0xfffffff0fff0f000#64
def F2P : List Row := mkRows [12,12,12,12,20,20,20,20,24,24,24,24,36,36,36,36,40,40,40,40,48,48,48,48]
def F2N : List Row := mkRows [4,8,16,32,4,8,16,32,4,8,16,32,4,8,16,32,4,8,16,32,4,8,16,32]
def F2R : List (Nat × Nat) := [(61695,1118481),(986895,2236962),(15732720,4473924),(16773120,8947848)]
def F2A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,2,4,3,5],[0,1,2,4,5,3],[0,1,2,5,3,4],[0,1,2,5,4,3],[0,1,3,2,4,5],[0,1,3,2,5,4],[0,1,3,4,2,5],[0,1,3,4,5,2],[0,1,3,5,2,4],[0,1,3,5,4,2],[0,1,4,2,3,5],[0,1,4,2,5,3],[0,1,4,3,2,5],[0,1,4,3,5,2],[0,1,4,5,2,3],[0,1,4,5,3,2],[0,1,5,2,3,4],[0,1,5,2,4,3],[0,1,5,3,2,4],[0,1,5,3,4,2],[0,1,5,4,2,3],[0,1,5,4,3,2]]
def F2C : List CutSpec := [⟨16,0,4,1,0,[0,1,3,4,2,5],0xffff0000ffff#64⟩,⟨4,0,4,1,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨8,0,4,1,0,[0,1,3,2,4,5],0xff00ff00ff00ff#64⟩,⟨32,0,4,1,0,[0,1,3,4,5,2],0xffffffff#64⟩]
def F2T3 : BTree NodeData := nd (lf 0x1214811000783 [0x20001]) (lf 0x3535091000473 [])
def F2T4 : BTree NodeData := nd (lf 0x48110003e2 [0x10003]) (nd (lf 0x50910002f2 [0x4]) (lf 0xd0910002f2 []))
def F2M4 : BST := BN 246176673 0 (BL 142170705 128) BE
def F2T5 : BTree NodeData := lf 0x110001f1 [0x100030002,0x4]
def F2M5 : BST := BN 264638547 385 (BN 239237001 0 (BN 239181461 128 (BL 214627343 384) BE) (BL 253069531 129)) (BN 271980395 1 (BL 269023962 7) (BL 299662611 6))
def F2T6 : BTree NodeData := lf 0xf0 [0x100030002,0x4]
def F2M6 : BST := BN 230260810 2 (BN 215866071 0 (BL 206320026 10) (BL 223391134 16)) (BN 263004204 4 (BL 236958675 8) BE)
def F2L : Nat → Option (BTree NodeData) | 3 => some F2T3 | 4 => some F2T4 | 5 => some F2T5 | 6 => some F2T6 | _ => none
def F2M : Nat → BST | 4 => F2M4 | 5 => F2M5 | 6 => F2M6 | _ => BE
def tF3 : Sig := 0xfffcfffcffc0ffc0#64
def F3P : List Row := mkRows [6,6,6,8,8,8,34,34,34,36,36,36]
def F3N : List Row := mkRows [2,4,32,2,4,32,2,4,32,2,4,32]
def F3R : List (Nat × Nat) := [(455,585),(3591,1170),(56,0),(4032,2340)]
def F3A : List (List Nat) := [[0,1,2,3,4,5],[0,1,5,3,4,2],[0,2,1,3,4,5],[0,2,5,3,4,1],[0,5,1,3,4,2],[0,5,2,3,4,1]]
def F3C : List CutSpec := [⟨8,0,4,1,0,[0,3,4,1,2,5],0xff00ff00ff00ff#64⟩]
def F3T4 : BTree NodeData := lf 0xf0 [0x1]
def F3L : Nat → Option (BTree NodeData) | 4 => some F3T4 | _ => none
def F3M : Nat → BST | _ => BE
def tF4 : Sig := 0xfff0ff00ff000000#64
def F4P : List Row := mkRows [24,24,24,24,40,40,40,40,52,52,52,52]
def F4N : List Row := mkRows [12,20,36,48,12,20,36,48,12,20,36,48]
def F4R : List (Nat × Nat) := [(3840,1911),(255,273),(3855,2730),(4080,3276)]
def F4A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4]]
def F4C : List CutSpec := [⟨0,4,4,1,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩]
def F4T4 : BTree NodeData := lf 0xf0 [0x1]
def F4L : Nat → Option (BTree NodeData) | 4 => some F4T4 | _ => none
def F4M : Nat → BST | _ => BE
def tF5 : Sig := 0xfcfcc0c0c0c00000#64
def F5P : List Row := mkRows [22,22,22,22,22,22,38,38,38,38,38,38,50,50,50,50,50,50,52,52,52,52,52,52]
def F5N : List Row := mkRows [6,18,20,34,36,48,6,18,20,34,36,48,6,18,20,34,36,48,6,18,20,34,36,48]
def F5R : List (Nat × Nat) := [(262143,2929355),(16519167,5592405),(16773183,10119590),(16777152,14913080)]
def F5A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,4,3,2,5],[0,1,4,3,5,2],[0,1,5,3,2,4],[0,1,5,3,4,2],[0,2,1,3,4,5],[0,2,1,3,5,4],[0,2,4,3,1,5],[0,2,4,3,5,1],[0,2,5,3,1,4],[0,2,5,3,4,1],[0,4,1,3,2,5],[0,4,1,3,5,2],[0,4,2,3,1,5],[0,4,2,3,5,1],[0,4,5,3,1,2],[0,4,5,3,2,1],[0,5,1,3,2,4],[0,5,1,3,4,2],[0,5,2,3,1,4],[0,5,2,3,4,1],[0,5,4,3,1,2],[0,5,4,3,2,1]]
def F5C : List CutSpec := [⟨0,4,4,1,0,[0,3,1,2,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,16,4,1,0,[0,3,4,1,2,5],0xffff0000ffff0000#64⟩,⟨0,32,4,1,0,[0,3,4,1,5,2],0xffffffff00000000#64⟩,⟨0,2,4,1,0,[0,1,3,2,4,5],0xcccccccccccccccc#64⟩]
def F5T3 : BTree NodeData := nd (lf 0x210801000783 [0x20001]) (lf 0x2531081000473 [])
def F5T4 : BTree NodeData := nd (lf 0x8010003e2 [0x20001]) (nd (lf 0x10810002f2 [0x3]) (lf 0x90810002f2 []))
def F5M4 : BST := BN 361592107 128 (BL 225791769 0) BE
def F5T5 : BTree NodeData := lf 0x10001f1 [0x200040001,0x3]
def F5M5 : BST := BN 304804510 7 (BN 300772491 129 (BN 297662232 385 (BL 251787768 1) BE) (BL 304551422 128)) (BN 322156621 6 (BL 318464957 0) (BL 338306344 384))
def F5T6 : BTree NodeData := lf 0xf0 [0x200040001,0x3]
def F5M6 : BST := BN 289680740 8 (BN 272328629 10 (BL 264191322 4) (BL 281984186 16)) (BN 337972941 0 (BL 330868511 2) BE)
def F5L : Nat → Option (BTree NodeData) | 3 => some F5T3 | 4 => some F5T4 | 5 => some F5T5 | 6 => some F5T6 | _ => none
def F5M : Nat → BST | 4 => F5M4 | 5 => F5M5 | 6 => F5M6 | _ => BE
def tF6 : Sig := 0xffc0ffc0c000c000#64
def F6P : List Row := mkRows [14,14,14,14,14,38,38,38,38,38,40,40,40,40,40]
def F6N : List Row := mkRows [6,10,12,34,36,6,10,12,34,36,6,10,12,34,36]
def F6R : List (Nat × Nat) := [(1023,11627),(1023,22197),(31775,6342),(32736,25368)]
def F6A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,5,4,3],[0,2,1,3,4,5],[0,2,1,5,4,3]]
def F6C : List CutSpec := [⟨0,2,4,1,0,[0,1,3,4,2,5],0xcccccccccccccccc#64⟩]
def F6T4 : BTree NodeData := lf 0xf0 [0x1]
def F6L : Nat → Option (BTree NodeData) | 4 => some F6T4 | _ => none
def F6M : Nat → BST | _ => BE
def tF7 : Sig := 0xfefefefe80808080#64
def F7P : List Row := mkRows [7,7,7,7,33,33,33,33,34,34,34,34,36,36,36,36]
def F7N : List Row := mkRows [3,5,6,32,3,5,6,32,3,5,6,32,3,5,6,32]
def F7R : List (Nat × Nat) := [(255,13107),(3855,21845),(61455,26214),(65520,34952)]
def F7A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def F7C : List CutSpec := [⟨1,0,2,0,0,[0,1,2,3,4,5],0x5555555555555555#64⟩,⟨0,1,2,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,2,2,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨0,3,1,0,0,[0,1,2,3,4,5],0x8888888888888888#64⟩,⟨3,0,1,0,0,[0,1,2,3,4,5],0x1111111111111111#64⟩,⟨2,0,2,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,4,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨5,0,1,0,0,[0,1,2,3,4,5],0x505050505050505#64⟩,⟨0,5,1,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩]
def F7T2 : BTree NodeData := lf 0x35444010004c3 []
def F7T3 : BTree NodeData := nd (nd (nd (lf 0x44010003c2 [0x20001]) (nd (lf 0xc4210003c2 []) (lf 0x50a10002b2 [0x1]))) (nd (lf 0x90a10002b2 [0x3]) (nd (lf 0x50e1000272 [0x2]) (lf 0x90e1000272 [0x1])))) (nd (nd (lf 0x9043000252 []) (nd (lf 0x50430002d2 [0x1]) (lf 0x90430002d2 []))) (nd (nd (lf 0xd053000252 []) (lf 0x10530002d2 [0x2])) (nd (lf 0xd0530002d2 []) (lf 0xcc23000362 []))))
def F7M3 : BST := BL 140647539 0
def F7T4 : BTree NodeData := nd (nd (nd (lf 0x10001f1 [0x10004]) (lf 0x110001f1 [0x20005])) (nd (lf 0x210001f1 [0x30001]) (nd (lf 0x3000171 [0x600030001,0x80007]) (lf 0x30001f1 [0x20001])))) (nd (nd (lf 0x13000171 [0x300060002,0x70008]) (nd (lf 0x130001f1 [0x10002]) (lf 0x23000171 [0x90005]))) (nd (lf 0x230001f1 [0x20001]) (nd (lf 0x33000171 [0xa0004]) (lf 0x330001f1 [0x10002]))))
def F7M4 : BST := BN 199498399 1409 (BN 119141266 129 (BN 107027481 384 (BN 101328901 640 (BL 100457831 1408) BE) (BL 116297009 896)) (BN 175677306 128 (BN 130584829 641 (BL 128410794 1665) BE) (BL 184946834 1664))) (BN 230686466 897 (BN 214950321 256 (BN 214016832 0 (BL 203889354 1792) BE) (BL 221416938 385)) (BN 267714796 768 (BN 239767189 512 (BL 238370446 1536) BE) (BL 320583751 1920)))
def F7T5 : BTree NodeData := lf 0xf0 []
def F7M5 : BST := BN 261503709 261 (BN 217058619 1922 (BN 194644577 772 (BN 192785291 512 (BN 186533124 259 (BL 186507270 770) BE) (BL 193549085 130)) (BN 203914105 1796 (BN 202818613 642 (BL 195776798 1794) BE) (BL 207789091 898))) (BN 240069439 384 (BN 230799911 1664 (BN 226226062 768 (BL 219304301 1) BE) (BL 235495590 1792)) (BN 259226123 257 (BL 252883374 256) (BL 261335169 1668)))) (BN 283231814 513 (BN 277144977 1920 (BN 270604697 388 (BN 269558417 3 (BL 267875449 896) BE) (BL 273618584 1666)) (BN 277468324 128 (BL 277288130 258) (BL 282888112 386))) (BN 289394846 260 (BN 286737852 640 (BN 284237818 515 (BL 283927332 132) BE) (BL 289102638 900)) (BN 298372166 1924 (BL 293196860 644) (BL 311635856 0))))
def F7L : Nat → Option (BTree NodeData) | 2 => some F7T2 | 3 => some F7T3 | 4 => some F7T4 | 5 => some F7T5 | _ => none
def F7M : Nat → BST | 3 => F7M3 | 4 => F7M4 | 5 => F7M5 | _ => BE
def tF8 : Sig := 0xfefefefefefe8080#64
def F8P : List Row := mkRows [7,7,7,7,17,17,17,17,18,18,18,18,20,20,20,20,33,33,33,33,34,34,34,34,36,36,36,36]
def F8N : List Row := mkRows [3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48]
def F8R : List (Nat × Nat) := [(983295,53687091),(15732495,89478485),(251719695,107374182),(65520,143165576),(268369920,143165576)]
def F8A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4],[1,0,2,3,4,5],[1,0,2,3,5,4],[1,2,0,3,4,5],[1,2,0,3,5,4],[2,0,1,3,4,5],[2,0,1,3,5,4],[2,1,0,3,4,5],[2,1,0,3,5,4]]
def F8C : List CutSpec := [⟨32,0,6,7,0,[0,1,2,3,5,4],0xffffffff#64⟩]
def F8T6 : BTree NodeData := lf 0x1f0 [0x1]
def F8L : Nat → Option (BTree NodeData) | 6 => some F8T6 | _ => none
def F8M : Nat → BST | _ => BE
def tF9 : Sig := 0xfee8fee8fe80fe80#64
def F9P : List Row := mkRows [7,7,7,7,7,7,7,9,9,9,9,9,9,9,10,10,10,10,10,10,10,12,12,12,12,12,12,12,35,35,35,35,35,35,35,37,37,37,37,37,37,37,38,38,38,38,38,38,38]
def F9N : List Row := mkRows [3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40]
def F9R : List (Nat × Nat) := [(4397778092031,48759444784523),(558586000294015,93086212770453),(562915860021375,168441718346534),(268435328,283691315109952),(562949684985856,531921215831160)]
def F9A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def F9C : List CutSpec := [⟨32,3,1,0,0,[0,1,2,3,4,5],0x88888888#64⟩,⟨0,8,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨32,0,6,7,0,[0,1,2,5,3,4],0xffffffff#64⟩,⟨2,1,2,0,0,[0,1,2,3,4,5],0x2222222222222222#64⟩,⟨4,8,1,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨2,5,1,0,0,[0,1,2,3,4,5],0x2020202020202020#64⟩,⟨0,32,7,2,0,[2,3,4,5,0,1],0xffffffff00000000#64⟩,⟨1,0,5,4,0,[0,4,5,3,1,2],0x5555555555555555#64⟩,⟨8,0,7,5,0,[1,2,4,0,3,5],0xff00ff00ff00ff#64⟩,⟨0,2,5,3,0,[1,0,2,3,4,5],0xcccccccccccccccc#64⟩,⟨32,5,1,0,0,[0,1,2,3,4,5],0xa0a0a0a0#64⟩,⟨37,0,1,0,0,[0,1,2,3,4,5],0x5050505#64⟩,⟨0,4,5,3,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,5,4,0,[4,5,0,3,1,2],0xf0f0f0f0f0f0f0f#64⟩,⟨8,1,4,1,0,[0,3,4,1,2,5],0xaa00aa00aa00aa#64⟩,⟨2,0,5,4,0,[4,0,5,3,1,2],0x3333333333333333#64⟩,⟨0,1,5,3,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨8,4,4,1,0,[3,4,0,1,2,5],0xf000f000f000f0#64⟩,⟨4,3,1,0,0,[0,1,2,3,4,5],0x808080808080808#64⟩,⟨8,2,4,1,0,[3,0,4,1,2,5],0xcc00cc00cc00cc#64⟩]
def F9T2 : BTree NodeData := nd (lf2 0x1cb654401004186 0xe6172 [0x20001]) (lf2 0x9cb654401006106 0x60f72 [0x22f03])
def F9T3 : BTree NodeData := nd (nd (lf2 0x1cb654401003185 0x172 [0x40001]) (lf2 0x9cb654401003185 0x372 [0xf0300050001])) (nd (lf2 0x9cb654401002945 0x183 []) (lf2 0xdcb654401002945 0x183 [0x5]))
def F9M3 : BST := BN 142309538 128 (BL 62241331 0) BE
def F9T4 : BTree NodeData := nd (nd (nd (lf 0xd95324401001944 [0xf070006]) (lf 0x1d9324401001344 [0xf070b090c08,0xa])) (nd (lf 0xd97434401001844 [0xb00010b03,0xc]) (lf 0x1cb6544010019c4 [0x10006]))) (nd (nd (lf 0x5cb6544010019c4 [0xb]) (lf 0x9cb6544010019c4 [0x7090004000c])) (nd (lf 0xdcb6544010019c4 [0x7090001070d,0x7030707]) (lf 0x5cf654401001944 [0x50f070004,0x70d])))
def F9M4 : BST := BN 181200337 384 (BN 144331428 256 (BL 62993440 0) BE) (BL 270966375 128)
def F9T5 : BTree NodeData := nd (nd (nd (nd (lf 0x1324401000f43 [0x408040a030d,0x10e0707]) (lf 0x2324401000f03 [0x408040a0707,0x10e])) (nd (lf 0x2324401000f43 [0x4080707040a,0x309010e]) (lf 0x624401000b83 [0x10e04080709,0x707]))) (nd (nd (lf 0x3434401000e43 [0x40a04080303]) (lf 0x3634401000b43 [0x7070408000f,0x10e])) (nd (lf 0x36544010009c3 [0x7070709]) (nd (lf 0x163c801000b63 [0xf010e0610,0x707]) (lf 0x3654c81000973 [0x80707010d,0x11]))))) (nd (nd (nd (lf 0x528c11000d23 [0x20a07070408]) (lf 0x3528c11000d23 [0x20a07070408])) (nd (lf 0x654c91000973 [0x707020a010d,0x6080610]) (nd (lf 0x2658c91000933 [0x61006080707,0x60a0611]) (lf 0x163d491000933 [0x411040a0707])))) (nd (nd (lf 0x132c421000f43 [0x4110707030d,0x408]) (lf 0x343c421000e43 [0x41104080303])) (nd (lf 0x3654ca1000973 [0x7070208020a,0x509]) (nd (lf 0x625463000b23 [0x10a07070408]) (lf 0x3625463000b23 [0x10a07070408])))))
def F9M5 : BST := BN 207787473 0 (BN 166391428 896 (BN 158630085 128 (BL 147804711 384) BE) (BL 180824903 768)) (BN 272988265 640 (BL 243151869 256) (BL 291202998 512))
def F9T6 : BTree NodeData := nd (nd (nd (nd (lf 0x44010007c2 [0x8000a0309,0x10e0307]) (nd (lf 0xc8010007e2 [0x3070210010e,0x309]) (lf 0x4c81000772 [0x3070208010d,0x110010020a,0xe000a0211]))) (nd (lf 0x8c81000732 [0x21003070208,0x12010e]) (nd (lf 0x8c81000772 [0x3070208010e,0x120210]) (lf 0xd0c1000672 [0x21001030208,0x20e020d])))) (nd (nd (lf 0x54c1000572 [0x10903070013,0x8000d000e,0x10]) (nd (lf 0x8c11000762 [0x3070008020a,0x20d020e]) (lf 0x4c91000772 [0x307010d020a,0xe0211]))) (nd (lf 0x8c91000732 [0x2110307020a,0x12000e]) (nd (lf 0x8c91000772 [0x307010e020a,0x20300120211]) (lf 0x14910005b2 [0x11000a0309,0x307000e]))))) (nd (nd (nd (lf 0xd4910005b2 [0xd03070309,0x11000a]) (nd (lf 0xd0d1000672 [0x1030211020a,0x20d020e]) (lf 0xd4d1000572 [0x307000a000f,0xd000e0009]))) (nd (lf 0xc4210007c2 [0x803070309,0x11]) (nd (lf 0x8c61000752 [0x30700100208,0x10e020e020d]) (lf 0x4ca1000772 [0x307010d020a,0x100208])))) (nd (nd (lf 0x8ca1000732 [0x2080307020a,0x12010e]) (nd (lf 0x8ca1000772 [0x307020a010e,0x120208]) (lf 0xd0e1000672 [0x103020a0208,0x20e020d]))) (nd (lf 0x54e1000572 [0x30700080014,0xd000e0109]) (nd (lf 0x5463000762 [0x3070008010a,0x10d010e]) (lf 0x9463000762 [0x3070110000f,0x10d010e0008])))))
def F9M6 : BST := BN 270086771 3968 (BN 215226309 512 (BN 157062566 1024 (BN 145083537 768 (BL 128777135 3712) BE) (BN 204279451 1795 (BL 171732109 1154) BE)) (BN 253166923 1152 (BN 230408860 1664 (BL 215547887 130) BE) (BN 269971457 640 (BL 263260173 1920) BE))) (BN 301556808 1280 (BN 281156766 0 (BN 274531796 1536 (BL 270118589 3840) BE) (BN 297498237 896 (BL 296982701 128) BE)) (BN 320775026 1792 (BN 316521162 256 (BL 306907123 384) BE) (BL 342271519 1408)))
def F9T7 : BTree NodeData := nd (nd (lf 0x10003f1 [0x10701090008,0xe000d0010]) (nd (lf 0x110003f1 [0x1070109000a,0xd000e0011,0x3]) (lf 0x210003f1 [0x80109000a,0xe000d0107]))) (nd (nd (lf 0x13000371 [0x1001070011,0xd000e000a]) (lf 0x23000361 [0x80107])) (nd (lf 0x23000371 [0xa01070008,0xe000d0010]) (lf 0x34300271 [0x3])))
def F9M7 : BST := BN 317676861 515 (BN 253300255 3840 (BN 218452830 0 (BN 195929108 384 (BN 159468921 1282 (BL 135831025 768) (BL 193994768 1792)) (BN 216683005 896 (BL 209484477 128) BE)) (BN 243093912 1411 (BN 234651568 387 (BL 219567004 1664) (BL 240903735 1280)) (BN 244915818 1027 (BL 244203187 640) BE))) (BN 293531834 256 (BN 274311274 3715 (BN 254681590 512 (BL 254092851 1408) (BL 259925225 3328)) (BN 289037454 3459 (BL 280325267 3200) BE)) (BN 309110531 3969 (BN 295613592 1026 (BL 295289621 1152) BE) (BN 312845333 1536 (BL 309622153 389) BE)))) (BN 356039847 1921 (BN 331350258 1281 (BN 323039770 3968 (BN 320023308 3712 (BL 318064497 1413) (BL 321808631 3585)) (BN 326119205 1539 (BL 325406574 1666) BE)) (BN 344570269 1920 (BN 337513290 1668 (BL 332356262 771) (BL 340798606 1795)) (BN 355387704 3456 (BL 349281859 3717) BE))) (BN 379792460 3458 (BN 372015968 3331 (BN 361730453 3457 (BL 357336567 3075) (BL 364008039 3461)) (BN 378775790 3072 (BL 372062747 3587) BE)) (BN 391899176 3460 (BN 386742148 1155 (BL 385736144 1153) BE) (BN 418105563 1024 (BL 414140186 3584) BE))))
def F9T8 : BTree NodeData := lf 0x1f0 [0x70009]
def F9M8 : BST := BN 258375698 130 (BN 223740299 1 (BN 180128270 388 (BN 145602423 642 (BL 121964527 644) BE) (BN 197221289 256 (BL 190969122 771) BE)) (BN 246058727 132 (BN 235479581 384 (BL 227037237 640) BE) (BN 257319372 768 (BL 248645601 386) BE))) (BN 281724128 770 (BN 266696943 128 (BN 265939707 773 (BL 263662121 769) BE) (BN 281423123 896 (BL 273994415 3) BE)) (BN 293830844 772 (BN 288673816 259 (BL 287667812 257) BE) (BL 316071854 0)))
def F9L : Nat → Option (BTree NodeData) | 2 => some F9T2 | 3 => some F9T3 | 4 => some F9T4 | 5 => some F9T5 | 6 => some F9T6 | 7 => some F9T7 | 8 => some F9T8 | _ => none
def F9M : Nat → BST | 3 => F9M3 | 4 => F9M4 | 5 => F9M5 | 6 => F9M6 | 7 => F9M7 | 8 => F9M8 | _ => BE
def tF10 : Sig := 0xfcc0fc00fc000000#64
def F10P : List Row := mkRows [26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,54,54]
def F10N : List Row := mkRows [14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56]
def F10R : List (Nat × Nat) := [(1057222719,255652815),(1073483712,392000983),(16777215,562436193),(1056968703,988524218),(1073737728,1022611260)]
def F10A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4],[0,4,5,3,1,2],[0,4,5,3,2,1],[0,5,4,3,1,2],[0,5,4,3,2,1]]
def F10C : List CutSpec := [⟨0,6,4,1,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨18,0,2,0,0,[0,1,2,3,4,5],0x333300003333#64⟩,⟨0,48,4,1,0,[0,3,4,5,1,2],0xffff000000000000#64⟩,⟨32,0,3,0,0,[0,1,2,3,4,5],0xffffffff#64⟩,⟨0,8,3,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨34,0,2,0,0,[0,1,2,3,4,5],0x33333333#64⟩,⟨16,0,3,0,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨0,16,5,4,0,[0,4,5,3,1,2],0xffff0000ffff0000#64⟩,⟨2,8,2,0,0,[0,1,2,3,4,5],0x3300330033003300#64⟩,⟨0,32,5,4,0,[0,4,5,3,2,1],0xffffffff00000000#64⟩,⟨36,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f#64⟩,⟨0,20,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f00000#64⟩,⟨2,4,2,0,0,[0,1,2,3,4,5],0x3030303030303030#64⟩,⟨32,8,2,0,0,[0,1,2,3,4,5],0xff00ff00#64⟩,⟨4,0,3,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨16,8,2,0,0,[0,1,2,3,4,5],0xff000000ff00#64⟩,⟨2,0,3,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,2,5,4,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨20,0,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f#64⟩,⟨0,56,1,0,0,[0,1,2,3,4,5],0xff00000000000000#64⟩,⟨36,16,1,0,0,[0,1,2,3,4,5],0xf0f0000#64⟩,⟨16,32,2,0,0,[0,1,2,3,4,5],0xffff00000000#64⟩,⟨4,8,2,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨0,4,5,4,0,[0,2,1,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨2,48,1,0,0,[0,1,2,3,4,5],0x3333000000000000#64⟩,⟨4,10,1,0,0,[0,1,2,3,4,5],0xc000c000c000c00#64⟩,⟨0,18,2,0,0,[0,1,2,3,4,5],0xcccc0000cccc0000#64⟩]
def F10T3 : BTree NodeData := lf 0x1d13294c1001404 [0xc01]
def F10T4 : BTree NodeData := nd (nd (nd (nd (nd (lf 0x2650c81000983 [0x5030002]) (lf 0x2631481000b03 [0x1040002])) (nd (lf 0x2651481000983 [0x50703]) (lf 0x2631481000b43 [0x40100020006]))) (nd (nd (lf 0x635481000943 [0x70005]) (lf 0x26390c1000a43 [0x2])) (nd (lf 0x23214c1000d03 [0x108]) (lf 0x16214c1000b83 [0x600090002,0x10a0401])))) (nd (nd (nd (lf 0x26214c1000b83 [0x40100060002]) (lf 0x13294c1000d03 [0x108])) (nd (lf 0x16294c1000983 [0x50703]) (lf 0x2630841000b03 [0x1040002]))) (nd (nd (lf 0x2630841000b43 [0x2000b]) (lf 0x1620c41000b83 [0x204010503,0xc])) (nd (lf 0x2620c41000b83 [0x40100020503]) (lf 0x2519402000d83 [0xe000d0002]))))) (nd (nd (nd (nd (lf 0x2539402000d23 [0x401]) (lf 0x26014c20009a3 [0x7000d0006])) (nd (lf 0x26114c2000993 [0x7000f0006]) (lf 0x2540c02000ce3 [0x508]))) (nd (nd (lf 0x26114c20009d3 [0x700110010]) (lf 0x538852000d03 [0x10])) (nd (lf 0x265cc62000983 [0x503]) (lf 0x263d462000b03 [0x2])))) (nd (nd (nd (lf 0x15314e2000d23 [0x108]) (lf 0x23214e2000d23 [0x108])) (nd (lf 0x23094e2000d23 [0x108]) (lf 0x26494e20008f3 [0x6120007]))) (nd (nd (lf 0x6154830009c3 [0x50603]) (lf 0x6454830008e3 [0x406080005,0x413])) (nd (lf 0x6154830009d3 [0xf06030010]) (lf 0x2619483000993 [0xf06030612])))))
def F10T5_0 := nd (nd (nd (nd (nd (lf 0xc81000782 [0x1030002]) (lf 0xc810007c2 [0x1401030002,0x7])) (nd (lf 0xcc81000782 [0x1030002]) (nd (lf 0xcc810007c2 [0x501030002,0x7]) (lf 0x1481000782 [0x10800060002,0x10a])))) (nd (nd (lf 0x14810007c2 [0x100060002,0x5010a0108]) (nd (lf 0x54810005c2 [0x703030005,0x4]) (lf 0xd481000582 [0xe00020303]))) (nd (lf 0xd481000782 [0x60002]) (nd (lf 0xd4810005c2 [0x3080002000e,0x7]) (lf 0xd4810007c2 [0x100060002]))))) (nd (nd (nd (lf 0x10c1000642 [0x10302010002]) (lf 0x10c1000742 [0x10a0006])) (nd (lf 0x90c10006c2 [0x2]) (nd (lf 0x14c10005c2 [0x1030010]) (lf 0x14c10007c2 [0x100090015,0x2])))) (nd (nd (lf 0x94c10005c2 [0x100016]) (nd (lf 0x841000782 [0xb0013]) (lf 0x8410007c2 [0x1000b0013,0x5]))) (nd (lf 0x8841000782 [0xb0013]) (nd (lf 0x88410007c2 [0x1000b0013,0x5]) (lf 0xc410007c2 [0x1701030002,0x1])))))) (nd (nd (nd (nd (lf 0xd4810005a2 [0x2180303000f]) (lf 0xd4810005e2 [0x218000f000e,0x700020308])) (nd (lf 0x14c10005e2 [0x100015]) (nd (lf 0x8821000782 [0xe0002]) (lf 0x88210007c2 [0x500060002,0x12])))) (nd (nd (lf 0xc210007c2 [0x1001030009]) (nd (lf 0x94210005c2 [0x203030001,0x700050006,0x4]) (lf 0x54a1000592 [0xe00100212,0x30a]))) (nd (lf 0x54a10005d2 [0x212000e0010]) (nd (lf 0x94e10005d2 [0x100019]) (lf 0x94020005a2 [0xe00020001,0x308]))))) (nd (nd (nd (lf 0x94020007a2 [0xe00010002,0x30a]) (lf 0x9442000592 [0xf03030212,0xd])) (nd (lf 0x9442000792 [0xd00060002]) (nd (lf 0x14c20005b2 [0x702010006]) (lf 0x54c2000732 [0x2001a])))) (nd (nd (lf 0x94c2000532 [0x600070201,0x30a]) (nd (lf 0x94c2000732 [0x6001a]) (lf 0x94c20005b2 [0x20101030002]))) (nd (lf 0x88020007e2 [0x1000010005,0xe0017]) (nd (lf 0xc02000762 [0x1100010006,0x800050010]) (lf 0xc020007e2 [0x101080010,0x13]))))))
def F10T5_1 := nd (nd (nd (nd (nd (lf 0x94020005e2 [0x20001000e,0x70308]) (lf 0x8842000792 [0xe00020010,0x6020a0208,0x1])) (nd (lf 0x94420005d2 [0x600130001,0x30a03080002,0x5000b0017]) (nd (lf 0x94420007d2 [0x11802120011,0x17]) (lf 0xcc82000732 [0x60002001a])))) (nd (nd (lf 0x14c20005f2 [0x1400110010,0x1b00070018,0xa001a]) (nd (lf 0x94c2000572 [0x2010006001a,0x30a]) (lf 0x94c20005f2 [0x1000190007]))) (nd (lf 0x8852000782 [0xe0010]) (nd (lf 0x14520005c2 [0xe00100001,0x308]) (lf 0x14d2000562 [0x10000e0001,0x30a]))))) (nd (nd (nd (lf 0x14d20005e2 [0x101030010]) (lf 0xc62000782 [0x1030002])) (nd (lf 0xc620007a2 [0x11801030002]) (nd (lf 0xcc62000782 [0x501180103]) (lf 0x1462000782 [0xe0002])))) (nd (nd (lf 0x14620007a2 [0x1000e0002,0xf]) (nd (lf 0x94620005a2 [0x303000f]) (lf 0x94620007a2 [0xe0002000d,0x30a00130308,0xb]))) (nd (lf 0xd462000782 [0xe0002]) (nd (lf 0x14e20007a2 [0x108000d000e]) (lf 0x94e20007a2 [0x1300020019])))))) (nd (nd (nd (nd (lf 0x8862000782 [0xe0010]) (lf 0x88620007a2 [0x118000e0010,0xf])) (nd (lf 0x94620005e2 [0x1000b0013,0x5]) (nd (lf 0xcca20007a2 [0x501030017]) (lf 0x14e20005e2 [0x13000e])))) (nd (nd (lf 0x94e20005e2 [0x1000130014,0x12]) (nd (lf 0xc220007a2 [0x101030011]) (lf 0x14e20005b2 [0x1101030201,0x7]))) (nd (lf 0x94e20005b2 [0x202010019]) (nd (lf 0x8c22000762 [0x10103]) (lf 0x14e20005f2 [0x500070011,0x1b00190212]))))) (nd (nd (nd (lf 0x94e20005f2 [0x21200140002,0x501080010,0xa]) (nd (lf 0x94430005e2 [0x102030013,0x50007]) (lf 0x54830007a2 [0x1302030010]))) (nd (lf 0x54830005e2 [0x1302030005,0x12]) (nd (lf 0x94830007a2 [0x208001b0010]) (lf 0x54830005b2 [0x2030201001b])))) (nd (nd (lf 0x54830005f2 [0x20302010009,0x70010]) (nd (lf 0x94830005b2 [0x1002030201]) (lf 0x94830005f2 [0x700100009]))) (nd (lf 0x54a3000532 [0x500030201]) (nd (lf 0x54a3000572 [0x302010005]) (lf 0x9523000472 [0x500030201]))))))
def F10T5 : BTree NodeData := nd F10T5_0 F10T5_1
def F10M5 : BST := BN 205669594 3329 (BN 172777833 1024 (BN 106671043 770 (BN 91930478 3712 (BN 70348595 512 (BL 49247754 2688) (BL 91053167 3201)) (BN 102235045 3330 (BL 94404371 2689) BE)) (BN 131909399 1280 (BN 120492170 1664 (BL 113707819 896) (BL 129726491 2560)) (BN 168481901 3328 (BL 139485972 128) BE))) (BN 184727835 513 (BN 179741290 0 (BN 172917899 768 (BL 172802342 2180) (BL 175691224 2944)) (BN 184674236 4 (BL 183872357 2048) BE)) (BN 191531303 3968 (BN 188475093 2304 (BL 188308355 3072) BE) (BN 199351854 3073 (BL 194915856 2049) BE)))) (BN 254703839 1792 (BN 243144574 2822 (BN 224052804 2818 (BN 216750997 1920 (BL 210105592 769) (BL 218070616 2176)) (BN 239875638 1152 (BL 226459260 3840) BE)) (BN 245759261 3972 (BN 244311636 640 (BL 243416932 1670) BE) (BN 253737107 256 (BL 251629136 3713) BE))) (BN 287534062 2432 (BN 266453294 1408 (BN 256344548 2816 (BL 255134471 1156) (BL 259570469 644)) (BN 278734402 1924 (BL 272835372 3584) BE)) (BN 329498551 1798 (BN 323541326 129 (BL 310406781 1794) BE) (BN 347723560 3456 (BL 341785710 3200) BE))))
def F10T6 : BTree NodeData := nd (nd (nd (lf 0x10003c1 [0x10103]) (nd (lf 0x10003e1 [0x1301030001,0xb]) (lf 0x210003d1 [0x10300180002,0x60012]))) (nd (lf 0x20003b1 [0x201030001,0x6]) (nd (lf 0x20003f1 [0x2001a0001,0x10a01080006,0xa00080009]) (lf 0x120003e1 [0xe00100001,0x108])))) (nd (nd (lf 0x220003a1 [0x1180103]) (nd (lf 0x220003e1 [0xe01030010,0x1201180017]) (lf 0x220003b1 [0x201030001,0x6]))) (nd (nd (lf 0x220003f1 [0xe00100001,0x2010a0108,0xa00080006]) (lf 0x30003e1 [0x1300100003,0x120118])) (nd (lf 0x30003f1 [0x1000030001,0x9001b0007]) (lf 0x23000371 [0x900010003]))))
def F10M6 : BST := BN 239012259 2689 (BN 187494886 640 (BN 166792778 3200 (BN 155794635 15489 (BN 138996019 4608 (BN 123471245 5120 (BN 115034730 1281 (BL 110638018 15488) BE) (BN 129726491 512 (BL 129526073 2561) BE)) (BN 147780499 6656 (BN 144001568 6657 (BL 140891309 1537) BE) (BL 149744376 2564))) (BN 163467535 6400 (BN 158552167 7937 (BN 157642016 7936 (BL 157062681 384) BE) (BL 162752966 7940)) (BN 165074927 5760 (BN 165064163 641 (BL 164277172 14721) BE) (BL 166281971 1409)))) (BN 177238340 5248 (BN 172777833 13312 (BN 169510925 2432 (BN 167903533 14592 (BL 167821695 16129) BE) (BL 170871067 4738)) (BN 176800752 7296 (BN 175039895 5888 (BL 172802342 1792) BE) (BL 177213831 7168))) (BN 181535421 1536 (BN 180848516 4737 (BN 179003573 5634 (BL 177975497 3584) BE) (BL 181202018 5376)) (BN 183439571 13826 (BN 182411495 7680 (BL 181711919 1280) BE) (BL 184114523 0))))) (BN 216254500 768 (BN 202531341 4100 (BN 196012921 2944 (BN 188550521 4096 (BN 188065228 1 (BL 187890234 4612) BE) (BN 192616604 4224 (BL 192501226 4097) BE)) (BN 198658242 3968 (BN 198200627 4736 (BL 198095343 4) BE) (BL 202165311 2305))) (BN 209334681 7552 (BN 206197330 15873 (BN 205944242 2304 (BL 203094240 8064) BE) (BL 206583359 4609)) (BN 215318939 5632 (BN 215226424 4480 (BL 214016947 15616) BE) (BL 215925116 2560)))) (BN 230874952 5505 (BN 222993138 3202 (BN 220690498 3840 (BN 219754937 13824 (BL 218452945 128) BE) (BL 221365450 14468)) (BN 225316155 14470 (BN 224063943 15104 (BL 223549441 15872) BE) (BL 229567982 7809))) (BN 234498884 16128 (BN 231572781 16001 (BN 231550949 4992 (BL 230941576 256) BE) (BL 234251011 7425)) (BN 235377574 4352 (BN 234801735 13952 (BL 234641192 14849) BE) (BL 238420123 14848)))))) (BN 289201720 14464 (BN 265584598 2052 (BN 256364370 2688 (BN 249659210 14080 (BN 243678818 16256 (BN 242730247 13568 (BL 242504641 14976) BE) (BN 247166245 3328 (BL 246492828 3586) BE)) (BN 252569866 4226 (BN 250928826 7682 (BL 250823677 2306) BE) (BL 254095208 13440))) (BN 262884352 13697 (BN 260105859 4482 (BN 259775630 4864 (BL 258050822 14726) BE) (BL 262013183 2816)) (BN 264737212 15874 (BN 264211628 2176 (BL 263417457 3072) BE) (BL 264889151 3457)))) (BN 273914245 2690 (BN 267853455 15360 (BN 266449181 6272 (BN 265796144 16132 (BL 265614081 14336) BE) (BL 267320350 15745)) (BN 270050079 1024 (BN 270020596 6148 (BL 269325149 897) BE) (BL 271416941 14720))) (BN 280007556 1408 (BN 275722885 3712 (BN 275306577 6785 (BL 275112117 13184) BE) (BL 275821011 258)) (BN 288288907 6784 (BN 283828982 15878 (BL 280257009 4354) BE) (BL 288539878 2049))))) (BN 342016672 1153 (BN 300668384 1664 (BN 295689414 7424 (BN 293253738 2048 (BN 293170739 1284 (BL 292975876 6145) BE) (BL 294620101 15232)) (BN 297689736 6144 (BN 297603251 14724 (BL 297552141 5504) BE) (BL 299056099 1920))) (BN 334881229 6912 (BN 325790805 6529 (BN 325117048 2310 (BL 313152736 7553) BE) (BL 330504665 6528)) (BN 339317227 1152 (BN 337580674 6913 (BL 336707751 7808) BE) (BL 340719383 6790)))) (BN 370024121 13696 (BN 359095249 5889 (BN 356690975 6532 (BN 352075200 14465 (BL 345298366 16000) BE) (BL 356857696 1793)) (BN 366127224 14081 (BN 361466094 7040 (BL 361293694 5249) BE) (BL 367029375 15105))) (BN 380974078 6016 (BN 374460119 15744 (BN 370563222 13441 (BL 370499361 5508) BE) (BL 378614736 3456)) (BN 419564455 6534 (BN 385410076 14208 (BL 383050734 896) BE) (BL 433372841 2694))))))
def F10T7 : BTree NodeData := lf 0x1f0 [0x30001]
def F10M7 : BST := BN 259357792 1414 (BN 228183042 1792 (BN 201219903 1536 (BN 190379051 130 (BN 181202018 0 (BL 165584142 1409) (BL 186865963 1926)) (BN 200093370 1542 (BL 194815049 642) (BL 200293788 4))) (BN 217259870 1413 (BN 212990748 1924 (BL 209563316 516) (BL 214016947 128)) (BN 218600884 1411 (BL 218452945 640) BE))) (BN 249570870 256 (BN 235952995 1410 (BN 232261331 1408 (BL 231311053 1538) (BL 234727318 1922)) (BN 242651051 1920 (BL 239365761 512) (BL 248542794 1666))) (BN 258447641 1412 (BN 254006868 768 (BL 252978792 386) (BL 254681820 260)) (BN 259117818 772 (BL 258632525 262) BE)))) (BN 300093676 1798 (BN 284245196 514 (BN 267495099 1415 (BN 263068523 774 (BL 260745506 1794) (BL 263144985 1796)) (BN 276764627 899 (BL 268627320 897) (BL 277150656 518))) (BN 290322234 770 (BN 286492413 1540 (BL 285886236 258) (BL 286964167 132)) (BN 294116738 898 (BL 291400165 644) BE))) (BN 346469106 1921 (BN 326041275 1925 (BN 317060125 1664 (BL 313058945 1927) (BL 321496123 384)) (BN 335304509 896 (BL 334185691 1923) BE)) (BN 363543173 390 (BN 354273645 646 (BL 349837647 134) (BL 359107175 1670)) (BN 368257033 388 (BL 363821035 1668) BE))))
def F10L : Nat → Option (BTree NodeData) | 3 => some F10T3 | 4 => some F10T4 | 5 => some F10T5 | 6 => some F10T6 | 7 => some F10T7 | _ => none
def F10M : Nat → BST | 5 => F10M5 | 6 => F10M6 | 7 => F10M7 | _ => BE
def tF11 : Sig := 0xe8e8808080800000#64
def F11P : List Row := mkRows [23,23,23,23,23,23,23,23,23,23,39,39,39,39,39,39,39,39,39,39,51,51,51,51,51,51,51,51,51,51,53,53,53,53,53,53,53,53,53,53,54,54,54,54,54,54,54,54,54,54]
def F11N : List Row := mkRows [7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52]
def F11R : List (Nat × Nat) := [(1099511627775,201407314713783),(1124801468956671,381903487462747),(1125898834149375,683464166323821),(1125899905795071,1001533641472910),(1125899906841600,1109391110554608)]
def F11A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,4,3,2,5],[0,1,4,3,5,2],[0,1,5,3,2,4],[0,1,5,3,4,2],[0,2,1,3,4,5],[0,2,1,3,5,4],[0,2,4,3,1,5],[0,2,4,3,5,1],[0,2,5,3,1,4],[0,2,5,3,4,1],[0,4,1,3,2,5],[0,4,1,3,5,2],[0,4,2,3,1,5],[0,4,2,3,5,1],[0,4,5,3,1,2],[0,4,5,3,2,1],[0,5,1,3,2,4],[0,5,1,3,4,2],[0,5,2,3,1,4],[0,5,2,3,4,1],[0,5,4,3,1,2],[0,5,4,3,2,1],[1,0,2,3,4,5],[1,0,2,3,5,4],[1,0,4,3,2,5],[1,0,4,3,5,2],[1,0,5,3,2,4],[1,0,5,3,4,2],[1,2,0,3,4,5],[1,2,0,3,5,4],[1,2,4,3,0,5],[1,2,4,3,5,0],[1,2,5,3,0,4],[1,2,5,3,4,0],[1,4,0,3,2,5],[1,4,0,3,5,2],[1,4,2,3,0,5],[1,4,2,3,5,0],[1,4,5,3,0,2],[1,4,5,3,2,0],[1,5,0,3,2,4],[1,5,0,3,4,2],[1,5,2,3,0,4],[1,5,2,3,4,0],[1,5,4,3,0,2],[1,5,4,3,2,0],[2,0,1,3,4,5],[2,0,1,3,5,4],[2,0,4,3,1,5],[2,0,4,3,5,1],[2,0,5,3,1,4],[2,0,5,3,4,1],[2,1,0,3,4,5],[2,1,0,3,5,4],[2,1,4,3,0,5],[2,1,4,3,5,0],[2,1,5,3,0,4],[2,1,5,3,4,0],[2,4,0,3,1,5],[2,4,0,3,5,1],[2,4,1,3,0,5],[2,4,1,3,5,0],[2,4,5,3,0,1],[2,4,5,3,1,0],[2,5,0,3,1,4],[2,5,0,3,4,1],[2,5,1,3,0,4],[2,5,1,3,4,0],[2,5,4,3,0,1],[2,5,4,3,1,0],[4,0,1,3,2,5],[4,0,1,3,5,2],[4,0,2,3,1,5],[4,0,2,3,5,1],[4,0,5,3,1,2],[4,0,5,3,2,1],[4,1,0,3,2,5],[4,1,0,3,5,2],[4,1,2,3,0,5],[4,1,2,3,5,0],[4,1,5,3,0,2],[4,1,5,3,2,0],[4,2,0,3,1,5],[4,2,0,3,5,1],[4,2,1,3,0,5],[4,2,1,3,5,0],[4,2,5,3,0,1],[4,2,5,3,1,0],[4,5,0,3,1,2],[4,5,0,3,2,1],[4,5,1,3,0,2],[4,5,1,3,2,0],[4,5,2,3,0,1],[4,5,2,3,1,0],[5,0,1,3,2,4],[5,0,1,3,4,2],[5,0,2,3,1,4],[5,0,2,3,4,1],[5,0,4,3,1,2],[5,0,4,3,2,1],[5,1,0,3,2,4],[5,1,0,3,4,2],[5,1,2,3,0,4],[5,1,2,3,4,0],[5,1,4,3,0,2],[5,1,4,3,2,0],[5,2,0,3,1,4],[5,2,0,3,4,1],[5,2,1,3,0,4],[5,2,1,3,4,0],[5,2,4,3,0,1],[5,2,4,3,1,0],[5,4,0,3,1,2],[5,4,0,3,2,1],[5,4,1,3,0,2],[5,4,1,3,2,0],[5,4,2,3,0,1],[5,4,2,3,1,0]]
def F11C : List CutSpec := [⟨0,18,4,1,0,[3,0,4,1,2,5],0xcccc0000cccc0000#64⟩,⟨0,4,7,5,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,20,4,1,0,[3,4,0,1,2,5],0xf0f00000f0f00000#64⟩,⟨0,3,4,1,0,[0,1,3,2,4,5],0x8888888888888888#64⟩,⟨0,2,7,5,0,[1,0,2,3,4,5],0xcccccccccccccccc#64⟩,⟨0,32,7,5,0,[1,2,4,0,5,3],0xffffffff00000000#64⟩,⟨0,16,7,5,0,[1,2,4,0,3,5],0xffff0000ffff0000#64⟩,⟨0,5,4,1,0,[0,3,1,2,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨0,6,4,1,0,[3,0,1,2,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨0,17,4,1,0,[0,3,4,1,2,5],0xaaaa0000aaaa0000#64⟩,⟨0,1,7,5,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F11T3 : BTree NodeData := nd (lf2 0x10c210801007806 0x19053 [0x1]) (nd (lf2 0xc8310801006c06 0xa1254 []) (lf2 0x990310801006246 0x9d283 []))
def F11T4 : BTree NodeData := nd (nd (nd (nd (lf2 0x10c210801003d05 0x53 []) (lf2 0x10c210801002d85 0x85 [0x2])) (nd (lf2 0x14c210801003d05 0x343 []) (nd (lf2 0x14c210801003985 0x64 [0x1]) (lf2 0x14c210801003985 0x264 [])))) (nd (nd (lf2 0x14c210801002d85 0x284 []) (lf2 0x94c210801003985 0x264 [])) (nd (lf2 0x94c210801002d85 0x284 []) (nd (lf2 0xc8310801003d05 0x54 [0x3]) (lf2 0xc8310801003d05 0x254 [0x4]))))) (nd (nd (nd (lf2 0x108310801003e05 0x43 []) (lf2 0x990310801002b45 0x283 [0x5])) (nd (lf2 0x9903108010032c5 0x274 []) (nd (lf2 0xd0c530801002d25 0x282 []) (lf2 0x1d8540c810021e5 0x280 [])))) (nd (nd (lf2 0x9ca540c810030b5 0x264 []) (nd (lf2 0x9c0650c810031c5 0x271 []) (lf2 0x9c0650c810030e5 0x174 []))) (nd (lf2 0x1933214810021b5 0x187 []) (nd (lf2 0x58c631481002875 0x84 [0xb06]) (lf2 0x9d2631481003075 0x243 [0x706])))))
def F11M4 : BST := BN 267723747 98 (BN 200782798 24 (BN 199393116 420 (BL 187155387 128) BE) (BL 217755868 396)) (BN 279724706 134 (BN 275622864 0 (BL 269887138 410) BE) (BL 349729966 384))
def F11T5_0 := nd (nd (nd (nd (lf 0x10c210801001f84 [0x80207070805,0x900080004]) (nd (lf 0x14c210801001d84 [0x100040902,0xa]) (lf 0x14c210801001f84 [0x109020004,0xa]))) (nd (lf 0x94c210801001d84 [0x807070004,0x9]) (nd (lf 0xc8310801001f04 [0x300080004,0x1]) (lf 0x108310801001f84 [])))) (nd (nd (lf 0x1c8310801001f84 [0x10009040b]) (nd (lf 0x150310801001dc4 []) (lf 0x950310801001dc4 []))) (nd (lf 0x190310801001bc4 [0x1]) (nd (lf 0x990310801001bc4 [0x8]) (lf 0x1d44308010015e4 [0x2]))))) (nd (nd (nd (lf 0xc8530801001da4 [0x2]) (nd (lf 0x9c8530801001da4 [0x20004000a]) (lf 0xd0c530801001d64 []))) (nd (lf 0x1905308010019e4 [0x1]) (nd (lf 0x9905308010019e4 []) (lf 0x9d05308010015e4 [0xd02])))) (nd (nd (lf 0x9c85308010017a4 [0x2000a]) (nd (lf 0xca530801001da4 [0x307]) (lf 0x9925308010019e4 []))) (nd (nd (lf 0x9d25308010015e4 [0x2]) (lf 0x184600c81001bc4 [0x60b0d020a05])) (nd (lf 0x1d8540c810011f4 []) (lf 0x9d8540c810011f4 [0xd02])))))
def F11T5_1 := nd (nd (nd (nd (lf 0x9ca540c810015b4 [0x7]) (nd (lf 0x992540c810018f4 []) (lf 0x9da540c810011f4 []))) (nd (lf 0x9c0650c810019e4 [0x5]) (nd (lf 0x5d0650c810018f4 []) (lf 0x9d0650c810010f4 [])))) (nd (nd (lf 0x9d0650c810018f4 [0x6]) (nd (lf 0x9d0650c810011f4 []) (lf 0x9c8650c810015b4 [0x2]))) (nd (nd (lf 0x9d0650c810014f4 [0xd02]) (lf 0x9c2650c810013e4 [0x5])) (nd (lf 0x9d6650c810011f4 [0x6]) (lf 0x1933214810019b4 [0x7]))))) (nd (nd (nd (lf 0x9933214810019b4 []) (nd (lf 0x9d33214810015b4 []) (lf 0x5db3214810015b4 [0x80009]))) (nd (lf 0x9c06314810015e4 [0x5]) (nd (lf 0x58c631481001974 [0x307]) (lf 0x9d06314810014f4 [])))) (nd (nd (lf 0x8ca631481001974 [0x2]) (nd (lf 0x9d26314810011f4 []) (lf 0xd8e631481001974 [0x307]))) (nd (nd (lf 0xd4e631481001974 []) (lf 0x8ca639481001974 [0x2])) (nd (lf 0xd0e639481001974 []) (lf 0x9d26394810011f4 [])))))
def F11T5 : BTree NodeData := nd F11T5_0 F11T5_1
def F11M5 : BST := BN 299651975 3480 (BN 247781912 1408 (BN 220290996 3615 (BN 213375966 676 (BN 208261294 3596 (BN 184974237 3736 (BL 180205894 3784) BE) (BL 209464660 3840)) (BN 217657016 3614 (BN 217180737 1304 (BL 215188062 896) BE) (BL 217832111 768))) (BN 239173521 670 (BN 236885135 1692 (BN 231738718 652 (BL 221702389 1188) BE) (BL 237782830 512)) (BN 245961449 1159 (BN 240065141 1164 (BL 239885664 3760) BE) (BL 247252776 0)))) (BN 280462030 1539 (BN 258535840 1414 (BN 252258325 1560 (BN 251505900 1420 (BL 249148066 3608) BE) (BL 253410748 386)) (BN 274241073 30 (BN 273882919 12 (BL 271714486 1280) BE) (BL 274771194 3876))) (BN 289857752 1561 (BN 283520239 646 (BN 281665396 1792 (BL 281575924 3598) BE) (BL 286265439 270)) (BN 295214971 3900 (BN 295131062 3591 (BL 290642906 6) BE) (BL 295757968 384))))) (BN 327098391 1536 (BN 306718936 446 (BN 303582595 1852 (BN 302210987 1541 (BN 300119653 444 (BL 299957593 3808) BE) (BL 303375963 3528)) (BN 304885989 1038 (BN 304408564 3456 (BL 303681815 3584) BE) (BL 304992500 1545))) (BN 321310427 1664 (BN 310405903 3504 (BN 308371330 256 (BL 307336783 1828) BE) (BL 316283946 128)) (BN 324928780 3968 (BN 322863057 46 (BL 322477756 3846) BE) (BL 326991880 1024)))) (BN 357572012 1834 (BN 345894332 1798 (BN 333910403 1054 (BN 331900625 20 (BL 330670112 3638) BE) (BL 338049482 31)) (BN 354086688 1585 (BN 348660612 1 (BL 346190161 1552) BE) (BL 355121218 1044))) (BN 387091993 1811 (BN 372397894 640 (BN 371204761 1668 (BL 370665166 1036) BE) (BL 379179208 3712)) (BN 412889548 7 (BN 396462721 1030 (BL 392483016 1152) BE) (BL 428380059 1632)))))
def F11T6 : BTree NodeData := nd (nd (nd (nd (lf 0x210801000f83 [0x40b00080004,0x907060707,0x205]) (lf 0x310801000fc3 [0x50203070004,0x10008])) (nd (lf 0x430801000fe3 [0x800040405,0x3070402]) (nd (lf 0x530801000de3 [0x4000a0502,0x1]) (lf 0x530801000fe3 [0xa05020004,0x1])))) (nd (nd (lf 0x2530801000de3 [0x30705020004,0x8]) (nd (lf 0x600c81000fe3 [0x3000a0605,0x80502]) (lf 0x540c81000df3 [0x405040b0003,0x5060502]))) (nd (lf 0x2540c81000df3 [0x50200030004,0x506]) (nd (lf 0x650c810009f3 [0x605060b0006,0x5070502]) (lf 0x650c81000df3 [0x402060502]))))) (nd (nd (nd (lf 0x2650c81000bf3 [0x605]) (lf 0x321481000df3 [0x403020007])) (nd (lf 0x3321481000db3 [0x102]) (nd (lf 0x631481000df3 [0x70306]) (lf 0x26314810009f3 [0x60b07060307,0x40605])))) (nd (nd (lf 0x2631481000df3 [0x800090307,0x4]) (nd (lf 0x3321481000fb3 [0x102]) (lf 0x531481000df3 [0x60505070302]))) (nd (lf 0x2631481000bf3 [0x60501070009,0x8]) (nd (lf 0x329481000df3 [0x102]) (lf 0x26394810009f3 [0x603070004])))))
def F11M6 : BST := BN 350201994 1054 (BN 309227121 2688 (BN 289458775 2048 (BN 259796106 7936 (BN 248642810 7730 (BN 243796175 7452 (BN 241873570 6657 (BL 235685239 3620) BE) (BL 243877595 3358)) (BN 254047991 3596 (BL 251078535 1025) (BL 257491446 1024))) (BN 275720021 130 (BN 267352884 2062 (BL 261482794 3614) (BL 273840899 2561)) (BN 285152397 7708 (BL 284830149 1820) (BL 288399408 1792)))) (BN 304562132 8064 (BN 296812917 7476 (BN 295122720 6414 (BL 294890312 3591) (BL 295471903 6786)) (BN 302137848 6656 (BL 299957593 7296) (BL 302501843 6784))) (BN 307051350 2060 (BN 305143974 1920 (BL 304626146 3334) (BL 305829512 3590)) (BN 308254716 3072 (BL 307885975 1572) (BL 308350127 6400))))) (BN 329131571 7756 (BN 318067241 128 (BN 314749253 6275 (BN 312668141 2079 (BN 309740818 2176 (BL 309557882 1055) BE) (BL 313322780 282)) (BN 316447072 2078 (BL 316078331 1305) (BL 317820073 2575))) (BN 326248727 1548 (BN 323279271 2049 (BL 318311920 3840) (BL 325431727 1480)) (BN 328809323 131 (BL 326857641 1543) (BL 329048255 1030)))) (BN 342305016 1664 (BN 333683530 1566 (BN 331685532 258 (BL 331106568 7754) (BL 332848905 2054)) (BN 338169139 7732 (BL 336505877 5844) (BL 342281783 6912))) (BN 347067495 6272 (BN 345181044 2330 (BL 344209752 256) (BL 346974268 5948)) (BN 348872708 2354 (BL 347436858 538) (BL 349398773 548)))))) (BN 378115801 7428 (BN 367062550 2944 (BN 362413569 7218 (BN 359632056 7196 (BN 358178169 7939 (BN 357591129 5888 (BL 352775300 1651) BE) (BL 358721905 7194)) (BN 361210203 2573 (BL 360965040 1432) (BL 361812868 1645))) (BN 364962401 1176 (BN 364091631 1031 (BL 363543796 2306) (BL 364404831 2304)) (BN 365721629 1408 (BL 365698359 3335) (BL 366333559 794)))) (BN 373234413 6150 (BN 368686389 1224 (BN 367748086 3456 (BL 367444382 3610) (BL 367759473 7168)) (BN 371337570 3712 (BL 369718990 1152) (BL 371718968 1456))) (BN 375196328 542 (BN 374338584 2560 (BL 374249112 3328) (BL 374676281 5784)) (BN 376826882 1281 (BL 375716329 1200) (BL 378030248 1542))))) (BN 411522141 7552 (BN 397559177 7680 (BN 387508207 2055 (BN 384519460 0 (BL 378938627 7424) (BL 384696311 770)) (BN 391270978 385 (BL 390309178 1378) (BL 392501953 270))) (BN 400009971 1562 (BN 399947447 1586 (BL 397665688 1280) (BL 399982266 512)) (BN 403307765 6175 (BL 400069947 562) (BL 407086696 6174)))) (BN 422175838 6144 (BN 419149775 1796 (BN 415150944 3584 (BL 412648798 7220) (BL 415519502 640)) (BN 419472023 7684 (BL 419227909 2581) (BL 421589053 3200))) (BN 440115770 5760 (BN 427893715 6151 (BL 424814647 768) (BL 438567520 1536)) (BN 467030018 7686 (BL 455996334 6145) (BL 483456845 2579))))))
def F11T7 : BTree NodeData := nd (nd (lf 0x8010007e2 [0x802050102,0x30603070004]) (lf 0xc810007f2 [0x20b01020205,0x300040107,0x1060206])) (nd (lf 0x14810005f2 [0x307020b0009,0x400080306]) (nd (lf 0x14810007f2 [0x30700090004,0x802050306,0x20b]) (lf 0x94810005f2 [0x30701020004,0x306])))
def F11M7 : BST := BN 400927904 1024 (BN 352838047 1036 (BN 332050091 768 (BN 302436857 647 (BN 281155036 1564 (BN 264459130 1793 (BL 258129877 3969) BE) (BN 295173145 284 (BL 293573463 1610) BE)) (BN 328561642 646 (BN 328058743 256 (BL 321645832 257) BE) (BL 329981348 3712))) (BN 342667651 1566 (BN 334475295 1060 (BN 334250715 1025 (BL 334171778 1588) BE) (BL 339279064 188)) (BN 349868591 0 (BN 347832225 1562 (BL 344654974 540) BE) (BL 351523889 1586)))) (BN 384198214 1159 (BN 366194977 1538 (BN 360272850 1054 (BN 360026072 1536 (BL 354953926 3713) BE) (BL 361850334 282)) (BN 376023678 1665 (BN 371337570 1792 (BL 371015322 3968) BE) (BL 380213086 258))) (BN 392335521 1153 (BN 388634148 600 (BN 387267457 1031 (BL 385015074 1304) BE) (BL 390130107 128)) (BN 397671716 576 (BN 397176193 3906 (BL 393846568 1537) BE) (BL 399615552 262))))) (BN 450875403 1158 (BN 426168026 3388 (BN 413684993 3840 (BN 404250827 3328 (BN 403416202 1542 (BL 401991078 3331) BE) (BN 409687632 1152 (BL 404619568 1030) BE)) (BN 416009187 771 (BN 415474662 1540 (BL 413872099 3612) BE) (BL 417800402 828))) (BN 439647456 3456 (BN 429492771 260 (BN 428629839 641 (BL 426290526 1364) BE) (BL 434658928 263)) (BN 443801710 3590 (BN 441612169 640 (BL 441545896 384) BE) (BL 445763625 1280)))) (BN 484240952 1340 (BN 466888841 1346 (BN 462698411 896 (BN 458075504 1543 (BL 455086757 512) BE) (BL 466518474 385)) (BN 480549288 3610 (BN 478974600 516 (BL 473467952 3457) BE) (BL 482902118 1664))) (BN 504054633 3900 (BN 498461012 3591 (BN 492743135 3584 (BL 487670989 897) BE) (BL 498912040 3586)) (BN 561346902 1409 (BN 548191725 3588 (BL 526563631 3585) BE) (BL 574329232 1408)))))
def F11T8 : BTree NodeData := lf 0x10003f1 [0x102000b0005,0x401060107]
def F11M8 : BST := BN 387347492 2 (BN 361903404 132 (BN 302307551 28 (BN 296115579 898 (BL 289702668 900) BE) (BL 328082908 130)) (BN 376089170 24 (BN 368984740 26 (BL 367340209 128) BE) (BL 381358318 896))) (BN 436627177 4 (BN 423143593 259 (BN 420435888 0 (BL 413488036 257) BE) (BL 430840147 256)) (BN 494620467 388 (BL 460799971 386) (BL 500057272 384)))
def F11T9 : BTree NodeData := lf 0x1f0 [0x2000b0005,0x60007]
def F11M9 : BST := BN 298123084 60 (BN 280770973 66 (BN 272633666 42 (BL 263072773 12) BE) (BN 296161169 6 (BL 290426530 90) BE)) (BN 346415285 30 (BN 339310855 36 (BL 312352458 18) BE) (BL 388492724 0))
def F11L : Nat → Option (BTree NodeData) | 3 => some F11T3 | 4 => some F11T4 | 5 => some F11T5 | 6 => some F11T6 | 7 => some F11T7 | 8 => some F11T8 | 9 => some F11T9 | _ => none
def F11M : Nat → BST | 4 => F11M4 | 5 => F11M5 | 6 => F11M6 | 7 => F11M7 | 8 => F11M8 | 9 => F11M9 | _ => BE
end CertData
noncomputable section CertVerify
abbrev ok (f : Forest) (k : Nat) (t : BTree NodeData) := t.all (fastNodeOK f k) = true
def base0 (_ : Nat) : List Sig × Sig × Nat := ([], 0, 0)
private theorem base0_s : ∀ k, k ≠ 0 → LowerBV (base0 k).1 (base0 k).2.1 (base0 k).2.2 := fun _ _ _ _ _ _ => Nat.zero_le _
def fF1 : Forest := ⟨56,tF1,3,F1P,F1N,F1R,F1A,F1C,F1L,F1M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F1v : graphValid fF1 base0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F1k3 : ok fF1 3 F1T3 := by decide +kernel
private theorem F1lv : levelsChecked fF1 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fF1,F1L] at ht
  subst ht; exact F1k3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF1 : LowerBV (rawOf 56) tF1 4 :=
  lower_forest fF1 base0 base0_s F1v F1lv (by decide +kernel)
def base1 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | _ => ([],0,0)
private theorem base1_s : ∀ k, k ≠ 0 → LowerBV (base1 k).1 (base1 k).2.1 (base1 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 0 | _ + 2 => exact fun _ _ _ _ => Nat.zero_le _
def fF2 : Forest := ⟨60,tF2,6,F2P,F2N,F2R,F2A,F2C,F2L,F2M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F2v : graphValid fF2 base1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F2k3 : ok fF2 3 F2T3 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F2k4 : ok fF2 4 F2T4 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F2k5 : ok fF2 5 F2T5 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F2k6 : ok fF2 6 F2T6 := by decide +kernel
private theorem F2lv : levelsChecked fF2 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF2,F2L] at ht
  · subst ht; exact F2k3
  · subst ht; exact F2k4
  · subst ht; exact F2k5
  · subst ht; exact F2k6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF2 : LowerBV (rawOf 60) tF2 7 :=
  lower_forest fF2 base1 base1_s F2v F2lv (by decide +kernel)
def base2 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | _ => ([],0,0)
private theorem base2_s : ∀ k, k ≠ 0 → LowerBV (base2 k).1 (base2 k).2.1 (base2 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 0 | _ + 3 => exact fun _ _ _ _ => Nat.zero_le _
def fF3 : Forest := ⟨46,tF3,4,F3P,F3N,F3R,F3A,F3C,F3L,F3M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F3v : graphValid fF3 base2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F3k4 : ok fF3 4 F3T4 := by decide +kernel
private theorem F3lv : levelsChecked fF3 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF3,F3L] at ht
  subst ht; exact F3k4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF3 : LowerBV (rawOf 46) tF3 5 :=
  lower_forest fF3 base2 base2_s F3v F3lv (by decide +kernel)
def base3 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | _ => ([],0,0)
private theorem base3_s : ∀ k, k ≠ 0 → LowerBV (base3 k).1 (base3 k).2.1 (base3 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 0 | _ + 4 => exact fun _ _ _ _ => Nat.zero_le _
def fF4 : Forest := ⟨60,tF4,4,F4P,F4N,F4R,F4A,F4C,F4L,F4M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F4v : graphValid fF4 base3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F4k4 : ok fF4 4 F4T4 := by decide +kernel
private theorem F4lv : levelsChecked fF4 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF4,F4L] at ht
  subst ht; exact F4k4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF4 : LowerBV (rawOf 60) tF4 5 :=
  lower_forest fF4 base3 base3_s F4v F4lv (by decide +kernel)
def base4 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | _ => ([],0,0)
private theorem base4_s : ∀ k, k ≠ 0 → LowerBV (base4 k).1 (base4 k).2.1 (base4 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 0 | _ + 5 => exact fun _ _ _ _ => Nat.zero_le _
def fF5 : Forest := ⟨54,tF5,6,F5P,F5N,F5R,F5A,F5C,F5L,F5M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F5v : graphValid fF5 base4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F5k3 : ok fF5 3 F5T3 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F5k4 : ok fF5 4 F5T4 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F5k5 : ok fF5 5 F5T5 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F5k6 : ok fF5 6 F5T6 := by decide +kernel
private theorem F5lv : levelsChecked fF5 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF5,F5L] at ht
  · subst ht; exact F5k3
  · subst ht; exact F5k4
  · subst ht; exact F5k5
  · subst ht; exact F5k6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF5 : LowerBV (rawOf 54) tF5 7 :=
  lower_forest fF5 base4 base4_s F5v F5lv (by decide +kernel)
def base5 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | _ => ([],0,0)
private theorem base5_s : ∀ k, k ≠ 0 → LowerBV (base5 k).1 (base5 k).2.1 (base5 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 0 | _ + 6 => exact fun _ _ _ _ => Nat.zero_le _
def fF6 : Forest := ⟨46,tF6,4,F6P,F6N,F6R,F6A,F6C,F6L,F6M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F6v : graphValid fF6 base5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F6k4 : ok fF6 4 F6T4 := by decide +kernel
private theorem F6lv : levelsChecked fF6 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF6,F6L] at ht
  subst ht; exact F6k4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF6 : LowerBV (rawOf 46) tF6 5 :=
  lower_forest fF6 base5 base5_s F6v F6lv (by decide +kernel)
def base6 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | _ => ([],0,0)
private theorem base6_s : ∀ k, k ≠ 0 → LowerBV (base6 k).1 (base6 k).2.1 (base6 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 0 | _ + 7 => exact fun _ _ _ _ => Nat.zero_le _
def fF7 : Forest := ⟨39,tF7,5,F7P,F7N,F7R,F7A,F7C,F7L,F7M⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F7v : graphValid fF7 base6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F7k2 : ok fF7 2 F7T2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F7k3 : ok fF7 3 F7T3 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F7k4 : ok fF7 4 F7T4 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem F7k5 : ok fF7 5 F7T5 := by decide +kernel
private theorem F7lv : levelsChecked fF7 := by
  intro k hk tree ht; change k ≤ 5 at hk; interval_cases k
  all_goals simp [fF7,F7L] at ht
  · subst ht; exact F7k2
  · subst ht; exact F7k3
  · subst ht; exact F7k4
  · subst ht; exact F7k5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowF7 : LowerBV (rawOf 39) tF7 6 :=
  lower_forest fF7 base6 base6_s F7v F7lv (by decide +kernel)
end CertVerify
end PEqualNP.Outside.L_meta_13287.Certificate

namespace PEqualNP.Outside.L_meta_13287.Certificate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def tRt : Sig := 0xeaa8c888e0a0c000#64
def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3936929928 * 2 ^ 32 + 3768631296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sliceRows (r : Row) : Row := ⟨48 + r.val / 32 + 2 * (r.val % 8), by omega⟩

set_option maxRecDepth 8192 in
theorem lowRt : LowerBV (rawOf 63) tRt 8 := by
  have h := lowerBV_slice (roots := rawOf 63) (other := rawOf 39) (T := tRt) (G := tF7)
    (proper_of (by decide)) (by decide) (by decide) (proper_of (by decide)) sliceRows
    (by funext r; exact (by decide : ∀ j : Row, bitBV (sliceRows j) tRt = bitBV j tF7) r)
    (by
      intro a ha
      rw [← observe6_rename]
      apply freeWord6_sound
      exact (List.all_eq_true.mp (by decide : (rawOf 63).all (fun w => freeWord6 (rawOf 39) (rename6 sliceRows w)) = true)) a ha)
    {x4,x5}
    (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · refine ⟨5,21,by decide,?_⟩
        intro v hv hne
        change v ∈ [x0,x1,x2,x3,x4,x5] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | contradiction
      · refine ⟨3,35,by decide,?_⟩
        intro v hv hne
        change v ∈ [x0,x1,x2,x3,x4,x5] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | contradiction)
    (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · refine ⟨true, ?_⟩
        funext r
        exact (by decide : ∀ j : Row, bitBV (sliceRows j) x4 = true) r
      · refine ⟨true, ?_⟩
        funext r
        exact (by decide : ∀ j : Row, bitBV (sliceRows j) x5 = true) r)
    6 lowF7
  simpa [show x4 ≠ x5 by decide] using h

def sample6 (r : Row) (i : Fin 6) : Bool := bitBV r ((rawOf 63).getD i.val zeroBV)

private theorem raw63_list : List.ofFn (fun i : Fin 6 => (rawOf 63).getD i.val zeroBV) = rawOf 63 := rfl

private theorem sample6_eq (r : Row) :
    List.ofFn (sample6 r) = ((rawOf 63).map observeBV).map (fun f => f r) := by
  rw [← raw63_list, List.map_map, List.map_ofFn]; rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sample6_target : ∀ r : Row, targetFun (sample6 r) = bitBV r tRt := by
  decide +kernel

private theorem fanInTwo_ops {C : Circuit} (h : FanInTwo C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ho, hl⟩ := h g hg
  refine ⟨?_, hl⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho


theorem binaryLower (C : Circuit) (hFanIn : FanInTwo C)
    (hEval : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x) :
    8 ≤ C.gates.countP (fun q => !isNot q) := by
  have hfit := fanInTwo_ops hFanIn
  obtain ⟨q, bank, hq, hreach, hsup⟩ := circuit_reach ((rawOf 63).map observeBV) C.gates ((rawOf 63).map observeBV)
    0 ((rawOf 63).map observeBV) hfit Reach.start (fun a ha => Or.inl ha)
  have hout : (execWires C.gates ((rawOf 63).map observeBV)).getD C.output (fun _ => false) = observeBV tRt := by
    funext r
    have hev := execWires_at C.gates ((rawOf 63).map observeBV) r
    have hr1 : ((execWires C.gates ((rawOf 63).map observeBV)).getD C.output (fun _ => false)) r =
        ((execWires C.gates ((rawOf 63).map observeBV)).map (fun f => f r)).getD C.output false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (execWires C.gates ((rawOf 63).map observeBV))[C.output]? <;> rfl
    rw [hr1, hev, ← sample6_eq r]
    exact (hEval (sample6 r)).trans (sample6_target r)
  have havail : Available bank (observeBV tRt) := hout ▸ avail_getD hsup C.output
  have h11 := lowRt q bank hreach havail
  omega

end PEqualNP.Outside.L_meta_13287.Certificate


namespace PEqualNP.Outside.L_meta_13287.Witness
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem mono : Monotone2 circuit := by simp [Monotone2, circuit]

theorem values : ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) =
    Nat.testBit (3936929928 * 2 ^ 32 + 3768631296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_13287.Witness

open PEqualNP.Outside.L_meta_13287 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_13287 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936929928 * 2 ^ 32 + 3768631296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936929928 * 2 ^ 32 + 3768631296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, legal, bound, computes⟩
  by_cases hNot : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hg, he⟩ := hNot
    have hsmall : C.gates.countP (fun q => !Certificate.isNot q) < C.gates.length :=
      List.countP_lt_length_iff.mpr ⟨g, hg, by simp [Certificate.isNot, he]⟩
    have hlarge := Certificate.binaryLower C legal computes
    refine ⟨Witness.circuit, Witness.mono, ?_, Witness.values⟩
    change 9 ≤ s
    change C.gates.length ≤ s at bound
    omega
  · refine ⟨C, ?_, bound, computes⟩
    intro g hg
    obtain ⟨hop, cap⟩ := legal g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun e => (hNot ⟨g, hg, e⟩).elim)), cap⟩
