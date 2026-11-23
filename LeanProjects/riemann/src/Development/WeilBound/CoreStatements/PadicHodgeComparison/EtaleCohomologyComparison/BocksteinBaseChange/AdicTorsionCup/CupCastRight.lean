import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowNsmulEqZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_rfl {n i : ℤ} (x : Ht q E n i) : x.cast rfl rfl = x := rfl

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem cast_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') : (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

theorem cast_add {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    (x + y).cast h1 h2 = x.cast h1 h2 + y.cast h1 h2 := by
  subst h1 h2; rfl

theorem cast_smul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (c : ℤ) (x : Ht q E n i) :
    (c • x).cast h1 h2 = c • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cast_nsmul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (c : ℕ) (x : Ht q E n i) :
    (c • x).cast h1 h2 = c • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cast_eq_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) : x.cast h1 h2 = 0 ↔ x = 0 := by
  subst h1 h2; rfl

theorem cast_inj {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x y : Ht q E n i} : x.cast h1 h2 = y.cast h1 h2 ↔ x = y := by
  subst h1 h2; rfl

def castH {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') : Ht q E n i →+ Ht q E n' i' where
  toFun x := x.cast h1 h2
  map_zero' := cast_zero h1 h2
  map_add' := cast_add h1 h2

theorem red_cast (Q q' : ℕ) {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht Q E n i) :
    red Q q' E n' i' (x.cast h1 h2) = (red Q q' E n i x).cast h1 h2 := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (x.cast h1 h2) = Ht.cast h1 h2 (pull _ f (tw q i) n x) := by
  subst h1 h2; rfl

theorem cup_cast_left {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) (y : Ht q E m j) :
    cup q (x.cast h1 h2) y = (cup q x y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (x : Ht q E n i) (y : Ht q E m j) :
    cup q x (y.cast h1 h2) = (cup q x y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cast_heq {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) : HEq (x.cast h1 h2) x := by
  subst h1 h2; rfl

end Cast

variable (l : ℕ) [Fact l.Prime]

theorem neZero_pow (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem mem_hl {E : Spc} {n i : ℤ} (x : ∀ k, HtL l k E n i) :
    x ∈ HlSub l E n i ↔ ∀ k, red (l ^ (k + 1)) (l ^ k) E n i (x (k + 1)) = x k := Iff.rfl

theorem isSys (hI : ZIn) (X : Scheme.{0}) (hX : IsUnit (l : Γ(X, ⊤))) (n i : ℤ)
    (hfin : ∀ k, Finite (Ht (l ^ k) (sch.obj X) n i)) :
    Adic.IsSys l (fun k => HtL l k (sch.obj X) n i) (fun m m' => red (l ^ m) (l ^ m') (sch.obj X) n i) where
  smul k r x := HtL.smul_eq l k k le_rfl _ n i r x
  id m x := by
    have := neZero_pow l m
    exact (hI.a11 (l ^ m) (l ^ m) dvd_rfl (sch.obj X)).2.2.1 n i x
  trans m m' p x h1 h2 := by
    have := neZero_pow l m
    exact (hI.a11 (l ^ m) (l ^ m') (pow_dvd_pow l h2) (sch.obj X)).2.2.2 (l ^ p) (pow_dvd_pow l h1) n i x
  bock a b z h := hI.bock l a b X hX n i z h
  fin k := hfin k

theorem cup_mem (hI : ZIn) (E : Spc) {n m i j n' i' : ℤ} (h1 : n + m = n') (h2 : i + j = i') (x : Hl l E n i) (y : Hl l E m j) :
    (fun k => ((cup (l ^ k) (x.1 k) (y.1 k)).cast h1 h2 : HtL l k E n' i')) ∈ HlSub l E n' i' := by
  intro k
  have := neZero_pow l (k + 1)
  have h := (hI.a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) E).1 (x.1 (k + 1)) (y.1 (k + 1))
  change red _ _ _ _ _ ((cup _ _ _).cast _ _) = (cup _ _ _).cast _ _
  rw [red_cast, h, x.2 k, y.2 k]

variable {l} {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem cup_ex (hI : ZIn) (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) : ∃ z, M.CupT x y z :=
  ⟨⟨_, cup_mem l hI M.spc (by push_cast; rfl) (add_zero 0) x y⟩, fun _ => rfl⟩

variable (l)

theorem sum_inj (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
    (x : Hl l (sch.obj X) n i) (h : ∀ s, pullHl l (sch.map (j s)) n i x = 0) : x = 0 := by
  apply Subtype.ext
  funext k
  refine (hI.sum (ZMod (l ^ k)) (tw (l ^ k) i) j hj n).1 (funext fun s => ?_)
  change pull _ _ _ n (x.1 k) = pull _ _ _ n 0
  rw [map_zero]
  exact congrArg (fun z : Hl l (sch.obj (Y s)) n i => z.1 k) (h s)

theorem sum_ext (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
    (y : ∀ s, Hl l (sch.obj (Y s)) n i) : ∃ x : Hl l (sch.obj X) n i, ∀ s, pullHl l (sch.map (j s)) n i x = y s := by
  have hb := fun k : ℕ => hI.sum (ZMod (l ^ k)) (tw (l ^ k) i) j hj n
  let xk : ∀ k, HtL l k (sch.obj X) n i := fun k => ((hb k).2 (fun s => (y s).1 k)).choose
  have hxk : ∀ k s, pull _ (sch.map (j s)) _ n (xk k) = (y s).1 k := fun k s =>
    congrFun ((hb k).2 (fun s => (y s).1 k)).choose_spec s
  refine ⟨⟨xk, fun k => ?_⟩, fun s => Subtype.ext (funext fun k => hxk k s)⟩
  refine (hb k).1 (funext fun s => ?_)
  change pull _ _ _ n (red _ _ _ n i (xk (k + 1))) = pull _ _ _ n (xk k)
  rw [pull_red, hxk, hxk]
  exact (y s).2 k

end CrystallineSemistableComparison.AdicCoh
