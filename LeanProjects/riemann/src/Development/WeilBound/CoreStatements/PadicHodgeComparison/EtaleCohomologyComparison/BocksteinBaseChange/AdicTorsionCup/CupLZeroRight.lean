import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.HeqOfEqCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable (l : ℕ) [Fact l.Prime]

theorem castH_apply {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) :
    castH h1 h2 x = x.cast h1 h2 := rfl

section Cup
variable {E : Spc} {n m i j n' i' : ℤ} (hI : ZIn) (h1 : n + m = n') (h2 : i + j = i')

def cupL (x : Hl l E n i) (y : Hl l E m j) : Hl l E n' i' := ⟨_, cup_mem l hI E h1 h2 x y⟩

theorem cupL_apply (x : Hl l E n i) (y : Hl l E m j) (k : ℕ) :
    (cupL l hI h1 h2 x y).1 k = (cup (l ^ k) (x.1 k) (y.1 k)).cast h1 h2 := rfl

theorem pull_cupL {E' : Spc} (f : E' ⟶ E) (x : Hl l E n i) (y : Hl l E m j) :
    pullHl l f n' i' (cupL l hI h1 h2 x y) = cupL l hI h1 h2 (pullHl l f n i x) (pullHl l f m j y) := by
  apply Subtype.ext
  funext k
  have := neZero_pow l k
  change pull _ f _ n' ((cup _ _ _).cast h1 h2) = (cup _ (pull _ f _ n _) (pull _ f _ m _)).cast h1 h2
  rw [pull_cast, (hI.nat (l ^ k)).1 f]

theorem cupL_zero_right (x : Hl l E n i) : cupL l hI h1 h2 x (0 : Hl l E m j) = 0 := by
  apply Subtype.ext
  funext k
  change (cup _ _ 0).cast h1 h2 = 0
  rw [map_zero, cast_zero]

theorem cupL_add_left (x x' : Hl l E n i) (y : Hl l E m j) :
    cupL l hI h1 h2 (x + x') y = cupL l hI h1 h2 x y + cupL l hI h1 h2 x' y := by
  apply Subtype.ext
  funext k
  change (cup _ (x.1 k + x'.1 k) (y.1 k)).cast h1 h2 = (cup _ _ _).cast h1 h2 + (cup _ _ _).cast h1 h2
  rw [map_add, AddMonoidHom.add_apply, cast_add]

theorem cupL_smul_left (r : ℤ_[l]) (x : Hl l E n i) (y : Hl l E m j) :
    cupL l hI h1 h2 (r • x) y = r • cupL l hI h1 h2 x y := by
  apply Subtype.ext
  funext k
  change (cup _ (r • x.1 k) (y.1 k)).cast h1 h2 = r • (show HtL l k E n' i' from (cup _ (x.1 k) (y.1 k)).cast h1 h2)
  rw [HtL.smul_eq l k k le_rfl E n i r (x.1 k), HtL.smul_eq l k k le_rfl E n' i' r]
  erw [map_nsmul, AddMonoidHom.nsmul_apply, cast_nsmul]

def cupR (y : Hl l E m j) : Hl l E n i →ₗ[ℤ_[l]] Hl l E n' i' where
  toFun x := cupL l hI h1 h2 x y
  map_add' x x' := cupL_add_left l hI h1 h2 x x' y
  map_smul' r x := cupL_smul_left l hI h1 h2 r x y

end Cup

section Sum
variable (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
include hI hj

theorem sum_eq (x x' : Hl l (sch.obj X) n i) (h : ∀ s, pullHl l (sch.map (j s)) n i x = pullHl l (sch.map (j s)) n i x') :
    x = x' :=
  sub_eq_zero.1 (sum_inj l hI j hj n i _ fun s => by rw [map_sub, h, sub_self])

def extS (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) : Hl l (sch.obj X) n i :=
  (sum_ext l hI j hj n i (Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y)).choose

theorem extS_spec (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) (t : Fin r) :
    pullHl l (sch.map (j t)) n i (extS l hI j hj n i s y) = Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y t :=
  (sum_ext l hI j hj n i (Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y)).choose_spec t

theorem extS_self (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) :
    pullHl l (sch.map (j s)) n i (extS l hI j hj n i s y) = y := by
  rw [extS_spec]; exact Pi.single_eq_same _ _

theorem extS_ne (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) {t : Fin r} (ht : t ≠ s) :
    pullHl l (sch.map (j t)) n i (extS l hI j hj n i s y) = 0 := by
  rw [extS_spec]; exact Pi.single_eq_of_ne ht _

theorem tors_of_restr (x : Hl l (sch.obj X) n i) (h : ∀ s, ∃ e : ℕ, (l : ℤ_[l]) ^ e • pullHl l (sch.map (j s)) n i x = 0) :
    ∃ e : ℕ, (l : ℤ_[l]) ^ e • x = 0 := by
  choose e he using h
  refine ⟨∑ s, e s, sum_inj l hI j hj n i _ fun s => ?_⟩
  rw [map_smul, ← Finset.add_sum_erase _ _ (Finset.mem_univ s), pow_add, mul_comm, mul_smul, he, smul_zero]

end Sum

theorem unitQ (k : ℕ) : IsUnit (((l ^ k : ℕ) : ℕ) : PadicAlgCl l) :=
  isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (pow_ne_zero k (Fact.out : l.Prime).ne_zero))

section Y
variable (hI : ZIn) {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of (PadicAlgCl l))) [IsProper p]
include hI p

theorem ysys (n i : ℤ) : Adic.IsSys l (fun k => HtL l k (sch.obj Y) n i) (fun m m' => red (l ^ m) (l ^ m') (sch.obj Y) n i) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine isSys l hI Y (AdicGeo.unit_of_over p l) n i fun k => ?_
  have := neZero_pow l k
  exact hI.e4 (l ^ k) (PadicAlgCl l) (unitQ l k) p n i

variable [IsIntegral Y] (d : ℕ) [SmoothOfRelativeDimension d p]

theorem hl_vanish (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Hl l (sch.obj Y) n 0) := by
  refine ⟨fun x y => Subtype.ext (funext fun k => ?_)⟩
  have := neZero_pow l k
  exact (vanish p d (l ^ k) (unitQ l k) hI n hn).elim _ _

theorem hl_cyclic (N : ℤ) (hN : N = 2 * d) : ∃ g : Hl l (sch.obj Y) N 0, ∀ x, ∃ c : ℤ_[l], x = c • g := by
  subst hN
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have := neZero_pow l 1
  obtain ⟨g, hg, hc⟩ := (ysys l hI p _ 0).cyclic (S := HlSub l (sch.obj Y) _ 0) (fun _ => Iff.rfl)
    (top_cyclic p d (l ^ 1) (unitQ l 1) hI (AdicGeo.prim_of_over p _) (AdicGeo.inv_sch _ (AdicGeo.unit_of_over p _)))
  refine ⟨⟨g, hg⟩, fun x => ?_⟩
  obtain ⟨c, e⟩ := hc x.1 x.2
  exact ⟨c, Subtype.ext e⟩

theorem hl_nondeg (i j N : ℤ) (hij : i + j = N) (hN : N = 2 * d) (x : Hl l (sch.obj Y) i 0)
    (h : ∀ y : Hl l (sch.obj Y) j 0, ∃ e : ℕ, (l : ℤ_[l]) ^ e • cupL l hI hij (add_zero 0) x y = 0) :
    ∃ e : ℕ, (l : ℤ_[l]) ^ e • x = 0 := by
  obtain ⟨g, hg⟩ := hl_cyclic l hI p d N hN
  have hnd : ∀ k (a : HtL l k (sch.obj Y) i 0),
      (∀ b : HtL l k (sch.obj Y) j 0, ((cup (l ^ k)).compr₂ (castH hij (add_zero (0 : ℤ)))) a b = 0) → a = 0 := by
    intro k a hb
    have := neZero_pow l k
    exact nondeg p d (l ^ k) (unitQ l k) hI (AdicGeo.prim_of_over p _) (AdicGeo.inv_sch _ (AdicGeo.unit_of_over p _))
      i j (hij.trans hN) a fun b => (cast_eq_zero _ _ _).1 (by simpa only [AddMonoidHom.compr₂_apply, castH_apply] using hb b)
  obtain ⟨e, he⟩ := Adic.pair_tors (ysys l hI p i 0) (ysys l hI p j 0) (ysys l hI p N 0)
    (SA := HlSub l (sch.obj Y) i 0) (SB := HlSub l (sch.obj Y) j 0) (SC := HlSub l (sch.obj Y) N 0)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (fun k => (cup (l ^ k)).compr₂ (castH hij (add_zero (0 : ℤ))))
    (fun m n a b hmn => by
      have := neZero_pow l m
      simp only [AddMonoidHom.compr₂_apply]
      show red (l ^ m) (l ^ n) (sch.obj Y) N 0 (Ht.cast hij (add_zero 0) (cup (l ^ m) a b)) =
        Ht.cast hij (add_zero 0) (cup (l ^ n) (red (l ^ m) (l ^ n) _ i 0 a) (red (l ^ m) (l ^ n) _ j 0 b))
      rw [red_cast, (hI.a11 (l ^ m) (l ^ n) (pow_dvd_pow l hmn) _).1])
    hnd ⟨g.1, g.2, fun z hz => by obtain ⟨c, e⟩ := hg ⟨z, hz⟩; exact ⟨c, congrArg Subtype.val e⟩⟩ x.2
    (fun y hy => by
      obtain ⟨e, he⟩ := h ⟨y, hy⟩
      exact ⟨e, congrArg Subtype.val he⟩)
  exact ⟨e, Subtype.ext he⟩

end Y

end CrystallineSemistableComparison.AdicCoh
