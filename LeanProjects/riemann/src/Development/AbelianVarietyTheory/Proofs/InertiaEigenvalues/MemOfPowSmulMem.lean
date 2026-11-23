import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachModuleUniqueness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemOfLe

noncomputable section

namespace GlobalTheory.WachSat

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_pow_smul_le {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (c : O) (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L S : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (hS : S.FG) :
    ∃ m : ℕ, ∀ x ∈ S, c ^ m • x ∈ L := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_7 h_8 h_9 h_10; revert LL O h_2 h_3 h_4 h_5 V h_7 h_8 h_9 h_10 c hc L S hL hS; exact @_root_.GlobalTheory.PowerScalarMembership.main)
  | exact @_root_.GlobalTheory.PowerScalarMembership.main
  | exact _root_.GlobalTheory.PowerScalarMembership.main
  | (apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScalarMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScalarMembership.main ..)

variable (W : LocWach PD LL O v n)

theorem ee_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (x : W.EE)
    (hx : (PD.p : W.EE) * x = 0) : x = 0 := by
  have hA : ∀ a : LetA O n, (PD.p : LetA O n) * a = 0 → a = 0 := by
    intro a ha
    funext i
    ext k
    have h1 : (PD.p : PowerSeries O) * a i = 0 := congrFun ha i
    have h2 := congrArg (PowerSeries.coeff k) h1
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, map_zero] at h2
    simpa using hp _ h2
  haveI := W.EE_complete
  refine IsHausdorff.haus (I := Ideal.span {((PD.p : ℕ) : W.EE)}) inferInstance x fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨a, m, ha⟩ := W.EE_dense x k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b, hb⟩ := W.EE_sat ((PD.p : LetA O n) * a) (k + 1) (by
    refine Ideal.mem_span_singleton'.2 ⟨-y, ?_⟩
    rw [map_mul, map_natCast]
    linear_combination (-(PD.p : W.EE)) * hy - (algebraMap (LetA O n) W.EE (letπ ^ m)) * hx)
  have hab : a = (PD.p : LetA O n) ^ k * b := by
    have := hA (a - (PD.p : LetA O n) ^ k * b) (by rw [mul_sub, hb]; ring)
    exact sub_eq_zero.1 this
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ m)) := by
    rw [map_pow]; exact W.EE_π.pow m
  refine Ideal.mem_span_singleton'.2 ⟨(y + algebraMap (LetA O n) W.EE b) * ↑u⁻¹, ?_⟩
  rw [hab, map_mul, map_pow (algebraMap (LetA O n) W.EE) (PD.p : LetA O n), map_natCast, ← hu] at hy
  have huu : (u : W.EE) * ↑u⁻¹ = 1 := u.mul_inv
  linear_combination (↑u⁻¹ : W.EE) * hy + x * huu

theorem mem_of_pow_smul_mem (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O)
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T) (m : ℕ) (x : W.DD T)
    (hx : ((PD.p : O) ^ m) • x ∈ W.N T) : x ∈ W.N T := by
  obtain ⟨b, hli, hsp⟩ := hb
  have hxs : x ∈ Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) := hsp ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hxs
  set a := b.repr ⟨_, hx⟩ with ha
  have h1 : ∑ j, algebraMap (LetA O n) W.EE (a j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hx⟩)
    rw [map_sum] at this
    simpa only [algebraMap_smul, map_smul, Submodule.subtype_apply] using this
  have h2 : ∑ j, ((PD.p : W.EE) ^ m * e j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    rw [← he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, ← algebraMap_smul W.EE ((PD.p : O) ^ m), map_pow, map_natCast]
  have h3 : ∀ j, algebraMap (LetA O n) W.EE (a j) = (PD.p : W.EE) ^ m * e j :=
    Fintype.linearIndependent_iffₛ.1 hli _ _ (h1.trans h2.symm)
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (ee_torsionFree W hp _ (by rw [← hy]; ring))
  have h4 : ∀ j, ∃ c : LetA O n, e j = algebraMap (LetA O n) W.EE c := by
    intro j
    obtain ⟨c, hc⟩ := W.EE_sat (a j) m (Ideal.mem_span_singleton'.2 ⟨e j, by rw [h3, mul_comm]⟩)
    refine ⟨c, sub_eq_zero.1 (hreg m _ ?_)⟩
    have := h3 j
    rw [hc, map_mul, map_pow, map_natCast] at this
    rw [mul_sub, this, sub_self]
  choose c hc using h4
  rw [← he]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hc, algebraMap_smul]
  exact (W.N T).smul_mem _ (b j).2

end Generic

end GlobalTheory.WachSat
