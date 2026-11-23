import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem eigen_split_holds : EigenSplit := by
  intro K _ _ ι T X _ ty pr BB th chi chi' hth hBB hc hsep
  refine ⟨fun i j => if ty j = pr (ty i) then 0 else BB i j / th, fun i j => ?_, fun i j => ?_⟩
  · dsimp only
    split_ifs with h
    · simp
    · obtain ⟨x, hx⟩ := hsep (ty i) (ty j) h
      have h1 := hc x i j
      rw [norm_mul, hx, one_mul] at h1
      rw [norm_div]
      exact div_le_one_of_le₀ h1 (norm_nonneg _)
  · dsimp only
    split_ifs with h
    · simp
    · field_simp
      ring

section Hom

variable {K : Type} [Field K]

theorem mvSubst_subst {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha]

theorem cc_linForm {m : Type} [Fintype m] (v : m → K) :
    MvPowerSeries.constantCoeff (∑ x, MvPowerSeries.C (v x) * MvPowerSeries.X x :
      MvPowerSeries m K) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

theorem hasSubst_lin {n m : Type} [Finite n] [Fintype m] (A : n → m → K) :
    MvPowerSeries.HasSubst
      (fun i => (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x : MvPowerSeries m K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_linForm (A i)

def linSubHom {n m : Type} [Finite n] [Fintype m] (A : n → m → K) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries m K :=
  MvPowerSeries.substAlgHom (hasSubst_lin A)

theorem linSubHom_apply {n m : Type} [Finite n] [Fintype m] (A : n → m → K)
    (f : MvPowerSeries n K) : linSubHom A f = linSub A f :=
  MvPowerSeries.substAlgHom_apply _ f

theorem linSub_C {n m : Type} [Fintype m] (A : n → m → K) (r : K) :
    linSub A (MvPowerSeries.C r) = MvPowerSeries.C r :=
  MvPowerSeries.subst_C r

theorem linSub_X {n m : Type} [Finite n] [Fintype m] (A : n → m → K) (i : n) :
    linSub A (MvPowerSeries.X i) = ∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x :=
  MvPowerSeries.subst_X (hasSubst_lin A) i

theorem linSub_sqSum {n m : Type} [Fintype n] [Fintype m] (A : n → m → K) (c : n → K) :
    linSub A (sqSum c) =
      ∑ i, MvPowerSeries.C (c i) * (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) ^ 2 := by
  unfold sqSum
  rw [← linSubHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, linSubHom_apply, linSubHom_apply, linSub_C, linSub_X]

theorem cc_sqSum {n : Type} [Fintype n] (c : n → K) :
    MvPowerSeries.constantCoeff (sqSum c) = 0 := by
  unfold sqSum
  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => by
    rw [map_mul, map_pow, MvPowerSeries.constantCoeff_X, zero_pow two_ne_zero, mul_zero]

theorem cc_zPt {n : Type} {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) linv h0

theorem hasSubst_zPt {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries.HasSubst (fun i : n =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_zPt h0 i

def toZHom {n : Type} [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries n K :=
  MvPowerSeries.substAlgHom (hasSubst_zPt h0)

theorem toZHom_apply {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : MvPowerSeries n K) :
    toZHom h0 f = toZ linv f :=
  MvPowerSeries.substAlgHom_apply _ f

theorem cc_toZ {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (toZ linv f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_zPt h0) (fun i => cc_zPt h0 i) hf

theorem toZ_subst_X {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : PowerSeries K) (i : n) :
    toZ linv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) f) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) (PowerSeries.subst linv f) := by
  unfold toZ
  rw [mvSubst_subst (hasSubst_zPt h0) (MvPowerSeries.constantCoeff_X i),
    MvPowerSeries.subst_X (hasSubst_zPt h0),
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]

theorem toZ_phSum {n : Type} [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (c : n → K) (ph : PowerSeries K) :
    toZ linv (phSum c ph) = phSum c (PowerSeries.subst linv ph) := by
  unfold phSum
  rw [← toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toZHom_apply, toZ_subst_X h0]

theorem cc_phSum {n : Type} [Fintype n] (c : n → K) {ph : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ph = 0) : MvPowerSeries.constantCoeff (phSum c ph) = 0 := by
  unfold phSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul,
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) ph h0, mul_zero]

theorem phSum_add {n : Type} [Fintype n] (c : n → K) (f g : PowerSeries K) :
    phSum c (f + g) = phSum c f + phSum c g := by
  unfold phSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero
    (MvPowerSeries.constantCoeff_X i)), smul_add]

theorem phSum_sq {n : Type} [Fintype n] (c : n → K) (s : K) :
    phSum c (PowerSeries.C s * PowerSeries.X ^ 2) = MvPowerSeries.C s * sqSum c := by
  unfold phSum sqSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries n K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs,
    PowerSeries.subst_C, MvPowerSeries.smul_eq_C_mul]
  ring

end Hom

theorem jetsIn_linForm {K : Type} [Field K] {R : Subring K} {m : Type} [Fintype m] {v : m → K}
    (hv : ∀ x, v x ∈ R) :
    JetsIn R (∑ x, MvPowerSeries.C (v x) * MvPowerSeries.X x : MvPowerSeries m K) :=
  jetsIn_sum _ _ fun x _ => jetsIn_mul (jetsIn_C (hv x)) (jetsIn_X x)

theorem jetsIn_linSub {K : Type} [Field K] [CharZero K] {R : Subring K} {n m : Type} [Fintype n]
    [Fintype m] {A : n → m → K} (hA : ∀ i x, A i x ∈ R) {f : MvPowerSeries n K} (hf : JetsIn R f) :
    JetsIn R (linSub A f) :=
  JetsSubst_of jets_ring_holds jets_div_pow_holds K R n m f _ hf (fun i => cc_linForm (A i))
    fun i => jetsIn_linForm (hA i)

theorem linSub_mvExp {K : Type} [Field K] [CharZero K] {n m : Type} [Finite n] [Fintype m]
    (A : n → m → K) {f : MvPowerSeries n K} (hf : MvPowerSeries.constantCoeff f = 0) :
    linSub A (mvExp f) = mvExp (linSub A f) :=
  mvSubst_mvExp hf (hasSubst_lin A)

theorem toZ_mvExp {K : Type} [Field K] [CharZero K] {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : toZ linv (mvExp f) = mvExp (toZ linv f) :=
  mvSubst_mvExp hf (hasSubst_zPt h0)

theorem shape_congruence_holds : ShapeCong := by
  intro K _ _ _ n m _ _ S0 th c A be Q2 h2 hS hA hbe hQ0 hQ hlin J hJ
  have h20 : (2 : K) ≠ 0 := two_ne_zero
  have hr : S0 * th / 2 ∈ unitBall K := by
    change ‖S0 * th / 2‖ ≤ 1
    rw [norm_div, h2, div_one]
    exact hS
  have c1 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (S0 / 2) * sqSum c)) = 0 := by
    rw [map_neg, map_mul, cc_sqSum, mul_zero, neg_zero]
  have c2 : MvPowerSeries.constantCoeff ((-S0) • be) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hbe, mul_zero]
  have c3 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (S0 * th / 2) * Q2)) = 0 := by
    rw [map_neg, map_mul, hQ0, mul_zero, neg_zero]
  have e : linSub A (-(MvPowerSeries.C (S0 / 2) * sqSum c)) =
      (-S0) • be + -(MvPowerSeries.C (S0 * th / 2) * Q2) := by
    rw [← linSubHom_apply, map_neg, map_mul, linSubHom_apply, linSubHom_apply, linSub_C, hlin,
      MvPowerSeries.smul_eq_C_mul]
    have e1 : (MvPowerSeries.C (-S0) : MvPowerSeries m K) =
        -(MvPowerSeries.C (S0 / 2) * MvPowerSeries.C 2) := by
      rw [← map_mul, ← map_neg, div_mul_cancel₀ _ h20]
    have e2 : (MvPowerSeries.C (S0 * th / 2) : MvPowerSeries m K) =
        MvPowerSeries.C (S0 / 2) * MvPowerSeries.C th := by
      rw [← map_mul]
      congr 1
      ring
    rw [e1, e2]
    ring
  refine ⟨mvExp (-(MvPowerSeries.C (S0 * th / 2) * Q2)) * linSub A J, ?_, ?_⟩
  · exact jetsIn_mul (R := unitBall K)
      (jetsIn_mvExp c3 (jetsIn_neg (jetsIn_mul (jetsIn_C hr) hQ))) (jetsIn_linSub hA hJ)
  · rw [← linSubHom_apply, map_mul, linSubHom_apply, linSubHom_apply, linSub_mvExp A c1, e,
      mvExp_add c2 c3, mul_assoc]

theorem jetsIn_phSum {K : Type} [Field K] [CharZero K] {R : Subring K} {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ i, c i ∈ R) {f : PowerSeries K} (hf : JetsIn1 R f) :
    JetsIn R (phSum c f) := by
  unfold phSum
  refine jetsIn_sum _ _ fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul]
  exact jetsIn_mul (jetsIn_C (hc i))
    (jetsIn_subst_one hf (MvPowerSeries.constantCoeff_X i) (jetsIn_X i))

theorem jetsIn_toZ {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hl : IsOneUnit R (PowerSeries.derivative K l)) {n : Type} [Fintype n]
    {G : MvPowerSeries n K} (hG : IntMv R G) : JetsIn R (toZ linv G) :=
  IntMvZ_of (JetsSubst_of jets_ring_holds jets_div_pow_holds) integral_jets_holds jets_subst_one_holds
    jets_ring_holds K R l linv h hl n G hG

theorem jetsIn1_rest {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}
    (h : IsLogPair l linv) (h0 : PowerSeries.constantCoeff ph = 0)
    (hj : ∀ i : ℕ, 1 ≤ i → i ≠ 2 → jet l ph i ∈ R) :
    JetsIn1 R (PowerSeries.subst linv ph - PowerSeries.C (jet l ph 2 / 2) * PowerSeries.X ^ 2) := by
  intro k
  rw [map_sub, mul_sub, ← jetAdditive K l linv ph h k, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  by_cases h2 : k = 2
  · subst h2
    have : jet l ph 2 - ((Nat.factorial 2 : ℕ) : K) * (jet l ph 2 / 2 * if 2 = 2 then 1 else 0) = 0 := by
      simp only [Nat.factorial, if_true]
      push_cast
      field_simp
      ring
    rw [this]
    exact R.zero_mem
  · rw [if_neg h2, mul_zero, mul_zero, sub_zero]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : jet l ph 0 = 0 := h0
      rw [this]
      exact R.zero_mem
    · exact hj k hk h2

theorem shape_orthogonal_holds : ShapeOrth := by
  intro K _ _ _ l linv ph d h hl hph hshape n _ c hc G hG
  have hv : PowerSeries.constantCoeff linv = 0 := h.2.2.1
  set S : K := jet l ph 2 / 2 with hS
  set ph0 : PowerSeries K := PowerSeries.subst linv ph - PowerSeries.C S * PowerSeries.X ^ 2
    with hph0
  have j0 : JetsIn1 (unitBall K) ph0 := jetsIn1_rest h hph hshape.2.1
  have cph0 : PowerSeries.constantCoeff ph0 = 0 := by
    rw [hph0, map_sub, JetSubstitutionLemmas.cc_subst1 hv, hph]
    simp
  have c1 : MvPowerSeries.constantCoeff (-(phSum c ph)) = 0 := by
    rw [map_neg, cc_phSum c hph, neg_zero]
  have c2 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C S * sqSum c)) = 0 := by
    rw [map_neg, map_mul, cc_sqSum, mul_zero, neg_zero]
  have c3 : MvPowerSeries.constantCoeff (-(phSum c ph0)) = 0 := by
    rw [map_neg, cc_phSum c cph0, neg_zero]
  have e : toZ linv (-(phSum c ph)) = -(MvPowerSeries.C S * sqSum c) + -(phSum c ph0) := by
    rw [← toZHom_apply hv, map_neg, toZHom_apply, toZ_phSum hv, ← phSum_sq, ← neg_add, ← phSum_add,
      hph0, add_sub_cancel]
  refine ⟨mvExp (-(phSum c ph0)) * toZ linv G, ?_, ?_⟩
  · exact jetsIn_mul (R := unitBall K) (jetsIn_mvExp c3 (jetsIn_neg (jetsIn_phSum hc j0)))
      (jetsIn_toZ h hl hG)
  · rw [← toZHom_apply hv, map_mul, toZHom_apply, toZHom_apply, toZ_mvExp hv c1, e,
      mvExp_add c2 c3, mul_assoc]

end Formalism.L2.Th1.G
