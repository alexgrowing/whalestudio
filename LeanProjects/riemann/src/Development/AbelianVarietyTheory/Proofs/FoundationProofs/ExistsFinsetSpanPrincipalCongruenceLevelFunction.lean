import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMulStatement

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.LevFin

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.LevFin.sl_ofSL_mul (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (a b : SL(2, ℤ)) (f : X.K) :
    X.sl (_root_.GlobalTheory.KZ.ofSL (a * b)) f =
      X.sl (_root_.GlobalTheory.KZ.ofSL b) (X.sl (_root_.GlobalTheory.KZ.ofSL a) f) := by
  rw [map_mul, X.sl_mul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.LevFin.sl_ofSL_one (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (f : X.K) : X.sl (_root_.GlobalTheory.KZ.ofSL 1) f = f := by
  rw [map_one, X.sl_one]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.LevFin.lev_sl
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (M : ℕ) (g : SL(2, ℤ)) {f : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.Lev X M f) :
    _root_.GlobalTheory.KZ.ES.Lev X M (X.sl (_root_.GlobalTheory.KZ.ofSL g) f) := by
  intro γ hγ
  have hc : g * γ * g⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    (CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ g
  have he : g * γ = (g * γ * g⁻¹) * g := by group
  rw [← _root_.GlobalTheory.KZ.ES.LevFin.sl_ofSL_mul, he, _root_.GlobalTheory.KZ.ES.LevFin.sl_ofSL_mul,
    hf _ hc]

def levSub (X : Tower Ω ε) (M : ℕ) : Subfield X.K where
  carrier := {f | Lev X M f}
  mul_mem' := by
    intro a b ha hb γ hγ
    rw [map_mul, ha γ hγ, hb γ hγ]
  one_mem' := by
    intro γ _
    rw [map_one]
  add_mem' := by
    intro a b ha hb γ hγ
    rw [map_add, ha γ hγ, hb γ hγ]
  zero_mem' := by
    intro γ _
    rw [map_zero]
  neg_mem' := by
    intro a ha γ hγ
    rw [map_neg, ha γ hγ]
  inv_mem' := by
    intro a ha γ hγ
    rw [map_inv₀, ha γ hγ]

def actE (X : Tower Ω ε) (M : ℕ) (g : SL(2, ℤ)) : levSub X M ≃+* levSub X M where
  toFun f := ⟨X.sl (ofSL g⁻¹) f, lev_sl X M g⁻¹ f.2⟩
  invFun f := ⟨X.sl (ofSL g) f, lev_sl X M g f.2⟩
  left_inv f := by
    apply Subtype.ext
    show X.sl (ofSL g) (X.sl (ofSL g⁻¹) f) = f
    rw [← sl_ofSL_mul, inv_mul_cancel, sl_ofSL_one]
  right_inv f := by
    apply Subtype.ext
    show X.sl (ofSL g⁻¹) (X.sl (ofSL g) f) = f
    rw [← sl_ofSL_mul, mul_inv_cancel, sl_ofSL_one]
  map_mul' a b := by
    apply Subtype.ext
    show X.sl (ofSL g⁻¹) ((a : X.K) * b) = X.sl (ofSL g⁻¹) a * X.sl (ofSL g⁻¹) b
    rw [map_mul]
  map_add' a b := by
    apply Subtype.ext
    show X.sl (ofSL g⁻¹) ((a : X.K) + b) = X.sl (ofSL g⁻¹) a + X.sl (ofSL g⁻¹) b
    rw [map_add]

theorem actE_apply (X : Tower Ω ε) (M : ℕ) (g : SL(2, ℤ)) (f : levSub X M) :
    ((actE X M g f : levSub X M) : X.K) = X.sl (ofSL g⁻¹) f := rfl

def act (X : Tower Ω ε) (M : ℕ) : SL(2, ℤ) →* RingAut (levSub X M) where
  toFun := actE X M
  map_one' := by
    ext f
    rw [actE_apply, inv_one, sl_ofSL_one]
    rfl
  map_mul' g h := by
    ext f
    rw [actE_apply, _root_.mul_inv_rev, sl_ofSL_mul]
    rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma coe_sum_smul_fixedPoints_eq_sum_mul {K : Type*} [Field K] (L : Subfield K) (G : Type*) [Group G]
    [MulSemiringAction G L] {ι : Type*} [Fintype ι] (c : ι → FixedPoints.subfield G L)
    (x : ι → L) : ((∑ i, c i • x i : L) : K) = ∑ i, ((c i : L) : K) * (x i : K) :=
  (map_sum L.subtype _ _).trans (Finset.sum_congr rfl fun _ _ => rfl)

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma exists_common_denominator_adjoin_simple {E : Type*} [Field E] [Algebra Ω E] (α : E)
    (S : Finset ℕ) (a : ℕ → IntermediateField.adjoin Ω {α}) :
    ∃ s : Polynomial Ω, Polynomial.aeval α s ≠ 0 ∧ ∀ i ∈ S, ∃ r : Polynomial Ω,
      Polynomial.aeval α s * (a i : E) = Polynomial.aeval α r := by
  refine Finset.induction_on S ⟨1, by simp, by simp⟩ ?_
  intro k S _ ih
  obtain ⟨s, hs, hS⟩ := ih
  obtain ⟨r₀, s₀, h₀⟩ := (IntermediateField.mem_adjoin_simple_iff Ω _).1 (a k).2
  by_cases hs₀ : Polynomial.aeval α s₀ = 0
  · refine ⟨s, hs, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨0, by rw [h₀, hs₀, div_zero, mul_zero, map_zero]⟩
    · exact hS i hi
  · refine ⟨s * s₀, by rw [map_mul]; exact mul_ne_zero hs hs₀, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨s * r₀, by rw [h₀, map_mul, map_mul]; field_simp⟩
    · obtain ⟨r, hr⟩ := hS i hi
      exact ⟨s₀ * r, by rw [map_mul, map_mul, ← hr]; ring⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma exists_differentiableOn_an_aeval_jK
    (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero)) (q : Polynomial Ω) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an (Polynomial.aeval X.jK q) = (φ : _root_.GlobalTheory.KZ.Mero) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a
    refine ⟨fun _ => ε a, differentiableOn_const _, ?_⟩
    rw [Polynomial.aeval_C]
    exact X.an_c a
  · rintro p q ⟨φ, hφ, hφe⟩ ⟨ψ, hψ, hψe⟩
    refine ⟨φ + ψ, hφ.add hψ, ?_⟩
    rw [map_add, map_add, hφe, hψe]
    rfl
  · rintro n a ⟨φ, hφ, hφe⟩
    obtain ⟨ψ, hψe, hψ⟩ := X.j_hol
    refine ⟨φ * ψ, hφ.mul hψ, ?_⟩
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, map_mul, hφe, hψe]
    rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma norm_le_max_one_of_monic_root {d : ℕ} {c : ℕ → ℂ} {w : ℂ} {B : ℝ}
    (hc : ∀ i < d, ‖c i‖ ≤ B) (hw : w ^ d + ∑ i ∈ Finset.range d, c i * w ^ i = 0) :
    ‖w‖ ≤ max 1 (d * B) := by
  by_contra hlt
  push_neg at hlt
  have h1 : 1 < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hlt
  have h2 : (d : ℝ) * B < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hlt
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp at hw
  have hpos : 0 < ‖w‖ ^ (d - 1) := pow_pos (by linarith) _
  have key : ‖w‖ ^ d ≤ d * B * ‖w‖ ^ (d - 1) := by
    have e : w ^ d = -∑ i ∈ Finset.range d, c i * w ^ i := eq_neg_of_add_eq_zero_left hw
    calc ‖w‖ ^ d = ‖w ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range d, c i * w ^ i‖ := by rw [e, norm_neg]
      _ ≤ ∑ i ∈ Finset.range d, ‖c i * w ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range d, B * ‖w‖ ^ (d - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        rw [norm_mul, norm_pow]
        exact mul_le_mul (hc i hi) (pow_le_pow_right₀ h1.le (by omega)) (by positivity)
          (le_trans (norm_nonneg _) (hc i hi))
      _ = d * B * ‖w‖ ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
  have e2 : ‖w‖ ^ d = ‖w‖ * ‖w‖ ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have := mul_lt_mul_of_pos_right h2 hpos
  linarith

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
open Filter Topology in
private lemma exists_differentiableOn_eventuallyEq_div_of_monic_root {U : Set ℂ} (hU : IsOpen U)
    {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U) {d : ℕ}
    {c : ℕ → ℂ → ℂ} (hc : ∀ i, DifferentiableOn ℂ (c i) U)
    (hev : ∀ᶠ z in codiscreteWithin U, b z ≠ 0 ∧
      (a z / b z) ^ d + ∑ i ∈ Finset.range d, c i z * (a z / b z) ^ i = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ U ∧ (fun z => a z / b z) =ᶠ[codiscreteWithin U] φ := by
  set φ₀ : ℂ → ℂ := fun z => a z / b z with hφ₀
  set φ : ℂ → ℂ := fun z => limUnder (𝓝[≠] z) φ₀ with hφ
  have key : ∀ z₀ ∈ U, DifferentiableAt ℂ φ z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, φ₀ z = φ z := by
    intro z₀ hz₀
    have hQ : {z | b z ≠ 0 ∧ φ₀ z ^ d + ∑ i ∈ Finset.range d, c i z * φ₀ z ^ i = 0} ∈
        𝓝[≠] z₀ := by
      have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hev) z₀ hz₀
      have h2 : U ∈ 𝓝[≠] z₀ := nhdsWithin_le_nhds (hU.mem_nhds hz₀)
      filter_upwards [h1, h2] with z hz hzU
      rcases hz with hz | hz
      · exact hz
      · exact absurd hzU hz
    have hbd : ∀ᶠ z in 𝓝 z₀, ∀ i ∈ Finset.range d, ‖c i z‖ < ‖c i z₀‖ + 1 := by
      rw [Filter.eventually_all_finset]
      intro i _
      have hcont : ContinuousAt (fun z => ‖c i z‖) z₀ :=
        ((hc i).continuousOn.continuousAt (hU.mem_nhds hz₀)).norm
      exact hcont.eventually_lt continuousAt_const (by linarith)
    obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hQ
    set s := u ∩ U ∩ {z | ∀ i ∈ Finset.range d, ‖c i z‖ < ‖c i z₀‖ + 1} with hs_def
    have hs : s ∈ 𝓝 z₀ := inter_mem (inter_mem hu (hU.mem_nhds hz₀)) hbd
    have hsU : s ⊆ U := fun z hz => hz.1.2
    have hP : ∀ z ∈ s \ {z₀}, b z ≠ 0 ∧
        φ₀ z ^ d + ∑ i ∈ Finset.range d, c i z * φ₀ z ^ i = 0 :=
      fun z hz => hus ⟨hz.1.1.1, hz.2⟩
    set B : ℝ := ∑ i ∈ Finset.range d, (‖c i z₀‖ + 1) with hB
    have hdiff : DifferentiableOn ℂ φ₀ (s \ {z₀}) :=
      (ha.mono (fun z hz => hsU hz.1)).div (hb.mono (fun z hz => hsU hz.1))
        (fun z hz => (hP z hz).1)
    have hbdd : BddAbove (norm ∘ φ₀ '' (s \ {z₀})) := by
      refine ⟨max 1 (d * B), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      refine norm_le_max_one_of_monic_root (c := fun i => c i z) (fun i hi => ?_) (hP z hz).2
      have hi' : i ∈ Finset.range d := Finset.mem_range.2 hi
      exact (hz.1.2 i hi').le.trans (Finset.single_le_sum (f := fun j => ‖c j z₀‖ + 1)
        (fun j _ => by positivity) hi')
    have hupd := Complex.differentiableOn_update_limUnder_of_bddAbove hs hdiff hbdd
    have heq : ∀ z ∈ s \ {z₀}, φ z = φ₀ z := by
      intro z hz
      have hzU : U ∈ 𝓝 z := hU.mem_nhds (hsU hz.1)
      have hcont : ContinuousAt φ₀ z :=
        ((ha.differentiableAt hzU).div (hb.differentiableAt hzU) (hP z hz).1).continuousAt
      exact (tendsto_nhdsWithin_of_tendsto_nhds hcont).limUnder_eq
    refine ⟨?_, ?_⟩
    · refine (hupd.differentiableAt hs).congr_of_eventuallyEq ?_
      filter_upwards [hs] with z hz
      by_cases h : z = z₀
      · subst h
        simp [hφ]
      · rw [Function.update_of_ne h, heq z ⟨hz, h⟩]
    · filter_upwards [diff_mem_nhdsWithin_compl hs {z₀}] with z hz
      exact (heq z hz).symm
  refine ⟨φ, fun z hz => (key z hz).1.differentiableWithinAt, ?_⟩
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z₀ hz₀ => ?_
  filter_upwards [(key z₀ hz₀).2] with z hz
  exact Or.inl hz

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
open Filter in
private lemma exists_differentiableOn_eq_of_monic_root_Mero {y : _root_.GlobalTheory.KZ.Mero}
    (hy : ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a _root_.GlobalTheory.KZ.Hs ∧
      DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs ∧ (b : _root_.GlobalTheory.KZ.Mero) ≠ 0 ∧
      y * (b : _root_.GlobalTheory.KZ.Mero) = (a : _root_.GlobalTheory.KZ.Mero))
    {d : ℕ} {c : ℕ → ℂ → ℂ} (hc : ∀ i, DifferentiableOn ℂ (c i) _root_.GlobalTheory.KZ.Hs)
    (hrel : y ^ d + ∑ i ∈ Finset.range d, (c i : _root_.GlobalTheory.KZ.Mero) * y ^ i = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      y = (φ : _root_.GlobalTheory.KZ.Mero) := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := hy
  obtain ⟨hbev, hu⟩ := _root_.GlobalTheory.FN.germ_main.2.2 b hb hb0
  have hyq : y = ((fun z => a z / b z : ℂ → ℂ) : _root_.GlobalTheory.KZ.Mero) := by
    have hq : ((fun z => a z / b z : ℂ → ℂ) : _root_.GlobalTheory.KZ.Mero) *
        (b : _root_.GlobalTheory.KZ.Mero) = (a : _root_.GlobalTheory.KZ.Mero) := by
      rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
      filter_upwards [hbev] with z hz
      simp [div_mul_cancel₀ _ hz]
    exact hu.mul_left_injective (hab.trans hq.symm)
  have hsum : ((fun z => (a z / b z) ^ d + ∑ i ∈ Finset.range d, c i z * (a z / b z) ^ i :
      ℂ → ℂ) : _root_.GlobalTheory.KZ.Mero) = ((0 : ℂ → ℂ) : _root_.GlobalTheory.KZ.Mero) := by
    rw [Filter.Germ.coe_zero, ← hrel, hyq]
    have e := map_sum (Filter.Germ.coeRingHom (codiscreteWithin _root_.GlobalTheory.KZ.Hs))
      (fun i z => c i z * (a z / b z) ^ i) (Finset.range d)
    have e2 : ∀ f : ℂ → ℂ, Filter.Germ.coeRingHom (codiscreteWithin _root_.GlobalTheory.KZ.Hs) f =
      (f : _root_.GlobalTheory.KZ.Mero) := fun f => rfl
    simp only [e2] at e
    have hfun : (fun z => (a z / b z) ^ d + ∑ i ∈ Finset.range d, c i z * (a z / b z) ^ i) =
        (fun z => a z / b z) ^ d + ∑ i ∈ Finset.range d, (fun z => c i z * (a z / b z) ^ i) := by
      funext z
      simp [Finset.sum_apply]
    rw [hfun, Filter.Germ.coe_add, Filter.Germ.coe_pow, e]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => rfl)
  have hev := Filter.Germ.coe_eq.1 hsum
  obtain ⟨φ, hφ, hφe⟩ := exists_differentiableOn_eventuallyEq_div_of_monic_root
    _root_.GlobalTheory.KZ.SiegelModel.isOpen_Hs ha hb hc (by
      filter_upwards [hbev, hev] with z hz1 hz2
      exact ⟨hz1, hz2⟩)
  exact ⟨φ, hφ, hyq.trans (Filter.Germ.coe_eq.2 hφe)⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma sl_aeval_jK (X : _root_.GlobalTheory.KZ.Tower Ω ε) (γ : SL(2, ℤ))
    (q : Polynomial Ω) :
    X.sl (_root_.GlobalTheory.KZ.ofSL γ) (Polynomial.aeval X.jK q) = Polynomial.aeval X.jK q := by
  have e := Polynomial.aeval_algHom_apply
    ((X.sl (_root_.GlobalTheory.KZ.ofSL γ) : X.K ≃ₐ[Ω] X.K) : X.K →ₐ[Ω] X.K) X.jK q
  simp only [AlgEquiv.coe_algHom, X.j_inv] at e
  exact e.symm

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma mem_adjoin_jK_of_sl_invariant [IsAlgClosure ℚ Ω]
    (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero)) (h : X.K)
    (hinv : ∀ γ : SL(2, ℤ), X.sl (_root_.GlobalTheory.KZ.ofSL γ) h = h) :
    h ∈ IntermediateField.adjoin Ω {X.jK} := by
  set F := IntermediateField.adjoin Ω {X.jK}
  have hint : IsIntegral F h := (X.alg_j h).isIntegral
  set p := minpoly F h with hp
  have hmon : p.Monic := minpoly.monic hint
  set d := p.natDegree with hd
  obtain ⟨s, hs₀, hsr⟩ := exists_common_denominator_adjoin_simple X.jK (Finset.range d)
    (fun i => p.coeff i)
  choose! r hr using hsr
  set ℓ := Polynomial.aeval X.jK s with hℓ
  have hexp : h ^ d + ∑ i ∈ Finset.range d, (p.coeff i : X.K) * h ^ i = 0 := by
    have h0 : Polynomial.aeval h p = 0 := minpoly.aeval F h
    rw [hmon.as_sum] at h0
    simpa [map_add, map_sum, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      IntermediateField.algebraMap_apply] using h0
  set c : ℕ → X.K := fun i => Polynomial.aeval X.jK (s ^ (d - i - 1) * r i) with hc
  have hrel : (ℓ * h) ^ d + ∑ i ∈ Finset.range d, c i * (ℓ * h) ^ i = 0 := by
    have e : (ℓ * h) ^ d + ∑ i ∈ Finset.range d, c i * (ℓ * h) ^ i =
        ℓ ^ d * (h ^ d + ∑ i ∈ Finset.range d, (p.coeff i : X.K) * h ^ i) := by
      rw [mul_add, Finset.mul_sum, mul_pow]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      simp only [hc, map_mul, map_pow]
      rw [← hr i hi]
      have hdi : d = d - i - 1 + 1 + i := by omega
      conv_rhs => rw [hdi]
      ring
    rw [e, hexp, mul_zero]
  have hcK : ∀ i, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an (c i) = (φ : _root_.GlobalTheory.KZ.Mero) :=
    fun i => exists_differentiableOn_an_aeval_jK X hj _
  choose C hC hCe using hcK
  have hgerm : X.an (ℓ * h) ^ d + ∑ i ∈ Finset.range d,
      (C i : _root_.GlobalTheory.KZ.Mero) * X.an (ℓ * h) ^ i = 0 := by
    have e := congrArg X.an hrel
    rw [map_add, map_pow, map_sum, map_zero] at e
    simpa only [map_mul, map_pow, hCe] using e
  obtain ⟨φ, hφ, hφe⟩ := exists_differentiableOn_eq_of_monic_root_Mero
    (X.an_mero (ℓ * h)) hC hgerm
  have hginv : ∀ γ : SL(2, ℤ), X.sl (_root_.GlobalTheory.KZ.ofSL γ) (ℓ * h) = ℓ * h := by
    intro γ
    rw [map_mul, hinv, hℓ, sl_aeval_jK]
  have hgF : ℓ * h ∈ F :=
    IntermediateField.algebra_adjoin_le_adjoin Ω _
      (_root_.GlobalTheory.KZ.LevelOne.mem_adjoin_j ε X ε.injective hj _ hginv ⟨φ, hφ, hφe⟩)
  have hℓF : ℓ ∈ F :=
    IntermediateField.algebra_adjoin_le_adjoin Ω _ (Polynomial.aeval_mem_adjoin_singleton Ω X.jK)
  have e : h = ℓ * h / ℓ := (mul_div_cancel_left₀ h hs₀).symm
  rw [e]
  exact div_mem hgF hℓF

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in

theorem _root_.GlobalTheory.KZ.ES.LevFin.exists_finset_span : ∀ {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero)) → ∀ M : ℕ, 0 < M → ∃ T : Finset X.K,
      (∀ x ∈ T, _root_.GlobalTheory.KZ.ES.Lev X M x) ∧
      ∀ f : X.K, _root_.GlobalTheory.KZ.ES.Lev X M f →
        f ∈ Submodule.span (IntermediateField.adjoin Ω {X.jK}) (T : Set X.K) := by
  intro Ω _ _ _ ε X hj M hM
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  set L := _root_.GlobalTheory.KZ.ES.LevFin.levSub X M
  set ρ := _root_.GlobalTheory.KZ.ES.LevFin.act X M with hρ
  have hker : CongruenceSubgroup.Gamma M ≤ ρ.ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker]
    ext f
    rw [show ρ γ = _root_.GlobalTheory.KZ.ES.LevFin.actE X M γ from rfl,
      _root_.GlobalTheory.KZ.ES.LevFin.actE_apply]
    exact f.2 _ (inv_mem hγ)
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hker
  haveI : Finite ρ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  let b := Module.finBasis (FixedPoints.subfield ρ.range L) L
  refine ⟨Finset.univ.image (fun i => ((b i : L) : X.K)), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact (b i).2
  · intro f hf
    set fL : L := ⟨f, hf⟩ with hfL
    have hcoe : (fL : X.K) = ∑ i, ((b.repr fL i : L) : X.K) * ((b i : L) : X.K) := by
      conv_lhs => rw [← b.sum_repr fL]
      exact coe_sum_smul_fixedPoints_eq_sum_mul L ρ.range _ _
    have hf' : f = (fL : X.K) := rfl
    rw [hf', hcoe]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hinv : ∀ γ : SL(2, ℤ), X.sl (_root_.GlobalTheory.KZ.ofSL γ)
        ((b.repr fL i : L) : X.K) = ((b.repr fL i : L) : X.K) := by
      have H : ∀ δ : SL(2, ℤ), X.sl (_root_.GlobalTheory.KZ.ofSL δ⁻¹) ((b.repr fL i : L) : X.K) =
          ((b.repr fL i : L) : X.K) := by
        intro δ
        have hx : ∀ g : ρ.range, g • (b.repr fL i : L) = (b.repr fL i : L) := (b.repr fL i).2
        have hx' : (ρ δ) (b.repr fL i : L) = (b.repr fL i : L) :=
          hx ⟨ρ δ, MonoidHom.mem_range.2 ⟨δ, rfl⟩⟩
        have e := congrArg Subtype.val hx'
        have e2 : (((ρ δ) (b.repr fL i : L) : L) : X.K) =
            X.sl (_root_.GlobalTheory.KZ.ofSL δ⁻¹) ((b.repr fL i : L) : X.K) :=
          _root_.GlobalTheory.KZ.ES.LevFin.actE_apply X M δ _
        exact e2.symm.trans e
      intro γ
      have hγ := H γ⁻¹
      generalize ((b.repr fL i : L) : X.K) = c at hγ ⊢
      rwa [inv_inv] at hγ
    have ht : ((b i : L) : X.K) ∈
        ((Finset.univ.image fun j => ((b j : L) : X.K) : Finset X.K) : Set X.K) :=
      Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    generalize ((b.repr fL i : L) : X.K) = c at hinv ⊢
    generalize ((b i : L) : X.K) = t at ht ⊢
    have hmem := mem_adjoin_jK_of_sl_invariant X hj c hinv
    have e : c * t = (⟨c, hmem⟩ : IntermediateField.adjoin Ω {X.jK}) • t := by
      rw [IntermediateField.smul_def, smul_eq_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ht)

end GlobalTheory.KZ.ES.LevFin
