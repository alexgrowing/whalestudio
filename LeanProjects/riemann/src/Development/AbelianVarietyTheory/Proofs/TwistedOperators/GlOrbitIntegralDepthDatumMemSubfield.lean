import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.SmallFInF

section Helpers
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_valLe (c : kˣ) : IsOpen {t : k | valuation k t ≤ valuation k (c : k)} := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have e : {t : k | valuation k t ≤ valuation k (c : k)} = (fun t => t / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ h0]
  rw [e]
  exact IsOpen.preimage (continuous_id.div_const _) Valuation.isOpen_integer

theorem isOpen_cosetM {n m : Type} [Fintype n] [Fintype m] (c : kˣ) (x : Matrix n m k) :
    IsOpen {y : Matrix n m k | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_valLe c).preimage (f := fun y : Matrix n m k => y i j - x i j) (by fun_prop)

theorem isCompact_ballM {n : Type} [Fintype n] (R : kˣ) :
    IsCompact {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} := by
  have h0 : 0 < valuation k (R : k) := zero_lt_iff.2 (by simp)
  have e : {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} =
      (fun z : Matrix n n k => (R : k) • z) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨(R : k)⁻¹ • y, fun i j => ?_, ?_⟩
      · rw [Valuation.mem_integer_iff]
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [inv_mul_le_iff₀ h0, mul_one]; exact hy i j
      · simp [smul_smul]
    · rintro ⟨z, hz, rfl⟩ i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hz i j))
  rw [e]
  exact isCompact_intMatrix.image (continuous_const_smul _)

end Helpers

theorem smallF_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → 1 ≤ e → CondLE ϖ e ν → ¬ IsUnram ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u (1 / 2) ∈ F) → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → (∀ X, Ψ X ∈ F) → ∀ h : GL D k, smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ F J hJo hJK σ ν ϖ e hϖ he hcond hram hνF hapF c Ψ hΨ hΨF h
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨R, N, hbd, hper⟩ := GlobalTheory.T.exists_valuation_bound_and_periodic_frameBlock σ hϖ c hΨ h
  set Y := Y0 k σ * h.val with hY
  set cN : kˣ := ϖ ^ N with hcN
  set z : ℂ := (Fintype.card D : ℂ) / 2 with hz
  have hzF : ∀ u : kˣ, apow u z ∈ F := fun u => by
    have : apow u z = (apow u (1 / 2)) ^ (Fintype.card D) := by
      simp only [apow, hz]
      rw [← Complex.cpow_nat_mul]; congr 1; ring
    rw [this]; exact pow_mem (hapF u) _
  let Cs : Matrix A' A' k → Set (GL A' k) :=
    fun x => {g | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (cN : k)}
  have hCs_meas : ∀ x, MeasurableSet (Cs x) := fun x =>
    ((isOpen_cosetM cN x).preimage Units.continuous_val).measurableSet
  have hCs_eq : ∀ x y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) →
      Cs x = Cs y := by
    intro x y hxy
    ext g
    simp only [Cs, Set.mem_setOf_eq]
    constructor
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) ((Valuation.map_sub_swap _ _ _).le.trans (hxy i j))
      simpa using this
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) (hxy i j)
      simpa using this
  have hcoset : ∀ x, ∫ g in Cs x, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
    intro x
    by_cases hs : ∃ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) ∧ y.det = 0
    · obtain ⟨y, hy, hy0⟩ := hs
      rw [hCs_eq x y hy]
      rw [GlobalTheory.T.integral_ramifiedChar_det_singularMatrixCoset_eq_zero (haarVol J) ν z hram cN y hy0]
      exact F.zero_mem
    · push_neg at hs
      exact GlobalTheory.T.integral_detChar_invertibleMatrixBall_mem_subfield F hJo hJK ν z hϖ hcond hνF hzF cN x hs

  let L : AddSubgroup (Matrix A' A' k) :=
    { carrier := {Z | ∀ i j, valuation k (Z i j) ≤ valuation k (cN : k)}
      add_mem' := fun ha hb i j => Valuation.map_add_le _ (ha i j) (hb i j)
      zero_mem' := fun i j => by simp
      neg_mem' := fun ha i j => by simpa using ha i j }
  let q : Matrix A' A' k → Matrix A' A' k ⧸ L := QuotientAddGroup.mk
  have hq : ∀ x y : Matrix A' A' k, q x = q y ↔ ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k) := by
    intro x y
    rw [QuotientAddGroup.eq]
    refine forall₂_congr fun i j => ?_
    show valuation k ((-x + y) i j) ≤ _ ↔ _
    rw [show (-x + y) i j = -(x i j - y i j) by simp; ring, Valuation.map_neg]

  obtain ⟨T0, hT0⟩ := (isCompact_ballM (n := A') R).elim_finite_subcover
    (fun y : Matrix A' A' k => {x : Matrix A' A' k | ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k)})
    (fun y => isOpen_cosetM cN y)
    (fun x _ => Set.mem_iUnion.2 ⟨x, fun i j => by simp⟩)
  classical
  let T : Finset (Matrix A' A' k ⧸ L) := T0.image q
  set f : GL A' k → ℂ := fun g => Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z with hf
  have hdec : f = fun g => ∑ t ∈ T, ({g : GL A' k | q g.val = t}).indicator f g := by
    funext g
    by_cases h0 : f g = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [Set.indicator_apply, h0]
    · have hΨ0 : Ψ (g.val * Y) ≠ 0 := fun h1 => h0 (by simp [hf, h1])
      have hB := hbd g.val hΨ0
      obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hT0 hB)
      have hqt : q g.val ∈ T := Finset.mem_image.2 ⟨y, hyT, ((hq _ _).2 hy).symm⟩
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_ite_eq]
      simp [hqt]
  show ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂(haarVol J) ∈ F
  change ∫ g, f g ∂(haarVol J) ∈ F
  by_cases hint : Integrable f (haarVol J)
  · have hmeas : ∀ t, MeasurableSet {g : GL A' k | q g.val = t} := by
      intro t
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
      have : {g : GL A' k | q g.val = q y} = Cs y := by
        ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
      rw [this]; exact hCs_meas y
    rw [hdec, integral_finset_sum _ (fun t _ => hint.indicator (hmeas t))]
    refine sum_mem fun t _ => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
    have hset : {g : GL A' k | q g.val = q y} = Cs y := by
      ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
    rw [integral_indicator (hmeas _), hset]
    have hc : ∫ g in Cs y, f g ∂(haarVol J) =
        ∫ g in Cs y, Ψ (y * Y) * ((ν (gdet g) : ℂ) * apow (gdet g) z) ∂(haarVol J) := by
      refine setIntegral_congr_fun (hCs_meas y) fun g hg => ?_
      have h1 : g.val = y + (g.val - y) := by abel
      have h2 : Ψ (g.val * Y) = Ψ (y * Y) := by
        rw [h1, hper y (g.val - y) (fun i j => hg i j)]
      simp only [hf, h2, mul_assoc]
    rw [hc, integral_const_mul]
    exact F.mul_mem (hΨF _) (hcoset y)
  · rw [integral_undef hint]; exact F.zero_mem

end GlobalTheory.SmallFInF
