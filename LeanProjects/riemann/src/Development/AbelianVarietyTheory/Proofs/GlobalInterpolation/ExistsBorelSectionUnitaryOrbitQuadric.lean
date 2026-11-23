import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

namespace GlobalTheory.QuadricSection

section general

variable {n : Type} [Fintype n] [DecidableEq n]

def coef (J : Matrix n n ℂ) (x y : n → ℂ) : ℂ := star (x - y) ⬝ᵥ (J *ᵥ x)

def qrefl (J : Matrix n n ℂ) (x y : n → ℂ) : Matrix n n ℂ :=
  1 - (coef J x y)⁻¹ • vecMulVec (x - y) (star (x - y) ᵥ* J)

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.QuadricSection.qrefl_mulVec (J : Matrix n n ℂ) (x y : n → ℂ)
    (hc : _root_.GlobalTheory.QuadricSection.coef J x y ≠ 0) :
    _root_.GlobalTheory.QuadricSection.qrefl J x y *ᵥ x = y := by
  have hdot : (star (x - y) ᵥ* J) ⬝ᵥ x = _root_.GlobalTheory.QuadricSection.coef J x y := by
    rw [_root_.GlobalTheory.QuadricSection.coef, dotProduct_mulVec]
  rw [_root_.GlobalTheory.QuadricSection.qrefl, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    hdot, op_smul_eq_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_sub_cancel]

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
private lemma star_dotProduct_mulVec_of_hermitian {J : Matrix n n ℂ} (hJ : Jᴴ = J) (a b : n → ℂ) :
    star (star a ⬝ᵥ (J *ᵥ b)) = star b ⬝ᵥ (J *ᵥ a) := by
  rw [← star_dotProduct_star, star_mulVec, star_star, hJ, dotProduct_comm, dotProduct_mulVec]
  exact dotProduct_comm _ _

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.QuadricSection.qrefl_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (x y : n → ℂ)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (hc : _root_.GlobalTheory.QuadricSection.coef J x y ≠ 0) :
    (_root_.GlobalTheory.QuadricSection.qrefl J x y)ᴴ * J * _root_.GlobalTheory.QuadricSection.qrefl J x y = J := by
  set c := _root_.GlobalTheory.QuadricSection.coef J x y with hcdef
  set d := x - y with hd
  set e := star d ᵥ* J with he
  have hstar_e : star e = J *ᵥ d := by rw [he, star_vecMul, hJ, star_star]
  have hq : e ⬝ᵥ d = star d ⬝ᵥ (J *ᵥ d) := by rw [he, dotProduct_mulVec]
  have hsum : c + star c = star d ⬝ᵥ (J *ᵥ d) := by
    have h1 : star c = star x ⬝ᵥ (J *ᵥ d) := by
      rw [hcdef, _root_.GlobalTheory.QuadricSection.coef, star_dotProduct_mulVec_of_hermitian hJ]
    rw [h1, hcdef, _root_.GlobalTheory.QuadricSection.coef, ← hd]
    simp only [hd, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct]
    linear_combination hxy
  have hcs : star c ≠ 0 := star_ne_zero.mpr hc
  have hJe : J * vecMulVec d e = vecMulVec (J *ᵥ d) e := mul_vecMulVec _ _ _
  have heJ : vecMulVec (J *ᵥ d) (star d) * J = vecMulVec (J *ᵥ d) e := by
    rw [vecMulVec_mul]
  have hVV : vecMulVec (J *ᵥ d) e * vecMulVec d e = (e ⬝ᵥ d) • vecMulVec (J *ᵥ d) e := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp [vecMulVec_apply, mul_left_comm]
  have hR : (_root_.GlobalTheory.QuadricSection.qrefl J x y)ᴴ = 1 - (star c)⁻¹ • vecMulVec (J *ᵥ d) (star d) := by
    rw [_root_.GlobalTheory.QuadricSection.qrefl, ← hcdef, ← hd, ← he, conjTranspose_sub, conjTranspose_one,
      conjTranspose_smul, conjTranspose_vecMulVec, hstar_e, star_inv₀]
  rw [hR, _root_.GlobalTheory.QuadricSection.qrefl, ← hcdef, ← hd, ← he]
  have hexp : (1 - (star c)⁻¹ • vecMulVec (J *ᵥ d) (star d)) * J * (1 - c⁻¹ • vecMulVec d e) =
      J - (c⁻¹ + (star c)⁻¹ - (star c)⁻¹ * c⁻¹ * (e ⬝ᵥ d)) • vecMulVec (J *ᵥ d) e := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, heJ, hJe, hVV,
      smul_smul]
    module
  rw [hexp, hq, ← hsum]
  have hzero : c⁻¹ + (star c)⁻¹ - (star c)⁻¹ * c⁻¹ * (c + star c) = 0 := by
    field_simp
    ring
  rw [hzero, zero_smul, sub_zero]

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.QuadricSection.measurable_qrefl (J : Matrix n n ℂ) (x : n → ℂ) (i j : n) :
    Measurable fun y => _root_.GlobalTheory.QuadricSection.qrefl J x y i j := by
  have hd : Continuous fun y : n → ℂ => x - y := by fun_prop
  have hcoef : Measurable fun y => _root_.GlobalTheory.QuadricSection.coef J x y := by
    refine Continuous.measurable ?_
    unfold _root_.GlobalTheory.QuadricSection.coef
    exact (continuous_star.comp hd).dotProduct continuous_const
  have hvec : Continuous fun y : n → ℂ => vecMulVec (x - y) (star (x - y) ᵥ* J) i j := by
    simp only [vecMulVec_apply]
    refine ((continuous_apply i).comp hd).mul ?_
    exact (continuous_apply j).comp ((continuous_star.comp hd).matrix_vecMul continuous_const)
  simp only [_root_.GlobalTheory.QuadricSection.qrefl, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.sub (hcoef.inv.mul hvec.measurable)

end general

open GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.jpq_conjTranspose (P Q : ℕ) : (_root_.Formalism.UG.Jpq P Q)ᴴ = _root_.Formalism.UG.Jpq P Q := by
  unfold _root_.Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.form_self {P Q : ℕ} (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    star x ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ x) = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x : ℂ) := by
  rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_self, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform]
  unfold _root_.Formalism.UG.hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_add]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.measurable_qf {P Q : ℕ} :
    Measurable (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  refine Continuous.measurable ?_
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf
  fun_prop

open Classical in

def sectMat {P Q : ℕ} (β : ℝ) (x₀ y : Sp P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  if qf y = β then
    (if coef (Formalism.UG.Jpq P Q) x₀ y = 0 then -qrefl (Formalism.UG.Jpq P Q) x₀ (-y)
      else qrefl (Formalism.UG.Jpq P Q) x₀ y)
  else 1

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.qf_neg {P Q : ℕ} (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf (-y) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf
  simp [Complex.normSq_neg]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.sectMat_spec {P Q : ℕ} {β : ℝ} {x₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q}
    (hβ : β ≠ 0) (hx : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β) (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y)ᴴ * _root_.Formalism.UG.Jpq P Q * _root_.GlobalTheory.QuadricSection.sectMat β x₀ y = _root_.Formalism.UG.Jpq P Q ∧
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β → _root_.GlobalTheory.QuadricSection.sectMat β x₀ y *ᵥ x₀ = y) := by
  have hJ := _root_.GlobalTheory.QuadricSection.jpq_conjTranspose P Q
  by_cases hy : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β
  · have hxy : star x₀ ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ x₀) = star y ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ y) := by
      rw [_root_.GlobalTheory.QuadricSection.form_self, _root_.GlobalTheory.QuadricSection.form_self, hx, hy]
    by_cases hc : _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y = 0
    · have hxy' : star x₀ ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ x₀) = star (-y) ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ -y) := by
        rw [hxy, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]
      have hc' : _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ (-y) ≠ 0 := by
        have hsum : _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y +
            _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ (-y) = 2 * (β : ℂ) := by
          rw [← hx, ← _root_.GlobalTheory.QuadricSection.form_self]
          simp only [_root_.GlobalTheory.QuadricSection.coef, sub_neg_eq_add, star_sub, star_add,
            sub_dotProduct, add_dotProduct]
          ring
        rw [hc, zero_add] at hsum
        rw [hsum]
        exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hβ)
      have hsect : _root_.GlobalTheory.QuadricSection.sectMat β x₀ y =
          -_root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ (-y) := by
        simp [_root_.GlobalTheory.QuadricSection.sectMat, hy, hc]
      rw [hsect]
      refine ⟨?_, fun _ => ?_⟩
      · rw [conjTranspose_neg, neg_mul, neg_mul, mul_neg, neg_neg]
        exact _root_.GlobalTheory.QuadricSection.qrefl_unitary _ hJ x₀ (-y) hxy' hc'
      · rw [neg_mulVec, _root_.GlobalTheory.QuadricSection.qrefl_mulVec _ x₀ (-y) hc', neg_neg]
    · have hsect : _root_.GlobalTheory.QuadricSection.sectMat β x₀ y =
          _root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ y := by
        simp [_root_.GlobalTheory.QuadricSection.sectMat, hy, hc]
      rw [hsect]
      exact ⟨_root_.GlobalTheory.QuadricSection.qrefl_unitary _ hJ x₀ y hxy hc,
        fun _ => _root_.GlobalTheory.QuadricSection.qrefl_mulVec _ x₀ y hc⟩
  · have hsect : _root_.GlobalTheory.QuadricSection.sectMat β x₀ y = 1 := by
      simp [_root_.GlobalTheory.QuadricSection.sectMat, hy]
    rw [hsect]
    exact ⟨by simp, fun h => absurd h hy⟩

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.measurable_sectMat {P Q : ℕ} (β : ℝ) (x₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q)
    (i j : Fin P ⊕ Fin Q) :
    Measurable fun y => _root_.GlobalTheory.QuadricSection.sectMat β x₀ y i j := by
  classical
  have hset1 : MeasurableSet {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q | _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β} :=
    _root_.GlobalTheory.QuadricSection.measurable_qf (measurableSet_singleton β)
  have hcoef : Measurable fun y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q =>
      _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y := by
    refine Continuous.measurable ?_
    unfold _root_.GlobalTheory.QuadricSection.coef
    exact (continuous_star.comp (continuous_const.sub continuous_id)).dotProduct continuous_const
  have hset2 : MeasurableSet {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q |
      _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y = 0} :=
    hcoef (measurableSet_singleton 0)
  have heq : (fun y => _root_.GlobalTheory.QuadricSection.sectMat β x₀ y i j) = fun y =>
      if _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β then
        (if _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y = 0 then
          -_root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ (-y) i j
        else _root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ y i j)
      else (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j := by
    funext y
    unfold _root_.GlobalTheory.QuadricSection.sectMat
    split_ifs <;> rfl
  rw [heq]
  refine Measurable.ite hset1 (Measurable.ite hset2 ?_ ?_) measurable_const
  · exact ((_root_.GlobalTheory.QuadricSection.measurable_qrefl _ x₀ i j).comp measurable_neg).neg
  · exact _root_.GlobalTheory.QuadricSection.measurable_qrefl _ x₀ i j

open MeasureTheory Matrix in

theorem _root_.GlobalTheory.QuadricSection.exists_isSection : ∀ (P Q : ℕ) (β : ℝ) (x₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q), β ≠ 0 →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β →
    ∃ s : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → _root_.Formalism.BasicNotions.UpqT P Q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection β x₀ s := by
  intro P Q β x₀ hβ hx
  have hspec := fun y => _root_.GlobalTheory.QuadricSection.sectMat_spec hβ hx y
  have hunit : ∀ y, IsUnit (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y).det := by
    intro y
    refine isUnit_det_of_left_inverse
      (B := _root_.Formalism.UG.Jpq P Q * (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y)ᴴ * _root_.Formalism.UG.Jpq P Q) ?_
    have hU : (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y)ᴴ * (_root_.Formalism.UG.Jpq P Q * _root_.GlobalTheory.QuadricSection.sectMat β x₀ y) =
        _root_.Formalism.UG.Jpq P Q := by
      rw [← Matrix.mul_assoc]
      exact (hspec y).1
    simp only [Matrix.mul_assoc]
    rw [hU, _root_.GlobalTheory.UpqTopology.jpq_sq]
  have hcT : ∀ M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, _root_.Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    unfold _root_.Formalism.UG.cT
    ext i j
    simp [conjTranspose_apply]
  have hmem : ∀ y, Matrix.nonsingInvUnit _ (hunit y) ∈ _root_.Formalism.UG.Upq P Q := by
    intro y
    unfold _root_.Formalism.UG.Upq _root_.Formalism.UG.UJ
    simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    rw [hcT]
    exact (hspec y).1
  refine ⟨fun y => (⟨Matrix.nonsingInvUnit _ (hunit y), hmem y⟩ : _root_.Formalism.UG.Upq P Q), ?_⟩
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection
  refine ⟨?_, ?_⟩
  · letI : MeasurableSpace (_root_.Formalism.BasicNotions.UpqT P Q) := _root_.Formalism.BasicNotions.instMeasurableSpaceUpqT P Q
    haveI : BorelSpace (_root_.Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩
    letI : MeasurableSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := MeasurableSpace.pi
    haveI : BorelSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
      inferInstanceAs (BorelSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
    apply (_root_.GlobalTheory.UpqTopology.isClosedEmbedding_mat.measurableEmbedding.measurable_comp_iff).mp
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact _root_.GlobalTheory.QuadricSection.measurable_sectMat β x₀ i j
  · intro y hy
    exact (hspec y).2 hy

end GlobalTheory.QuadricSection
