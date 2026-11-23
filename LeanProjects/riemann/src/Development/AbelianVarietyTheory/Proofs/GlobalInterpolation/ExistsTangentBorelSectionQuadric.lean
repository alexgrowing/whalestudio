import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric

noncomputable section

namespace GlobalTheory.TangentSection

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot GlobalTheory.QuadricSection

variable {P Q P' Q' : ℕ}

theorem jpq_eq_diagonal (P Q : ℕ) :
    Formalism.UG.Jpq P Q = diagonal fun i : Fin P ⊕ Fin Q => ((sg i : ℝ) : ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, sg, diagonal_apply, Matrix.one_apply]
  all_goals split_ifs <;> simp

theorem norm_sg (i : Fin P ⊕ Fin Q) : ‖((sg i : ℝ) : ℂ)‖ = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

def flipAt (k : Fin P ⊕ Fin Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  diagonal fun i => if i = k then 1 else -1

theorem flipAt_unitary (k : Fin P ⊕ Fin Q) :
    (flipAt k)ᴴ * Formalism.UG.Jpq P Q * flipAt k = Formalism.UG.Jpq P Q := by
  rw [jpq_eq_diagonal, flipAt, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = k <;> simp [h]

theorem flipAt_mulVec (k : Fin P ⊕ Fin Q) :
    flipAt k *ᵥ (Pi.single k 1 : Sp P Q) = Pi.single k 1 := by
  funext i
  rw [flipAt, mulVec_diagonal]
  by_cases h : i = k <;> simp [h]

theorem coef_single (k : Fin P ⊕ Fin Q) (y : Sp P Q) :
    coef (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) = star (1 + y k) * (sg k : ℂ) := by
  rw [coef, jpq_eq_diagonal, dotProduct, Finset.sum_eq_single k]
  · simp [mulVec_diagonal]
  · intro b _ hb; simp [mulVec_diagonal, hb]
  · simp

theorem coef_single_ne (k : Fin P ⊕ Fin Q) (y : Sp P Q) (hy : y k ≠ -1) :
    coef (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) ≠ 0 := by
  rw [coef_single]
  refine mul_ne_zero (star_ne_zero.2 fun h => hy ?_) (by exact_mod_cast sg_ne_zero k)
  linear_combination h

theorem qf_single (k : Fin P ⊕ Fin Q) : qf (Pi.single k 1 : Sp P Q) = sg k := by
  rw [qf_eq_sum, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

open Classical in

def tanMat (k : Fin P ⊕ Fin Q) (y : Sp P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  if qf y = sg k ∧ y k ≠ -1 then -qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) * flipAt k
  else sectMat (sg k) (Pi.single k 1) y

theorem tanMat_spec (k : Fin P ⊕ Fin Q) (y : Sp P Q) :
    (tanMat k y)ᴴ * Formalism.UG.Jpq P Q * tanMat k y = Formalism.UG.Jpq P Q ∧
      (qf y = sg k → tanMat k y *ᵥ (Pi.single k 1 : Sp P Q) = y) := by
  unfold tanMat
  split_ifs with h
  · have hc := coef_single_ne k y h.2
    have hu := qrefl_unitary _ (jpq_conjTranspose P Q) (Pi.single k 1) (-y)
      (by rw [form_self, form_self, qf_neg, qf_single, h.1]) hc
    refine ⟨?_, fun _ => ?_⟩
    · rw [neg_mul, conjTranspose_neg, neg_mul, neg_mul_neg, conjTranspose_mul]
      calc _ = (flipAt k)ᴴ * ((qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y))ᴴ * Formalism.UG.Jpq P Q *
            qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y)) * flipAt k := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu, flipAt_unitary]
    · rw [← mulVec_mulVec, flipAt_mulVec, neg_mulVec, qrefl_mulVec _ _ _ hc, neg_neg]
  · exact sectMat_spec (sg_ne_zero k) (qf_single k) y

theorem measurable_tanMat (k i j : Fin P ⊕ Fin Q) : Measurable fun y => tanMat k y i j := by
  classical
  have : (fun y => tanMat k y i j) = fun y => if qf y = sg k ∧ y k ≠ -1 then
      -qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) i j * (if j = k then 1 else -1)
      else sectMat (sg k) (Pi.single k 1) y i j := by
    funext y
    unfold tanMat
    by_cases h : qf y = sg k ∧ y k ≠ -1
    · rw [if_pos h, if_pos h, flipAt, mul_diagonal]; rfl
    · rw [if_neg h, if_neg h]
  rw [this]
  refine Measurable.ite ?_
    (((measurable_qrefl _ _ i j).comp measurable_neg).neg.mul measurable_const)
    (measurable_sectMat _ _ i j)
  have h2 : MeasurableSet ((fun y : Sp P Q => y k) ⁻¹' ({-1} : Set ℂ)ᶜ) :=
    (measurable_pi_apply k) (measurableSet_singleton (-1 : ℂ)).compl
  exact (measurable_qf (measurableSet_singleton (sg k))).inter h2

theorem tanMat_sub_one (k i b : Fin P ⊕ Fin Q) (y : Sp P Q) (h1 : qf y = sg k) (h2 : y k ≠ -1)
    (hb : b ≠ k) :
    ‖(tanMat k y - 1) i b‖ = ‖(Pi.single k 1 : Sp P Q) i + y i‖ * ‖y b‖ / ‖1 + y k‖ := by
  have : (tanMat k y - 1) i b = -((star (1 + y k) * (sg k : ℂ))⁻¹ *
      (((Pi.single k 1 : Sp P Q) i + y i) * (star (y b) * (sg b : ℂ)))) := by
    rw [tanMat, if_pos ⟨h1, h2⟩, Matrix.sub_apply, flipAt, mul_diagonal, if_neg hb, qrefl,
      coef_single]
    simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, jpq_eq_diagonal, vecMul_diagonal, Pi.star_apply, Pi.add_apply,
      Pi.single_eq_of_ne hb, sub_neg_eq_add, zero_add]
    ring
  rw [this]
  simp only [norm_neg, norm_mul, norm_inv, norm_star, norm_sg, mul_one]
  ring

theorem exists_tangent_section : ∀ (P Q P' Q' : ℕ)
    (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), ∃ σ : Sp P Q → UpqT P Q,
    IsSection (sg (e none)) (baseVec e) σ ∧ ∀ y : Sp P Q, qf y = sg (e none) → y (e none) ≠ -1 →
      (∀ b, ‖UpqT.mat (σ y) (e none) (e (some b))‖ = ‖y (e (some b))‖) ∧
      ∀ a b, ‖(UpqT.mat (σ y) - 1) (e (some a)) (e (some b))‖ =
        ‖y (e (some a))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖ := by
  intro P Q P' Q' e
  have hex : ∀ y, ∃ g : UpqT P Q, UpqT.mat g = tanMat (e none) y := fun y => by
    have : tanMat (e none) y ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
      rw [GlobalTheory.UpqTopology.range_mat]; exact (tanMat_spec _ y).1
    exact this
  choose s hs using hex
  have hne : ∀ b, e (some b) ≠ e none := fun b h => by simpa using e.injective h
  refine ⟨s, ⟨?_, fun y hy => ?_⟩, fun y h1 h2 => ⟨fun b => ?_, fun a b => ?_⟩⟩
  · have : BorelSpace (UpqT P Q) := (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
    have he : MeasurableEmbedding
        (β := (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) (UpqT.mat (P := P) (Q := Q)) :=
      Topology.IsClosedEmbedding.measurableEmbedding
        (β := (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) GlobalTheory.UpqTopology.isClosedEmbedding_mat
    refine he.measurable_comp_iff.1 ?_
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simpa only [Function.comp, hs] using measurable_tanMat (e none) i j
  · rw [act, hs]; exact (tanMat_spec _ y).2 hy
  · have h := tanMat_sub_one (e none) (e none) (e (some b)) y h1 h2 (hne b)
    rw [Matrix.sub_apply, Matrix.one_apply_ne (hne b).symm, sub_zero, Pi.single_eq_same] at h
    have h0 : ‖1 + y (e none)‖ ≠ 0 := norm_ne_zero_iff.2 fun h => h2 (by linear_combination h)
    rw [hs, h]
    field_simp
  · rw [hs, tanMat_sub_one (e none) _ _ y h1 h2 (hne b), Pi.single_eq_of_ne (hne a), zero_add]

end GlobalTheory.TangentSection
