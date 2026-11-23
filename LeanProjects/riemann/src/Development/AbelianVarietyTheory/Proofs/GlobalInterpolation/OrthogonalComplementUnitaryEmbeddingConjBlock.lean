import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

noncomputable section

namespace GlobalTheory.CompactDualQuot.PerpConj

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

theorem jpq_apply (a b : Fin P ⊕ Fin Q) :
    Formalism.UG.Jpq P Q a b = if a = b then (sg a : ℂ) else 0 := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, sg, Matrix.one_apply]
  all_goals (split_ifs <;> simp)

theorem herm_eq_sum (x y : Sp P Q) : herm x y = ∑ i, (sg i : ℂ) * (x i * star (y i)) := by
  simp [herm, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem herm_swap (x y : Sp P Q) : herm y x = star (herm x y) := by
  simp [herm_eq_sum, mul_comm]

theorem gram_apply (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i l : Fin P ⊕ Fin Q) :
    (uᴴ * Formalism.UG.Jpq P Q * u) i l = herm (fun a => u a l) (fun a => u a i) := by
  simp only [Matrix.mul_apply, jpq_apply, herm_eq_sum, conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem herm_single (a b : Fin P ⊕ Fin Q) :
    herm (Pi.single b 1 : Sp P Q) (Pi.single a 1) = if a = b then (sg a : ℂ) else 0 := by
  rw [herm_eq_sum, Finset.sum_eq_single a]
  · by_cases h : a = b <;> simp [h]
  · intro c _ hc; simp [hc]
  · simp

theorem perp_conj : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ →
    ∀ (x₀ : Sp P Q) (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q),
    qf x₀ = sg (e none) → IsPerpEmb x₀ A j →
    ∃ g₀ : UpqT P Q, act g₀ (baseVec e) = x₀ ∧ ∀ g, j g = g₀ * j₀ g * g₀⁻¹ := by
  intro P Q P' Q' e he j₀ hj₀ x₀ A j hx ⟨h1, h2, h3⟩
  let u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    Matrix.of fun a l => (e.symm l).elim (x₀ a) (fun b => A a b)
  have un : ∀ a, u a (e none) = x₀ a := fun a => by simp [u]
  have us : ∀ a b, u a (e (some b)) = A a b := fun a b => by simp [u]
  have cn : (fun a => u a (e none)) = x₀ := funext un
  have cs : ∀ b, (fun a => u a (e (some b))) = A *ᵥ Pi.single b 1 := fun b => by
    funext a; simp [us]
  have hu : u ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    ext i l
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective l
    rw [gram_apply, jpq_apply]
    rcases i with _ | i <;> rcases l with _ | l
    · rw [cn, herm_self, hx, if_pos rfl]
    · rw [cn, cs, (h2 _).2 ⟨_, rfl⟩, if_neg (by simp)]
    · rw [cn, cs, herm_swap, (h2 _).2 ⟨_, rfl⟩, if_neg (by simp), star_zero]
    · rw [cs, cs, h1, herm_single, he i]
      simp
  obtain ⟨g₀, hg₀⟩ := hu
  refine ⟨g₀, ?_, fun g => ?_⟩
  · funext a
    simp [act, baseVec, hg₀, un]
  · rw [eq_mul_inv_iff_mul_eq]
    apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
    change UpqT.mat (j g) * UpqT.mat g₀ = UpqT.mat g₀ * UpqT.mat (j₀ g)
    rw [hg₀]
    obtain ⟨b1, b2, b3, b4⟩ := hj₀ g
    ext a l
    obtain ⟨l, rfl⟩ := e.surjective l
    rw [Matrix.mul_apply (M := u), ← e.sum_comp, Fintype.sum_option]
    rcases l with _ | l
    · have := congrFun (h3 g).1 a
      simp only [b1, b3, un, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← this]
      simp [act, Matrix.mul_apply, Matrix.mulVec, dotProduct, un]
    · have := congrFun ((h3 g).2 (Pi.single l 1)) a
      simp only [b2, b4, us, mul_zero, zero_add]
      simp only [act, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, us] using this

end GlobalTheory.CompactDualQuot.PerpConj
