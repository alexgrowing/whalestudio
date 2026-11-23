import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCxAlg

variable {D : D7}

theorem actC_actC (V W : HSp D) (g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h h' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (x : WC V W) :
    actC V W g h (actC V W g' h' x) = actC V W (g * g') (h * h') x := by
  unfold actC
  split_ifs <;> simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actC_smul (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (c : ℂ) (x : WC V W) :
    actC V W g h (c • x) = c • actC V W g h x := by
  unfold actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem actC_one (V W : HSp D) (x : WC V W) : actC V W 1 1 x = x := by
  unfold actC
  split_ifs <;> simp

theorem hC_actC (V W : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ)
    (hh : hᴴ * gramAt D W τ * h = gramAt D W τ) (x y : WC V W) :
    hC V W τ (actC V W g h x) (actC V W g h y) = hC V W τ x y := by
  unfold hC actC
  split_ifs with hr
  · rw [GlobalTheory.DualPairCheck.sum_small, GlobalTheory.DualPairCheck.sum_small]
    exact GlobalTheory.DualPairCheck.inv_small (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y
  · rw [GlobalTheory.DualPairCheck.sum_large, GlobalTheory.DualPairCheck.sum_large]
    exact GlobalTheory.DualPairCheck.inv_large (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y

theorem I_smul_unitary {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : tᴴ * G * t = G) :
    (Complex.I • t)ᴴ * G * (Complex.I • t) = G := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]
  simp

theorem cx_alg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  intro D V W τ s s' hV hW
  refine ⟨fun x => ?_, fun x y => ?_, fun g h hg hh x => ?_, ?_⟩
  · unfold jAt
    rw [actC_smul, actC_actC, hV.1, hW.1, actC_one, smul_smul, Complex.I_mul_I, neg_one_smul]
  · unfold symplC jAt
    rw [hC_smul_left, hC_smul_right, hC_actC V W τ _ _ hV.2.1 hW.2.1, ← mul_assoc (starRingEnd ℂ Complex.I),
      Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  · unfold jAt
    rw [actC_smul, actC_actC, actC_actC, hg.eq, hh.eq]
  · by_cases hr : V.rank ≤ W.rank
    · refine ⟨thAt V τ s, ⟨hV.2.1, rfl⟩, Complex.I • thAt W τ s',
        ⟨I_smul_unitary hW.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_pos hr, if_pos hr, Matrix.transpose_smul, Matrix.mul_smul]
    · refine ⟨Complex.I • thAt V τ s,
        ⟨I_smul_unitary hV.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, thAt W τ s', ⟨hW.2.1, rfl⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_neg hr, if_neg hr, Matrix.smul_mul, Matrix.smul_mul]

end GlobalTheory.FockCxAlg
