import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem sum_pullMat_subBG_reframe : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  intro D p _ X E pos fd lam ι hι ρ hL e c j La La' he he' hdet x y
  classical
  have hs : ∀ q : D.host.E, star q = D.host.conj q := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hcc : ∀ q : D.host.E, D.host.conj (D.host.conj q) = q := fun q => D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])
  have hconj : ∀ τ q, TaylorLogMetric.embT D τ (D.host.conj q) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ q) := fun τ q =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) q
  have hιe : ∀ τ q, ι (TaylorLogMetric.embT D τ q) = twG X E (pos.symm τ).1 (pos.symm τ).2
      (ρ _ (if IsOddPos (pos.symm τ).2 then D.host.conj q else q)) := by
    intro τ q
    have halg : TaylorLogMetric.embT D τ q ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) q).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
    have h2 := hL (pos.symm τ).1 (pos.symm τ).2 q
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h2
    rw [← h2]; unfold TaylorLogMetric.lamC; rw [dif_pos halg]; exact hι ⟨_, halg⟩
  have hinv : ∀ {n : ℕ} (v : X.Pl) (A : Matrix (Fin n) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin n) (X.G.P.Qq v)),
      A * star A = 1 → ((star A).map (ρ v) * M)⁻¹ = M⁻¹ * A.map (ρ v) := by
    intro n v A M h
    rw [Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero (ρ v)) (map_one (ρ v))]
  obtain ⟨τ, b0, a0⟩ := x
  obtain ⟨τ', b1, a1⟩ := y
  by_cases hxy : τ = τ'
  · subst hxy
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · rw [Fintype.sum_prod_type]
      simp only [subBG, reframe, pullMat, ↓reduceIte]
      rw [hinv _ _ _ he, hinv _ _ _ he']
      by_cases hodd : IsOddPos (pos.symm τ).2
      · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
        first
          | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
        first
          | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    · intro τ'' _ hne
      apply Finset.sum_eq_zero
      intro z _
      simp [pullMat, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [show subBG E pos (reframe fd ρ e) j La La' (τ, b0, a0) (τ', b1, a1) = 0 from if_neg hxy, mul_zero]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : τ = z.1
    · have h2 : z.1 ≠ τ' := fun h => hxy (h1.trans h)
      rw [show subBG E pos fd j La La' z (τ', b1, a1) = 0 from if_neg h2, mul_zero, mul_zero]
    · rw [show pullMat (e j La) (e (j + 1) La') (τ, b0, a0) z = 0 from if_neg h1, map_zero, zero_mul]

end GlobalTheory.TwV.DelB
