import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sum_Icc_one_eq_sum_fin (f : ℕ → ℤ) : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, f i = ∑ r : Fin n, f (r.val + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_one_eq_sum_fin f n, Fin.sum_univ_castSucc]
    simp

theorem size_first_last_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  intro p _ X D pos j hN ν hν
  have hle : D.R.N j ≤ D.R.N (j + 1) := rk_le X D hN
  have hz : ∀ τ (i : ℕ), D.R.N j < i → X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 i = 0 := fun τ i hi =>
    nuv_zero X _ j _ i (hN.1 ▸ hi)
  have hext : NuIs X D pos j (extNu (D.R.N (j + 1)) ν) := by
    intro τ i
    unfold extNu
    split_ifs with h
    · exact hν τ ⟨i.val, h⟩
    · rw [hz τ _ (by omega)]; simp
  have hsz : ∀ τ, szT X D pos j τ = ∑ i ∈ Finset.Icc 1 (D.R.N (j + 1)), X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 i := by
    intro τ
    unfold szT szMu
    rw [hN.2]
  refine ⟨hext, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hsz τ, ← Finset.sum_subset (Finset.Icc_subset_Icc_right hle) (fun i hi hni => by
      simp only [Finset.mem_Icc] at hi hni
      exact hz τ i (by omega)), sum_Icc_one_eq_sum_fin]
    exact Finset.sum_congr rfl fun r _ => hν τ r
  · intro τ
    rw [hsz τ, sum_Icc_one_eq_sum_fin]
    exact Finset.sum_congr rfl fun r _ => hext τ r
  · intro τ r
    rw [← hext τ r]
    exact nuv_le_first X _ j _ _
  · intro τ
    exact nuv_nonneg X _ j _ _

end GlobalTheory.TwV.DelA
