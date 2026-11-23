import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlagStatement

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Glob.MinParLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_block_of_triangular {n r s : ℕ} (X : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (hs : s ≤ r)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (show Fin.castLE hs j < Fin.castLE hs i from Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hs j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F X) x (Fin.castLE hs j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    have hz : B i (Fin.castLE hs j) = 0 :=
      hB (show Fin.castLE hs j < i by rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega)
    rw [hz, mul_zero]

theorem minPar_eq_unip_mul_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S p hp
  obtain ⟨s, hs, hS⟩ : ∃ s, ∃ hs : s ≤ r, ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := by
    refine ⟨S.sup fun k => k.val + 1, Finset.sup_le fun k _ => k.2, fun i => ?_⟩
    rw [Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS
    (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl
  have hp' : p ∈ parFlag σ J (X.submatrix id (Fin.castLE hs))
      (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) := by
    obtain ⟨B, hB, e⟩ := hp
    obtain ⟨B', hB', e'⟩ := PositivityTheory.ThKR.inv_mem_minPar h hJ hW (show p ∈ PositivityTheory.ThKR.minPar σ J X from ⟨B, hB, e⟩)
    exact ⟨exists_block_of_triangular X S hs hB e, exists_block_of_triangular X S hs hB' e'⟩
  obtain ⟨u, hu', m, hm, e, -⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 p hp'
  exact ⟨u, hu ▸ hu', m, hl ▸ hm, e⟩

end GlobalTheory.CompanionTheory.Glob.MinParLevi
