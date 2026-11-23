import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameUnipotentLeFlagUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSubgroupLeGradedIsotropicFlagLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIsotropicFlagLeviLeLeviSubgroupStatement

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

def leftStab {G : Type} [Group G] (φ : G → ℂ) : Subgroup G where
  carrier := {γ | ∀ g, φ (γ * g) = φ g}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

theorem stdPar_eq_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ∧ GlobalTheory.StdPar.levi σ J X Y S = GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ∧ ∀ (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ ↔ GlobalTheory.UAut.IsAutOn σ J (GlobalTheory.UAut.leftGrp σ J (X.submatrix id (Fin.castLE hs)) d) K φ := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have hu := le_antisymm (GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.unipotent_radical_graded_isotropic_flag_le F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hl := le_antisymm (GlobalTheory.T.leviSubgroup_le_gradedIsotropicFlagLevi F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).2.2.1
  refine ⟨hu, hl, fun K φ => ⟨fun hφ => ⟨?_, hφ.level, hφ.cont, hφ.smooth, hφ.growth, GlobalTheory.UAut.kfin_iff.1 hφ.kfin, hφ.zfin⟩,
    fun hφ => ⟨fun u hu' g => hφ.left u ?_ g, fun γ hγ hγ' g => hφ.left γ ?_ g, hφ.level, hφ.cont, hφ.smooth, hφ.growth,
      GlobalTheory.UAut.kfin_iff.2 hφ.kfin, hφ.zfin⟩⟩⟩
  · rw [hg]
    have : GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ⊔ (ratPts σ J ⊓ GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d) ≤ leftStab φ :=
      sup_le (fun u hu' => hφ.leftN u (hu ▸ hu')) (fun γ hγ => hφ.leftM γ hγ.1 (hl ▸ hγ.2))
    exact fun γ hγ => this hγ
  · rw [hg]; exact Subgroup.mem_sup_left (hu ▸ hu')
  · rw [hg]; exact Subgroup.mem_sup_right ⟨hγ, hl ▸ hγ'⟩

end GlobalTheory.TieStd
