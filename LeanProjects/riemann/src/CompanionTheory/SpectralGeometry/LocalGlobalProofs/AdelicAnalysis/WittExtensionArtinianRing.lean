import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianDiagonalizeOverReducedTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLaws
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionDiagonalGramTuples
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitChoiceOfIsArtinianRingIsReduced

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittTuples

theorem exists_actW_eq_of_gramR_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = gramR R σ J Y → IsUnit (gramR R σ J X).det → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ n X Y hXY hdet
  have hσ := HermTop.sigma_sigma hCM
  have hS : cT (sigR R σ) (gramR R σ J X) = gramR R σ J X := by
    ext a b
    exact HermTop.gramR_mem (R := R) hσ hJ.1 X a b
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.exists_diagonal_congr F E σ hCM R n _ hS hdet
  have hgram : ∀ Z : Fin n → Fin M → R ⊗[F] E, gramR R σ J (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J Z * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    fun Z => (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g 1).1
  have hX' := (hgram X).trans hg
  have hY' : gramR R σ J (rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      gramR R σ J (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    rw [hgram, hgram, hXY]
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag F E σ hCM R (GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced R) M J hJ n D _ _ hX' hY'
  refine ⟨h, ?_⟩
  have hk : actTup R (HA.mat R σ J h) (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      rmul R (actTup R (HA.mat R σ J h) X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J X g 1).2.2.2 _
  have he : rmul R (actW R σ J h X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := hk.symm.trans hh
  have hcancel : ∀ Z : Fin n → Fin M → R ⊗[F] E,
      rmul R (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Z := by
    intro Z
    have h1 := GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [h1.2.1, Units.mul_inv, h1.2.2.1]
  rw [← hcancel (actW R σ J h X), he, hcancel]

end GlobalTheory.CompanionTheory.SW.WittTuples
