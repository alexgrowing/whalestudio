import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangentBound

def acts (W : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ
  | .inl uv => Matrix.single uv.1 uv.2 1
  | .inr true => (W + W.transpose).adjugate * W
  | .inr false => (W + W.transpose).adjugate * W.transpose

theorem main : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro h n _ h3 hodd K _ _ r β c hc hun
  have hn : n ≠ 0 := by omega
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W, hW, hbasAll⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hbasAll h
  have hζ : (cycBase hn).ζ ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, cycBase_ζ]
    exact Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
  have hdet : (W + W.transpose).det = 1 := hW.2
  have hw : (W + W.transpose) * acts W (.inr true) = W := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have hw' : (W + W.transpose) * acts W (.inr false) = W.transpose := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have he : ∀ u v : Fin 8, ∃ j, acts W j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c hodd h3 hζ hc
  refine GlobalTheory.PowerTangent.main L1 L2 GlobalTheory.Moduli.cube_of_isLB h (8 * h) W _ (acts W) bas hW hbas (.inr true) (.inr false)
    hw hw' n (cycAway n) (cycBase hn) K r β t c hc ht ?_
  intro lam t' m₁ m₂
  have hf : spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      spMap ((algebraMap K (DualNumber K)).comp β) ≫ spMap (RingHom.id (cycAway n)) := by
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => by
      simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).1 c
  have hc'P := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).2.1 c c' hc' hc
  obtain ⟨t'', ht''⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c' hodd h3 hζ hc'P
  have m₃ : TMap t'' t (spMap (dirMap lam)) :=
    (GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
      (spMap (dirMap lam)) hc hc'P ht ht'').1 hc'
  have m₄ : TMap t'' t' (𝟙 _) :=
    ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₁).2 (by rwa [Category.id_comp])
  have m₅ : TMap t'' t (constPt (spMap (dirMap lam))) := by
    have := ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₂).1 m₄
    rwa [Category.id_comp] at this
  exact hun lam c' hc' ((GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
    _ hc hc'P ht ht'').2 he m₅)

end GlobalTheory.SiegelTangentBound
end
