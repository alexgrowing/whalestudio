import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem exists_splitExt_of_galois_invariant :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  intro k K _ _ _ _ _ G₀ B₀ _ _ _ hB₀ G B _ _ X _ _ _ φG φ hG hB q i hq hfl hsu hqc hi H hinv
  have hc := GlobalTheory.ZM.DwModel.isGaloisCover_field k K
  let s : (K ≃ₐ[k] K) → (G.left ⟶ G.left) := fun τ =>
    hG.1.lift φG (G.hom ≫ spMap (τ : K →+* K)) (by rw [Category.assoc, hc.inv, hG.1.w])
  have hs₁ : ∀ τ, s τ ≫ φG = φG := fun τ => hG.1.lift_fst _ _ _
  have hs₂ : ∀ τ, s τ ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) := fun τ => hG.1.lift_snd _ _ _
  have hcG := hc.of_isPullback (ρ' := s) hG.1.flip hs₂ hs₁
  have hT := SplitTorus.isPullback_bcMap (spMap (algebraMap k K)) X
  have hcT := hc.of_isPullback
    (ρ' := fun τ : K ≃ₐ[k] K => SplitTorus.bcMap (spMap (τ : K →+* K)) X) hT.flip
    (fun τ => SplitTorus.bcMap_hom _ X) (fun τ => pullback.hom_ext
      (by
        have e := SplitTorus.bcMap_torusFst (spMap (algebraMap k K)) X
        exact (Category.assoc _ _ _).trans ((congrArg _ e).trans
          ((SplitTorus.bcMap_torusFst _ X).trans e.symm)))
      (by
        have e := SplitTorus.bcMap_hom (spMap (algebraMap k K)) X
        refine (Category.assoc _ _ _).trans ((congrArg _ e).trans (Eq.trans ?_ e.symm))
        rw [SplitTorus.bcMap_hom_assoc, hc.inv]))
  obtain ⟨q', hq', -⟩ := hcG.existsUnique_desc (q.left ≫ φ) fun τ => (hinv τ _ (hs₁ τ) (hs₂ τ)).1
  obtain ⟨i', hi', -⟩ := hcT.existsUnique_desc (i.left ≫ φG) fun τ => by
    rw [← Category.assoc, (hinv τ _ (hs₁ τ) (hs₂ τ)).2, Category.assoc, hs₁]
  have wq : q' ≫ B₀.hom = G₀.hom :=
    (hcG.existsUnique_desc (φG ≫ G₀.hom) fun τ => by rw [← Category.assoc, hs₁]).unique
      (by rw [← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]) rfl
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom :=
    (hcT.existsUnique_desc (SplitTorus.bcMap (spMap (algebraMap k K)) X ≫ (splitTorus (Sp k) X).hom)
      fun τ => by rw [← Category.assoc, hcT.inv]).unique
      (by rw [← Category.assoc, hi', Category.assoc, hG.1.w, ← Category.assoc, Over.w, hT.w]) rfl
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' hq hfl hsu hqc hi H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _
    h₁ h₅ h₂ h₃ h₄ h₆
  obtain ⟨d, -⟩ := h hB₀
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory
