import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfIdModEpsThickeningStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstKOfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_locDerK :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro hL K _ A₀ _ R _ xD A _ A' _ ψ j d hA₀ hA' hψ hj hd

  have hra : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of K)
    ext x
    simp
  have : Flat A₀.hom := inferInstance

  have hρ : IsPullback (pullback.fst A₀.hom (spMap (algebraMap K (DualNumber K)))) (pullback.snd _ _)
      A₀.hom (spMap (algebraMap K (DualNumber K))) := IsPullback.of_hasPullback _ _
  obtain ⟨j₀, hj₀ρ, hj₀π⟩ : ∃ j₀ : A₀.left ⟶ pullback A₀.hom (spMap (algebraMap K (DualNumber K))),
      j₀ ≫ pullback.fst _ _ = 𝟙 _ ∧
        j₀ ≫ pullback.snd _ _ = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
    ⟨pullback.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
      (by rw [Category.assoc, hra, Category.comp_id, Category.id_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hj₀ : IsPullback j₀ A₀.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K))))
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hj₀π hρ
    rw [hj₀ρ, hra]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

  have hm : (j ≫ ψ) ≫ A.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hΦj, hΦp, -⟩ := DerMorK.exists_hom_of_derivation K A₀.left _ A₀.hom (pullback.snd _ _)
    (pullback.fst _ _) j₀ hρ hj₀ρ hj₀π R xD A.left A.hom (j ≫ ψ) d hm hd

  obtain ⟨e, heψ, heh⟩ : ∃ e : pullback A₀.hom (spMap (algebraMap K (DualNumber K))) ⟶ A'.left,
      e ≫ ψ = Φ ∧ e ≫ A'.hom = pullback.snd _ _ :=
    ⟨hψ.1.lift Φ _ hΦp, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have hje : j₀ ≫ e = j := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, heψ, hΦj]
    · rw [Category.assoc, heh, hj₀π, hj.1.w]

  have : IsIso e := GlobalTheory.T.isIso_of_id_mod_eps_thickening K A₀.left _ A'.left A₀.hom (pullback.snd _ _) A'.hom j₀ j e hj₀ hj.1
    inferInstance heh hje
  refine exists_isConstK_of_isPullback hL K A₀ A' (inv e ≫ pullback.fst _ _) j hA₀ hA' hj ?_ ?_
  · have h1 : IsPullback (inv e) A'.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K)))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heh]⟩
    have h2 := h1.paste_horiz hρ
    rwa [Category.id_comp] at h2
  · rw [← hje, Category.assoc, IsIso.hom_inv_id_assoc, hj₀ρ]

end GlobalTheory.KS
