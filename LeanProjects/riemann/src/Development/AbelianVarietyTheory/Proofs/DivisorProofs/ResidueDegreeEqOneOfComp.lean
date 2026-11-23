import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt GlobalTheory.VB GlobalTheory.GenSmoothCover

namespace GlobalTheory.GenRes

theorem bijective_residueFieldMap {A B : Scheme.{0}} (f : A ⟶ B) [SurjectiveOnStalks f] (x : A) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := A.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨B.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩

theorem residueDegree_eq_one_of_comp {A B C : Scheme.{0}} (g : A ⟶ B) (c : B ⟶ C) (a : A)
    (h : Function.Bijective ((g ≫ c).residueFieldMap a).hom) : c.residueDegree (g a) = 1 := by
  rw [Scheme.residueFieldMap_comp] at h
  have hs : Function.Surjective (c.residueFieldMap (g a)).hom := fun y => by
    obtain ⟨x, hx⟩ := h.2 ((g.residueFieldMap a).hom y)
    exact ⟨x, (g.residueFieldMap a).hom.injective hx⟩
  have hb : Function.Bijective (c.residueFieldMap (g a)).hom := ⟨RingHom.injective _, hs⟩
  letI := (c.residueFieldMap (g a)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  exact (LinearEquiv.finrank_eq (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).toLinearEquiv).symm.trans
    (Module.finrank_self _)

theorem exists_birational_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X),
      IsArithVar (ρ ≫ p) d ∧ GenSmooth (ρ ≫ p) d ∧ ρ (genericPoint Y) = genericPoint X ∧
        ρ.residueDegree (genericPoint Y) = 1 := by
  intro hP k _ X _ p D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ‹_›, ρ, hA, fun σ => ?_, ?_, ?_⟩
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have : SurjectiveOnStalks (((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ) := by rw [e]; infer_instance
    rw [← eη]
    exact residueDegree_eq_one_of_comp _ ρ _ (bijective_residueFieldMap _ _)

end GlobalTheory.GenRes
