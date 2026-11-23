import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverLinkedThetaSystemsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.GSep

theorem exists_uLink_regAt_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : V →+* V₁) (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (r : Fin Cm.m → V₁), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ GlobalTheory.GSep.ULink C X₁ act u π ∧ IsCov C π z₁ ζ ∧ IsCN V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ev₁ ∧ GlobalTheory.GSep.RegAt X₁ z₁ ev₁ ∧ spMap ev₁ ≫ ζ = spMap ρ₁ ≫ ξ ∧ ∀ k, r k ^ 2 = ρ₁ (Cm.s k) := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn ho j₀
  classical
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := GlobalTheory.T.exists_finite_cover_linked_thetaSystems E H Dw hpq l Xo c C n hn ho j₀
  obtain ⟨L, _, _, _, yL, hyL⟩ := GlobalTheory.FinLift.lift_point_finite_surjective (FractionRing V) _ _ Cm.y q hqf hqs
  obtain ⟨X₁, act, u, π, yM, hlink, hrN, ⟨U, g', hg', hgU, hrange⟩, hyM, hreg⟩ := hB L yL
  let G : Polynomial V := ∏ k, (Polynomial.X ^ 2 - Polynomial.C (Cm.s k))
  have hG : G.Monic := Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_pow_sub_C _ two_ne_zero
  obtain ⟨V₁, _, _, _, ρ₁, σ, hV₁, hinj, hfin, hσ, hR⟩ := GlobalTheory.USep.Setup.exists_ext V hV L G hG
  choose r hr₂ using fun k => hR.exists_sq
    (Finset.dvd_prod_of_mem (fun k => Polynomial.X ^ 2 - Polynomial.C (Cm.s k)) (Finset.mem_univ k))
  have hr : Set.range (ξ ≫ pullback.fst _ _ :) ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hrange ⟨ξ p, rfl⟩
  let f : Sp V ⟶ U.toScheme := IsOpenImmersion.lift U.ι _ hr
  have hf : f ≫ U.ι = ξ ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
  have hkey : spMap σ ≫ spMap (algebraMap (FractionRing V) L) ≫ jK V = jK V₁ ≫ spMap ρ₁ := by
    simp only [← Spec.map_comp]
    exact congrArg (fun χ => spMap χ) hσ
  have hcomp : (spMap σ ≫ yM) ≫ g' = jK V₁ ≫ spMap ρ₁ ≫ f := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [hgU, hyM, hf, ← Category.assoc yL, hyL]
    simp only [Category.assoc, UCompact.i]
    rw [← Category.assoc Cm.y, hξ]
    simp only [Category.assoc]
    rw [reassoc_of% hkey]
  obtain ⟨z₁, ev, hloc, hev, hev2⟩ := GlobalTheory.FiniteLift.exists_stalk_lift V₁ hV₁.1.2.2.1 X₁.M.Z U.toScheme g' hg'
    (spMap ρ₁ ≫ f) (spMap σ ≫ yM) hcomp
  have hev' : spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = (spMap ρ₁ ≫ ξ) ≫ pullback.fst _ _ := by
    rw [← hgU, reassoc_of% hev, hf, Category.assoc]
  haveI := hloc
  obtain ⟨ζ, hζ⟩ := GlobalTheory.USep.Setup.exists_lift_genericFibre C ev _ _ hev'
  haveI : IsPreimmersion (spMap C.b) := by
    letI : Algebra C.o c.F := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hgen : ∀ p : Sp (X₁.M.Z.presheaf.stalk z₁), p.asIdeal = ⊥ → ζ p ∈ Set.range C.iF := by
    intro p hp
    have hpt := hlink.2.2.2
    have h1 : π (genericPoint X₁.M.Z) =
        (pullback.fst C.z (spMap C.b)) (C.iF (u (spMap (ratHull X₁.S.R).val.toRingHom (closedPoint X₁.Ω₁)))) := by
      rw [← X₁.M.pt_apply (closedPoint X₁.Ω₁)]
      exact congrArg (fun χ : Sp X₁.Ω₁ ⟶ C.Z => χ (closedPoint X₁.Ω₁)) hpt
    refine ⟨u (spMap (ratHull X₁.S.R).val.toRingHom (closedPoint X₁.Ω₁)),
      (pullback.fst C.z (spMap C.b)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply ζ, hζ, Scheme.Hom.comp_apply, GlobalTheory.USep.Setup.fromSpecStalk_bot z₁ p hp, h1]
  refine ⟨j, X₁, act, u, π, z₁, ζ, V₁, inferInstance, inferInstance, inferInstance, ρ₁, ev, r, hj, hrN, hlink,
    ⟨X₁.normal, ⟨U, g', hg', hgU, hrange⟩, hζ, hgen⟩, ⟨hV₁.1.1, hV₁.1.2.2.1, hV₁.1.2.2.2, hV₁.2⟩, hinj, hfin, hloc, ?_, ?_, hr₂⟩
  · intro a ha
    rw [hev2]
    convert hreg a ha using 2
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg yM (Subsingleton.elim (α := PrimeSpectrum L) _ _))
  · rw [← cancel_mono (pullback.fst C.z (spMap C.b)), Category.assoc, hζ, hev']

end GlobalTheory.GSep
