import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.GoodOpenFree

theorem exists_free_away {A M : Type} [CommRing A] [CommRing M] [IsDomain A] [IsDomain M]
    [IsNoetherianRing A] [Algebra A M] [Module.Finite A M]
    (hinj : Function.Injective (algebraMap A M)) (p : Ideal A) [p.IsPrime]
    (hic : IsIntegrallyClosed (Localization.AtPrime p))
    (hd : ringKrullDim (Localization.AtPrime p) ≤ 1) :
    ∃ g ∉ p, Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  let Mp := Localization (Algebra.algebraMapSubmonoid M p.primeCompl)
  have hle : Algebra.algebraMapSubmonoid M p.primeCompl ≤ nonZeroDivisors M := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => ha ?_
    have : a = 0 := hinj (by simpa using h)
    simp [this]
  haveI : IsDomain Mp := IsLocalization.isDomain_localization hle
  have hinj' : Function.Injective (algebraMap (Localization.AtPrime p) Mp) :=
    localizationAlgebra_injective _ _ hinj
  haveI : IsLocalizedModule p.primeCompl (IsScalarTower.toAlgHom A M Mp).toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  haveI : Module.Finite (Localization.AtPrime p) Mp :=
    Module.Finite.of_isLocalizedModule p.primeCompl (IsScalarTower.toAlgHom A M Mp).toLinearMap
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  haveI : Module.Free (Localization.AtPrime p) Mp := by
    by_cases hf : IsField (Localization.AtPrime p)
    · letI := hf.toField
      infer_instance
    · haveI h1 : Ring.KrullDimLE 1 (Localization.AtPrime p) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hd)
      have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
      have h3 : IsIntegrallyClosed (Localization.AtPrime p) ∧
          ∃! P : Ideal (Localization.AtPrime p), P ≠ ⊥ ∧ P.IsPrime :=
        ⟨hic, _, ⟨hm, inferInstance⟩, fun P hP ↦ IsLocalRing.eq_maximalIdeal
          (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
      haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
        ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p) hf).out 0 3).mpr h3
      haveI : Module.IsTorsionFree (Localization.AtPrime p) Mp := by
        exact Module.isTorsionFree_iff_algebraMap_injective.mpr hinj'
      exact Module.free_of_finite_type_torsion_free'
  obtain ⟨g, hg, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (IsScalarTower.toAlgHom A M Mp).toLinearMap (Localization.AtPrime p)
  exact ⟨g, hg, hfree⟩

end GlobalTheory.GoodOpenFree

namespace GlobalTheory.GoodOpenFree

theorem app_injective {X Y : Scheme.{0}} [IsIntegral Y] [IsReduced X] (f : X ⟶ Y) [Surjective f]
    (V : Y.Opens) : Function.Injective (f.app V) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := f.surjective x
  have : z ∈ f ⁻¹ᵁ Y.basicOpen s := hx
  rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero] at this
  exact this

theorem exists_free_nbhd : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B.X → ∀ y : B.X, ringKrullDim (B.X.presheaf.stalk y) ≤ 1 → ∀ V : B.X.Opens, y ∈ V → IsAffineOpen V → IsAffineOpen (f.f ⁻¹ᵁ V) → (letI := (f.f.app V).hom.toAlgebra; Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V)) → ∃ V' : B.X.Opens, y ∈ V' ∧ IsAffineOpen V' ∧ IsAffineOpen (f.f ⁻¹ᵁ V') ∧ (letI := (f.f.app V').hom.toAlgebra; Module.Free Γ(B.X, V') Γ(B'.X, f.f ⁻¹ᵁ V') ∧ Module.Finite Γ(B.X, V') Γ(B'.X, f.f ⁻¹ᵁ V')) := by
  intro O _ _ _ B B' f hN y hdim V hy hV hV' hfin
  letI : Algebra Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) := (f.f.app V).hom.toAlgebra
  haveI : Nonempty V := ⟨⟨y, hy⟩⟩
  obtain ⟨z, hz⟩ := f.f.surjective y
  haveI : Nonempty (f.f ⁻¹ᵁ V) := ⟨⟨z, show f.f z ∈ V from hz ▸ hy⟩⟩
  haveI : IsNoetherianRing Γ(B.X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hinj : Function.Injective (algebraMap Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V)) := app_injective f.f V
  let q := hV.primeIdealOf ⟨y, hy⟩
  let p : Ideal Γ(B.X, V) := q.asIdeal
  haveI : p.IsPrime := q.isPrime
  letI : Algebra Γ(B.X, V) (B.X.presheaf.stalk y) := B.X.presheaf.algebra_section_stalk ⟨y, hy⟩
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  haveI := hN
  let e := IsLocalization.algEquiv p.primeCompl (B.X.presheaf.stalk y) (Localization.AtPrime p)
  have hic : IsIntegrallyClosed (Localization.AtPrime p) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have hd : ringKrullDim (Localization.AtPrime p) ≤ 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]; exact hdim
  obtain ⟨g, hg, hfree⟩ := exists_free_away hinj p hic hd
  have hyW : y ∈ B.X.basicOpen g := by
    have h1 : q ∈ hV.fromSpec ⁻¹ᵁ B.X.basicOpen g := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hV.fromSpec q ∈ B.X.basicOpen g := h1
    rwa [hV.fromSpec_primeIdealOf] at h2
  have hpre : f.f ⁻¹ᵁ B.X.basicOpen g = B'.X.basicOpen (f.f.app V g) := Scheme.preimage_basicOpen _ _
  have hW' : IsAffineOpen (f.f ⁻¹ᵁ B.X.basicOpen g) := hpre ▸ hV'.basicOpen (f.f.app V g)
  refine ⟨B.X.basicOpen g, hyW, hV.basicOpen g, hW', ?_⟩
  let A := Γ(B.X, V)
  let M := Γ(B'.X, f.f ⁻¹ᵁ V)
  let R := Γ(B.X, B.X.basicOpen g)
  let N := Γ(B'.X, f.f ⁻¹ᵁ B.X.basicOpen g)
  letI : Algebra A R := (B.X.presheaf.map (homOfLE (B.X.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g R := hV.isLocalization_basicOpen g
  have hle : f.f ⁻¹ᵁ B.X.basicOpen g ≤ f.f ⁻¹ᵁ V := f.f.preimage_mono (B.X.basicOpen_le g)
  letI : Algebra M N := (B'.X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI : IsLocalization.Away (algebraMap A M g) N :=
    hV'.isLocalization_of_eq_basicOpen (f.f.app V g) (homOfLE hle) hpre
  letI : Algebra R N := (f.f.app (B.X.basicOpen g)).hom.toAlgebra
  letI : Algebra A N := ((algebraMap R N).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A M N := IsScalarTower.of_algebraMap_eq fun a => by
    change (f.f.app _).hom ((B.X.presheaf.map (homOfLE (B.X.basicOpen_le g)).op).hom a) =
      (B'.X.presheaf.map (homOfLE hle).op).hom ((f.f.app V).hom a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers g)) N := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers g) (IsScalarTower.toAlgHom A M N).toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  refine ⟨?_, Module.Finite.of_isLocalizedModule (Submonoid.powers g) (Rₚ := R)
    (IsScalarTower.toAlgHom A M N).toLinearMap⟩
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (IsScalarTower.toAlgHom A M N).toLinearMap
  let b₀ := Module.Free.chooseBasis (Localization.Away g) (LocalizedModule.Away g M)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) R
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars A ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) R
  exact Module.Free.of_basis (Module.Basis.ofRepr Ψ')

end GlobalTheory.GoodOpenFree
