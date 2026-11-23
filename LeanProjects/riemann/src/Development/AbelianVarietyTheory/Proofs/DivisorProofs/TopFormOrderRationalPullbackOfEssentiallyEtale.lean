import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem isFreeGen_formMap_of_formallyEtale {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} {D : ℕ} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β)
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formOrd_ratPull (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ)
    (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p]
    (hn : topologicalKrullDim W = n) (E : DivOver p) (E' : DivOver (f ≫ p))
    (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring)
    (hρ : ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale)
    (hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g)
    (η : RatForms p n) (hη : η ≠ 0) :
    E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  set φ := functionFieldMap f with hφ
  set ρ := φ.restrict E.ring E'.ring h with hρdef
  obtain ⟨ω, hω, g, hη', hg⟩ := E.isFormOrd_formOrd hn hη
  have hc : ρ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun (functionFieldMap_comp_constFn p f) a
  have hω' : IsFreeGen E'.ring (TopForm.formMap n ρ hc ω) := isFreeGen_formMap_of_formallyEtale hρ hc hω
  have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ρ := by
    ext x
    rfl
  have hτ : (E'.ring.subtype.comp ρ).comp E.const = Cartier.constFn (f ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ρ hc ω) := by
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl
      (functionFieldMap_comp_constFn p f) hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ρ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hpull : ratPull p f n η = φ (g : W.functionField) • E'.toRat n (TopForm.formMap n ρ hc ω) := by
    rw [hη', map_smulₛₗ, key]
  have hne : ratPull p f n η ≠ 0 := by
    rw [hpull]
    intro h0
    have hinj := (E'.isFreeGen_toRat hω').1
    have : φ (g : W.functionField) = 0 := hinj (by simpa using h0)
    exact (g.map φ.toMonoidHom).ne_zero this
  rw [← hg]
  refine DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', Units.map φ.toMonoidHom g, hpull, hord g⟩

end GlobalTheory.EtaleKlt
