import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isObU_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L C' _ F' L' n l u u' c hL hN hu hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hex : ∀ T, ∃ s : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) s := fun T =>
    GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ' hσ' using hex
  have hnat : ∀ T : C', (∀ y, l T (σ (n.G.obj T) y) = σ' T (extHom R₁ (coefHom n T) y)) ∧
      ∀ y, α.KerQ y → α.KerQ (extHom R₁ (coefHom n T) y) := fun T =>
    GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _)
      _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) (l T) (coefHom n T) (fun b => hL T b) _ _ (hσ _) (hσ' T)
  refine ⟨fun T T' a => Units.map (l T').toRingHom.toMonoidHom (v _ _ (n.G.map a)), σ', (extMap R₁ n).pullbackTwoCocycle z,
    ?_, hσ', ?_, ?_⟩
  · intro T T' a
    change L'.p T' (l T' _) = _
    rw [hL, hv, hu]
  · rw [hc]; rfl
  · intro T T' T'' a b
    obtain ⟨hk1, hk2⟩ := hz _ _ _ (n.G.map a) (n.G.map b)
    refine ⟨(hnat T'').2 _ hk1, ?_⟩
    change L'.ρ b (l T' _) * l T'' _ = (1 + σ' T'' (extHom R₁ (coefHom n T'') _)) * l T'' _
    rw [hN, ← map_mul, hk2, map_mul, map_add, map_one, (hnat T'').1, Functor.map_comp]
    rfl

end GlobalTheory.LBObs
