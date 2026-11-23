import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.TraitUniq

theorem jK_comp_spMap {V W : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W)
    (fK : FractionRing V →+* FractionRing W) (hK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) :
    spMap fK ≫ jK V = jK W ≫ spMap f := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact hK a

theorem exists_common_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∃ tW : SAB H (Sp W), Nonempty (SABMap tW T.t (spMap f)) ∧ Nonempty (SABMap tW T'.t (spMap f')) := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' _ hdvr _ _ _ _ hK hK' hy
  obtain ⟨tW, ⟨mW⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) T.t
  obtain ⟨tW', ⟨mW'⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f') T'.t
  obtain ⟨tK, ⟨a⟩, ⟨b⟩⟩ := T.gen
  obtain ⟨tK', ⟨a'⟩, ⟨b'⟩⟩ := T'.gen
  obtain ⟨uK, ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap fK ≫ T.y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨c₁⟩ := GlobalTheory.TraitOrder.cancel rfl b n
  have e' : spMap fK' ≫ T'.y ≫ pullback.fst _ _ = spMap fK ≫ T.y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hy, Category.assoc]
  obtain ⟨c₂⟩ := GlobalTheory.TraitOrder.cancel e' b' n
  obtain ⟨d₁⟩ := GlobalTheory.TraitOrder.comp (jK_comp_spMap f fK hK) a c₁
  obtain ⟨d₂⟩ := GlobalTheory.TraitOrder.comp (jK_comp_spMap f' fK' hK') a' c₂
  obtain ⟨x₁⟩ := GlobalTheory.TraitOrder.cancel rfl mW d₁
  obtain ⟨x₂⟩ := GlobalTheory.TraitOrder.cancel rfl mW' d₂
  obtain ⟨ψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map W (FractionRing W) tW tW' uK x₁ x₂
  exact ⟨tW, ⟨mW⟩, GlobalTheory.TraitOrder.comp (Category.id_comp _) mW' ψ⟩

end GlobalTheory.UPoinc.TraitUniq
