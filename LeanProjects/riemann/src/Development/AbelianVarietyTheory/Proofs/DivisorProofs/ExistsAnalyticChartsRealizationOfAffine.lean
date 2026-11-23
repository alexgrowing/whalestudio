import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapValHomFromSpec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_real_isFor : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ K : Charts F, (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ r : Real K s σ, r.IsFor u ∧ ∀ k (U : X.Opens), IsAffineOpen U → (∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ⊤ ≤ r.x k ⁻¹ᵁ U := by
  intro I _ g Λ _ F B _ X s σ u hX K hK
  choose U hU hUE using hK
  have hx := fun k => exists_pt_of_affine u (K.W k) (K.base k) (U k) (hU k) (hUE k)
  choose x hxU hxE using hx
  have uniq : ∀ k (y : Sp (Hol (K.W k)) ⟶ X),
      (∀ p (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ y = u.E p) → y = x k := fun k y hy =>
    point_hol_ext_of_isSeparated (K.W k) hX y (x k) (fun p hp => (hy p hp).trans (hxE k p hp).symm)
  refine ⟨⟨x, ?_, ?_⟩, ?_, ?_⟩
  · intro k
    apply point_hol_ext_of_isSeparated (K.W k) inferInstance
    intro p hp
    rw [← Category.assoc, hxE k p hp, u.w p (K.base k p hp), ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    congr 1
  · intro l k k' h
    apply uniq k'
    intro p hp
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    have e : ((Hol.ev p hp).toRingHom.comp (Charts.sh h)) = (Hol.ev (F.shift l p) (K.maps h p hp)).toRingHom := by
      ext f
      simp [Hol.ev_apply, Charts.fn_sh h f hp]
    rw [e, hxE k _ (K.maps h p hp), u.per l p (K.base k' p hp)]
  · intro k p hp
    exact hxE k p hp
  · intro k V hV hVE
    obtain ⟨y, hyV, hyE⟩ := exists_pt_of_affine u (K.W k) (K.base k) V hV hVE
    have e := uniq k y hyE
    subst e
    exact hyV

end GlobalTheory.AnPer
