import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

noncomputable def displ (X : Data E r) (cu : FJ.CuspFD X ρ) (s : Finset (Fin r → E)) :
    Matrix (Fin ρ) (Fin ρ) E →+ (s → Fin r → E) where
  toFun β := fun v => FJ.zMatE X cu.e β *ᵥ v.1 - v.1
  map_zero' := by
    funext v
    simp [zMatE_zero]
  map_add' β β' := by
    funext v
    simp only [zMatE_mulVec, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
      add_smul]
    abel

theorem displ_injective (X : Data E r) (cu : FJ.CuspFD X ρ) (s : Finset (Fin r → E))
    (hs : Submodule.span E (s : Set (Fin r → E)) = ⊤) : Function.Injective (displ X cu s) := by
  intro β β' h
  apply zMatE_injective X cu
  apply Matrix.toLin'.injective
  refine LinearMap.ext_on hs fun v hv => ?_
  have h1 : FJ.zMatE X cu.e β *ᵥ v - v = FJ.zMatE X cu.e β' *ᵥ v - v := congrFun h ⟨v, hv⟩
  simpa [Matrix.toLin'_apply] using h1

theorem span_zGam_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ), (Submodule.span ℤ (FJ.zGam X cu)).FG := by
  intro E _ _ _ r ρ X cu
  obtain ⟨s, hs⟩ := X.Λ_fg
  have hsE : Submodule.span E (s : Set (Fin r → E)) = ⊤ := by
    rw [← X.Λ_span, ← hs, Submodule.span_span_of_tower]
  have hΛ : (X.Λ.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h2 : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact Module.Finite.iff_fg.1 h2
  have hN : (Submodule.pi Set.univ fun _ : s => X.Λ.restrictScalars ℤ).FG :=
    Submodule.fg_pi fun _ => hΛ
  refine Submodule.fg_of_fg_map_injective (displ X cu s).toIntLinearMap
    (displ_injective X cu s hsE) (hN.of_le ?_)
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro β ⟨-, γ, hγ, e⟩ v -
  have hv : v.1 ∈ X.Λ := hs ▸ Submodule.subset_span v.2
  change FJ.zMatE X cu.e β *ᵥ v.1 - v.1 ∈ X.Λ
  rw [← e]
  exact X.Λ.sub_mem (((X.Γ_stab γ hγ).2 _).1 hv) hv

end GlobalTheory.CuspCentre
