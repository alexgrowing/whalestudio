import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceUnderIsPlaceOver

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.RealGal.ConjUnr

theorem unr_of_conj_res : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)), UpperTheory.V.Af.RepIso r (ρ.comp (UpperTheory.V.Af.Bc.res E Ω ↥Q.K)) → (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := ↥Q.K) A, r s = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1 := by
  intro E Ω _ _ _ _ _ Q l _ a ρ r hiso hr
  haveI : FiniteDimensional E Q.K := Module.finite_of_finrank_eq_succ Q.two
  have hS1 := GlobalTheory.InertiaAlmostAll.finite_ramified E Ω Q.K
  have hbad := Filter.eventually_cofinite.mp hr
  have hS2 := hbad.image (fun u : HeightOneSpectrum (𝓞 ↥Q.K) => u.under (𝓞 E))
  refine Filter.eventually_cofinite.mpr ((hS1.union hS2).subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨A, hA, s, hs, hρ⟩ := hw
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image, not_or, not_exists, not_and] at hn
  obtain ⟨h1, h2⟩ := hn
  have hfix : s ∈ Q.K.fixingSubgroup := by
    by_contra hns
    exact h1 A hA (fun hle => hns (hle hs))
  obtain ⟨u, hu⟩ := GlobalTheory.LocLanglands.EpsUnique.exists_place hA ↥Q.K
  have hwu : u.under (𝓞 E) = w := ReciprocityTheory.Gal.eq_of_isPlaceOver (GlobalTheory.DelGlob.placeUnder_isPlaceOver ↥Q.K hu) hA
  have hgood : ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ t ∈ Ine (F := ↥Q.K) A, r t = 1 := by
    by_contra hb
    exact h2 u hb hwu
  let t : G ↥Q.K Ω := IntermediateField.fixingSubgroupEquiv Q.K ⟨s, hfix⟩
  have hts : UpperTheory.V.Af.Bc.res E Ω ↥Q.K t = s := AlgEquiv.ext fun _ => rfl
  have ht : t ∈ Ine (F := ↥Q.K) A := ⟨hs.1, hs.2⟩
  obtain ⟨g, hg⟩ := hiso
  apply hρ
  have := hg t
  rw [MonoidHom.comp_apply, hts, hgood A hu t ht] at this
  rw [this]; simp

end GlobalTheory.RealGal.ConjUnr
