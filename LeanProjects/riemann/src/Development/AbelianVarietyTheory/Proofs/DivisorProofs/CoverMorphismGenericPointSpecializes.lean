import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.CoverGenPt

theorem fibre_map_genericPoint {F : Type} [Field F] [NumberField F] {Y : Var F} {V' V : Cover Y} (g : V'.G ⟶ V.G)
    (h : g ≫ V.π = V'.π) : g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem lies_genericPoint_specializes : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V V' : Cover Y) (π : V'.X ⟶ V.X), Lies V' V π → π (genericPoint V'.X) ⤳ genericPoint V.X := by
  intro F _ _ Y V V' π h
  obtain ⟨g, h₁, h₂⟩ := h
  refine specializes_of_eq ?_
  rw [← GlobalTheory.CoverDeg.j_genericPoint V', ← Scheme.Hom.comp_apply, ← h₁, Scheme.Hom.comp_apply, fibre_map_genericPoint g h₂, GlobalTheory.CoverDeg.j_genericPoint V]

end GlobalTheory.CoverGenPt
