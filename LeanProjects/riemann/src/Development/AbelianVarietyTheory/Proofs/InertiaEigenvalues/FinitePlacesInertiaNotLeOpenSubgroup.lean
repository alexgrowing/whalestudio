import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

theorem finite_not_ine_le_of_isOpen : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) →
    {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  intro Ω _ k _ _ _ _ N hN
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff k Ω (N : Set (G k Ω))).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional k L := hL
  refine (GlobalTheory.InertiaAlmostAll.finite_ramified k Ω L).subset ?_
  rintro w ⟨B, hB, h⟩
  exact ⟨B, hB, fun h' => h fun x hx => hLN (h' hx)⟩

end GlobalTheory.DelGlob
