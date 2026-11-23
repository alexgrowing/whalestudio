import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem hl_basic : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), D.HL.Normal ∧ IsOpen (D.HL : Set (GQ l)) ∧ IsOpenEmbedding D.HL.subtype ∧ (∀ s ∈ D.HL, s ∈ Iq l → D.Ψ s = cycA l l O s ^ D.e) ∧ GlobalTheory.OrdLoc.IsInertiaInfiniteCyclotomic D (GlobalTheory.OrdLoc.s0 D) := by
  intro l _ O _ _ _ D
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  have hex : ∃ s, IsInertiaInfiniteCyclotomic D s := by
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.HL ho).2
    exact ⟨s, hs1, hs2, hs⟩
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ho.isOpenEmbedding_subtypeVal, fun s hs hi => ?_,
    Classical.epsilon_spec hex⟩
  have ht : D.τ s = 1 := hs.2
  rw [D.Ψ_I s hi, ht, mul_one]

end GlobalTheory.OrdLoc
