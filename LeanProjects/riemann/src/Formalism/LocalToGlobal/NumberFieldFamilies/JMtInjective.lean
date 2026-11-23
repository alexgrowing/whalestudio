import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNdStd
import Formalism.LocalToGlobal.NumberFieldFamilies.GamCSpec

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

theorem jMt_injective (μ : what₂.Tup) (j : ℕ) : Function.Injective (what₂.jMt μ j) := by
  set b := Module.Free.chooseBasis what₂.LL (what₂.MtL μ j)
  have hb := (what₂.jMt_basis μ j b).1
  have key : ∀ z, Finsupp.linearCombination ℂ (fun i => what₂.jMt μ j (b i))
      ((b.repr z).mapRange what₂.embLL (map_zero _)) = what₂.jMt μ j z := by
    intro z
    conv_rhs => rw [← b.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp),
      map_finsuppSum]
    simp only [LinearMap.map_smulₛₗ]
  intro x y hxy
  have h1 : what₂.jMt μ j (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← key] at h1
  have h2 := (linearIndependent_iff.1 hb) _ h1
  have h3 : b.repr (x - y) = 0 := Finsupp.ext fun i => what₂.embLL.injective (by
    have := congrArg (fun f => f i) h2
    simpa using this)
  rw [← sub_eq_zero]
  exact b.repr.injective (h3.trans (map_zero _).symm)

theorem latL_finite (i : LocT B) : (latL B i).Finite := by
  classical
  refine Set.Finite.subset ((what₂.MtLat (what₂.muTw (wOf B i)) (jOf B i)).gen.finite_toSet.preimage
    ((jMt_injective (what₂.muTw (wOf B i)) (jOf B i)).injOn)) fun x hx => hx

variable {B}

instance noZero (i : LocT B) : NoZeroSMulDivisors (OOf B i) (B.V (jOf B i) (wOf B i)) := by
  refine ⟨fun {c x} h => ?_⟩
  have h1 : algebraMap (OOf B i) (FractionRing (OOf B i)) c • x = 0 := by rw [algebraMap_smul]; exact h
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact Or.inl ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2)
  · exact Or.inr h2

theorem mtSub_fg (hC : PartCompl B) (i : LocT B) : (MtSub B hC i).FG := by
  classical
  refine ⟨((latL_finite B i).toFinset.image fun x => projOf B hC i (B.iV (jOf B i) (wOf B i) x)), ?_⟩
  unfold MtSub
  congr 1
  ext y
  simp

theorem mtSub_finite (hC : PartCompl B) (i : LocT B) : Module.Finite (OOf B i) (MtSub B hC i) :=
  Module.Finite.iff_fg.2 (mtSub_fg hC i)

theorem mtSub_free (hC : PartCompl B) (i : LocT B) : Module.Free (OOf B i) (MtSub B hC i) := by
  haveI := mtSub_finite hC i
  haveI : NoZeroSMulDivisors (OOf B i) (partOf B i) := by
    refine ⟨fun {c x} h => ?_⟩
    have h1 : c • (x : B.V (jOf B i) (wOf B i)) = 0 := by
      have := congrArg (fun z : partOf B i => (z : B.V (jOf B i) (wOf B i))) h
      simpa using this
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Subtype.ext h2)
  exact Module.free_of_finite_type_torsion_free'

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
