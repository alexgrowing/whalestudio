import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem kbarRep_contAction : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro g0 hg0
  have hop := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
  have hn : (fun g : GK p K => g0⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K)
      (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) : Set (GK p K)) ∈ nhds g0 :=
    (hop.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : (g0⁻¹ * g) (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := hg
  have hgg : g (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = g0 (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := by
    have := congrArg g0 hg'
    rw [AlgEquiv.mul_apply] at this
    rw [← this]
    exact (g0.apply_symm_apply _).symm
  have hxy : kbarRep p K g y = kbarRep p K g0 y := Units.ext hgg
  show kbarRep p K g y = x
  rw [hxy]
  exact hg0

noncomputable def kbarT : TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := kbarRep_contAction p K

scoped instance : DiscreteTopology (kbarT p K).V := inferInstanceAs (DiscreteTopology (KbarMult p))

end ReciprocityTheory.DiscreteGroups.LocalClassField
