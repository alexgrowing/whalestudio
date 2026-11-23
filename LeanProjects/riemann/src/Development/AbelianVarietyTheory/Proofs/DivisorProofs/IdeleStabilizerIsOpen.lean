import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IdeleTate

theorem isOpen_stab (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsOpen ((GlobalTheory.IdeleTate.stab F E : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) := by
  classical
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set B := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hB
  let O : Set (AF F) := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  have hO : IsOpen O :=
    (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd
  have hOadd : ∀ a b, a ∈ O → b ∈ O → a + b ∈ O := fun a b ha hb v => by
    rw [map_add]; exact add_mem (ha v) (hb v)
  have hOmul : ∀ a b, a ∈ O → b ∈ O → a * b ∈ O := fun a b ha hb v => by
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  have hO0 : (0 : AF F) ∈ O := fun v => by rw [map_zero]; exact zero_mem _
  have hlat : ∀ x, x ∈ lat F E ↔ ∀ i, B.equivFun x i ∈ O := fun x => Iff.rfl
  have hlatadd : ∀ x z, x ∈ lat F E → z ∈ lat F E → x + z ∈ lat F E := by
    intro x z hx hz
    rw [hlat] at hx hz ⊢
    intro i
    rw [map_add, Pi.add_apply]
    exact hOadd _ _ (hx i) (hz i)
  let V : Set (AE F E) := {y | ∀ j k, B.equivFun (y * B j) k ∈ O}
  have hcont : ∀ j k, Continuous fun y : AE F E => B.equivFun (y * B j) k := fun j k =>
    (continuous_apply k).comp ((IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap).comp
      (continuous_mul_right _))
  have hV : IsOpen V := by
    have : V = ⋂ j, ⋂ k, (fun y : AE F E => B.equivFun (y * B j) k) ⁻¹' O := by
      ext y; simp [V]
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => hO.preimage (hcont j k)
  have hV0 : (0 : AE F E) ∈ V := fun j k => by simpa using hO0
  have hmulV : ∀ y ∈ V, ∀ x ∈ lat F E, y * x ∈ lat F E := by
    intro y hy x hx
    rw [hlat] at hx ⊢
    intro k
    have hx' : x = ∑ j, B.equivFun x j • B j := (B.sum_equivFun x).symm
    have e : B.equivFun (y * x) k = ∑ j, B.equivFun x j * B.equivFun (y * B j) k := by
      conv_lhs => rw [hx', Finset.mul_sum]
      simp only [mul_smul_comm, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Finset.sum_induction _ (· ∈ O) hOadd hO0 fun j _ => hOmul _ _ (hx j) (hy j k)
  have key : ∀ w : AE F E, w - 1 ∈ V → ∀ z ∈ lat F E, w * z ∈ lat F E := fun w hw z hz => by
    have := hlatadd _ _ hz (hmulV _ hw z hz)
    rwa [show z + (w - 1) * z = w * z by ring] at this
  have hstab : ∀ u : (AE F E)ˣ, (u : AE F E) - 1 ∈ V → ((u⁻¹ : (AE F E)ˣ) : AE F E) - 1 ∈ V →
      u ∈ stab F E := by
    intro u h1 h2 x
    constructor
    · exact key _ h1 x
    · intro h
      have := key _ h2 _ h
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  let S : Set (AE F E)ˣ := {u | (u : AE F E) - 1 ∈ V ∧ ((u⁻¹ : (AE F E)ˣ) : AE F E) - 1 ∈ V}
  have hS : IsOpen S :=
    (hV.preimage (Units.continuous_val.sub continuous_const)).inter
      (hV.preimage (Units.continuous_coe_inv.sub continuous_const))
  have h1S : (1 : (AE F E)ˣ) ∈ S := ⟨by simpa using hV0, by simpa using hV0⟩
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hS.mem_nhds h1S) fun u hu => hstab u hu.1 hu.2)

end GlobalTheory.IdeleTate
