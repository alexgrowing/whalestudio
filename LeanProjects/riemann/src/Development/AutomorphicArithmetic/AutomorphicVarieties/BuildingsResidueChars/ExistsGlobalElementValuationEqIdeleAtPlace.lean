import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

theorem UpperTheory.exists_global_element_valuation_eq_idele_at_place :
    ∀ (F : Type) [Field F] [NumberField F] (y : (Af F)ˣ) (w : Pl F), ∃ β : F, w.valuation F β = Valued.v (pLoc F w (y : Af F)) ∧ ∀ v : Pl F, v.valuation F β ≤ Valued.v (pLoc F v (y : Af F)) := by
  intro F _ _ y w
  obtain ⟨p, hpw, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hp : algebraMap (𝓞 F) F p ≠ 0 := by simpa using hp0
  have hval : ∀ (v : Pl F) (f : F), Valued.v (pLoc F v (algebraMap F (Af F) f)) = v.valuation F f :=
    fun v f => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  set z : Af F := algebraMap F (Af F) (algebraMap (𝓞 F) F p)⁻¹ * ((y⁻¹ : (Af F)ˣ) : Af F) with hz
  have hc : Continuous fun a : Af F => z * (a - (y : Af F)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  obtain ⟨β, hβ⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open
    ((GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F)).preimage hc)
    ⟨(y : Af F), by simp⟩
  have hβ' : ∀ v : Pl F, Valued.v (pLoc F v (z * (algebraMap F (Af F) β - (y : Af F)))) ≤ 1 :=
    fun v => GroundTheory.Global.mem_integralFiniteAdeles.1 hβ v
  have e : algebraMap F (Af F) β - (y : Af F) =
      (y : Af F) * algebraMap F (Af F) (algebraMap (𝓞 F) F p) * (z * (algebraMap F (Af F) β - (y : Af F))) := by
    have h1 : algebraMap F (Af F) (algebraMap (𝓞 F) F p) * algebraMap F (Af F) (algebraMap (𝓞 F) F p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hp, map_one]
    have h2 : (y : Af F) * ((y⁻¹ : (Af F)ˣ) : Af F) = 1 := y.mul_inv
    have h3 : (y : Af F) * algebraMap F (Af F) (algebraMap (𝓞 F) F p) * z = 1 := by
      rw [hz]
      linear_combination ((y : Af F) * ((y⁻¹ : (Af F)ˣ) : Af F)) * h1 + h2
    rw [← mul_assoc, h3, one_mul]
  have key : ∀ v : Pl F, Valued.v (pLoc F v (algebraMap F (Af F) β) - pLoc F v (y : Af F)) ≤
      Valued.v (pLoc F v (y : Af F)) * v.valuation F (algebraMap (𝓞 F) F p) := fun v => by
    rw [← map_sub, e, map_mul, map_mul, map_mul, map_mul, hval]
    exact mul_le_of_le_one_right' (hβ' v)
  refine ⟨β, ?_, fun v => ?_⟩
  · rw [← hval]
    refine Valuation.map_eq_of_sub_lt _ ((key w).trans_lt ?_)
    have h0 : 0 < Valued.v (pLoc F w (y : Af F)) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (y.isUnit.map (pLoc F w)).ne_zero)
    exact (mul_lt_mul_of_pos_left ((w.valuation_lt_one_iff_mem p).2 hpw) h0).trans_eq (mul_one _)
  · rw [← hval, ← sub_add_cancel (pLoc F v (algebraMap F (Af F) β)) (pLoc F v (y : Af F))]
    exact (Valuation.map_add _ _ _).trans
      (max_le ((key v).trans (mul_le_of_le_one_right' (v.valuation_le_one p))) le_rfl)
