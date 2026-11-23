import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.PsiTriv

theorem exists_nat_trivial {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m : Fv F v)‖) → ψ t = 1 := by
  classical
  let f : FiniteAdeleRing (𝓞 F) F → AF F := fun y => (0, y)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  have hW : (fun y => ψ (f y)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine ((isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).preimage (hψ.comp hf)).mem_nhds ?_
    show ‖ψ (0 : AF F) - 1‖ < 1 / 2
    rw [AddChar.map_zero_eq_one]; norm_num
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  set D : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d) with hD
  have htriv : ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = 1 := by
    intro y hy
    refine GroundTheory.Global.eq_one_of_sq_mem
      (s := {z | ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = z}) ?_ ?_ ⟨y, hy, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨a + a, add_mem ha ha, ?_⟩
      rw [sq, ← AddChar.map_add_eq_mul]
      congr 1
      show ((0 : InfiniteAdeleRing F), D * (a + a)) = ((0 : InfiniteAdeleRing F) + 0, D * a + D * a)
      rw [mul_add, add_zero]
    · rintro _ ⟨a, ha, rfl⟩
      exact hd a ha
  have hm0 : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero hm0, fun t ht0 ht => ?_⟩
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  let y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2
  have hty : t = f (D * y) := by
    refine Prod.ext ht0 ?_
    show t.2 = algebraMap F _ (algebraMap (𝓞 F) F d) * (algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hdF, map_one, one_mul]
  rw [hty]
  refine htriv y fun v => ?_
  have hv : ‖t.2 v‖ ≤ _ := ht v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
  have hy : y v = algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)⁻¹ * t.2 v := rfl
  have hm : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Fv F v) =
      algebraMap F (Fv F v) (algebraMap (𝓞 F) F e) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) := by
    rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
  have hdv : algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) ≠ 0 := (map_ne_zero _).2 hdF
  have he1 : ‖algebraMap F (Fv F v) (algebraMap (𝓞 F) F e)‖ ≤ 1 := FinitePlace.norm_le_one F v e
  rw [hy, map_inv₀, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hdv)]
  rw [hm, norm_mul] at hv
  nlinarith [norm_nonneg (algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)), norm_nonneg (t.2 v)]

end GlobalTheory.PsiTriv
