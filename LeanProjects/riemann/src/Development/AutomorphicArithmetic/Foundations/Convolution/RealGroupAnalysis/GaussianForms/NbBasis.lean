import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsAlt
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem val_coe {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v) = v.valuation F a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem dv_iff {F : Type} [Field F] [NumberField F] (m : F) (hm : m ≠ 0) (x : A F) :
    Dv m x ↔ algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2 ∈ integralFiniteAdeles (𝓞 F) F := by
  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) v) ≤ 1 ↔
        Valued.v (x.2 v) ≤ v.valuation F m) := by
    intro v
    have h0 : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) v =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹) v * x.2 v := rfl
    rw [e, Valuation.map_mul, val_coe, map_inv₀, mul_comm, ← div_eq_mul_inv]
    exact div_le_one₀ (zero_lt_iff.2 h0)
  constructor
  · intro h v
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((key v).2 (h v))
  · intro h v
    exact (key v).1 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h v))

theorem UpperTheory.ConvolutionTheory.R2.C.nbBasis :
    ∀ (F : Type) [Field F] [NumberField F], (∀ U ∈ 𝓝 (0 : A F), ∃ m : F, m ≠ 0 ∧ Dv 1 (rt m) ∧ ∀ x : A F, x.1 = 0 → Dv m x → x ∈ U) ∧
    ∀ m : F, m ≠ 0 → ∀ᶠ x in 𝓝 (0 : A F), Dv m x := by
  intro F _ _
  constructor
  · intro U hU
    have hc : Continuous (fun y : FiniteAdeleRing (𝓞 F) F => ((0, y) : A F)) :=
      continuous_const.prodMk continuous_id
    have hW : (fun y : FiniteAdeleRing (𝓞 F) F => ((0, y) : A F)) ⁻¹' U ∈
        𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := hc.continuousAt.preimage_mem_nhds hU
    obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
    have hm : algebraMap (𝓞 F) F d ≠ 0 := by
      simpa using hd0
    refine ⟨algebraMap (𝓞 F) F d, hm, ?_, ?_⟩
    · intro v
      have : Valued.v ((rt (algebraMap (𝓞 F) F d) : A F).2 v) = v.valuation F (algebraMap (𝓞 F) F d) :=
        val_coe v _
      rw [this, map_one]
      exact v.valuation_le_one d
    · intro x hx1 hx
      have hy := hd _ ((dv_iff _ hm x).1 hx)
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
          (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d)⁻¹ * x.2) = x.2 := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hm, map_one, one_mul]
      rw [e] at hy
      have h3 : ((0, x.2) : A F) ∈ U := hy
      rwa [show ((0, x.2) : A F) = x from Prod.ext hx1.symm rfl] at h3
  · intro m hm
    have hc : Continuous (fun x : A F => algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) :=
      continuous_const.mul continuous_snd
    have hO : IsOpen ((fun x : A F => algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) ⁻¹'
        (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
      isOpen_integralFiniteAdeles.preimage hc
    have h0 : (0 : A F) ∈ ((fun x : A F => algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) ⁻¹'
        (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) := by
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * (0 : FiniteAdeleRing (𝓞 F) F) ∈
        (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
      rw [mul_zero]
      exact (integralFiniteAdeles (𝓞 F) F).zero_mem
    filter_upwards [hO.mem_nhds h0] with x hx
    exact (dv_iff m hm x).2 hx
