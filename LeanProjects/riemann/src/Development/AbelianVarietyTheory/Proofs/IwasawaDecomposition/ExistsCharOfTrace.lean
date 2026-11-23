import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

section General

variable (F : Type) [Field F] [NumberField F]

def ratChar (x : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))

theorem ratChar_add (x y : F) : ratChar F (x + y) = ratChar F x * ratChar F y := by
  rw [ratChar, ratChar, ratChar, ← Complex.exp_add, map_add]
  congr 1
  push_cast
  ring

theorem ratChar_zero : ratChar F 0 = 1 := by simp [ratChar]

theorem norm_ratChar (x : F) : ‖ratChar F x‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((Algebra.trace ℚ F x : ℚ) : ℝ))
  rw [← this, ratChar]
  congr 2
  push_cast
  ring

theorem ratChar_integer (r : 𝓞 F) : ratChar F (r : F) = 1 := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) := Algebra.isIntegral_trace r.isIntegral_coe
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [ratChar, ← hk, eq_intCast, Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem ratChar_of_integral (x : F)
    (h : ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) : ratChar F x = 1 := by
  have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
  rw [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
    FractionalIdeal.mem_one_iff] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ratChar_integer F r

theorem exists_finChar : ∃ χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ, Continuous χ ∧ (∀ y, ‖χ y‖ = 1) ∧
    ∀ x : F, χ (algebraMap F _ x) = ratChar F x := by
  choose e s hs he using GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos
  simp only [one_smul] at he
  have key : ∀ (y : FiniteAdeleRing (𝓞 F) F) (a : F) (w : FiniteAdeleRing (𝓞 F) F),
      (∀ v, w v ∈ v.adicCompletionIntegers F) → y = algebraMap F _ a + w → ratChar F (e y) = ratChar F a := by
    intro y a w hw h
    have h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (e y - a) = w - s y := by
      rw [map_sub]
      linear_combination h - he y
    have h3 := ratChar_of_integral F (e y - a) fun v => by
      rw [h2]; exact sub_mem (hw v) (hs y v)
    rw [show e y = a + (e y - a) by ring, ratChar_add, h3, mul_one]
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    { toFun := fun y => ratChar F (e y)
      map_zero_eq_one' := (key 0 0 0 (fun v => zero_mem _) (by simp)).trans (ratChar_zero F)
      map_add_eq_mul' := fun x y => by
        rw [← ratChar_add]
        refine key _ _ (s x + s y) (fun v => add_mem (hs x v) (hs y v)) ?_
        rw [map_add]
        linear_combination he x + he y }
  refine ⟨χ, ?_, fun y => norm_ratChar F _, fun x => key _ x 0 (fun v => zero_mem _) (add_zero _).symm⟩
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : Continuous fun z : FiniteAdeleRing (𝓞 F) F => z - y := continuous_id.sub continuous_const
  have hU := ((GlobalTheory.AdLat.OpenLat.isOpen_integral F).preimage hc).mem_nhds (x := y) (by
    intro v
    simp only [sub_self]
    exact zero_mem _)
  refine (continuousAt_const (y := χ y)).congr (Filter.mem_of_superset hU fun z hz => ?_)
  refine (key z (e y) (s y + (z - y)) (fun v => add_mem (hs y v) (hz v)) ?_).symm
  linear_combination he y

theorem exists_char_of_trace (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := by
  obtain ⟨χ, hc, hn, hr⟩ := exists_finChar F
  have him : ∀ x, (L x).im = 0 := by
    have : (fun x => (L x).im) = fun _ => (0 : ℝ) := by
      refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer (Complex.continuous_im.comp hL)
        continuous_const ?_
      funext x
      show (L (algebraMap F _ x)).im = 0
      rw [hT, Complex.ratCast_im]
    exact congrFun this
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun a => Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        rw [map_add, map_add, map_add, mul_add, Complex.exp_add, AddChar.map_add_eq_mul]
        ring }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := fun x => by
    show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) * χ 0 = _
    rw [AddChar.map_zero_eq_one, mul_one]
  refine ⟨ψ, ⟨?_, fun a => ?_, fun a => ?_, ?_⟩, hinf⟩
  · exact (Complex.continuous_exp.comp (continuous_const.mul (hL.comp continuous_fst))).mul
      (hc.comp continuous_snd)
  · show ‖Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)‖ = 1
    rw [norm_mul, hn, mul_one, Complex.norm_exp]
    simp [him]
  · show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F (algebraMap F _ a))) *
      χ (sndA F (algebraMap F _ a)) = 1
    rw [AlgHom.commutes, AlgHom.commutes, hT, hr, ratChar, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  · have hd : ((Module.finrank ℚ F : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ)))) 0, ?_⟩
    have h := hinf (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ))))
    rw [hT, Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ _ hd, psiInf] at h
    have e : 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ((-(1 / 2) : ℚ) : ℂ) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [h, e, Complex.exp_pi_mul_I]
    norm_num

end General

theorem exists_isStdChar : ∀ D : D7, ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  obtain ⟨ψ, h1, h2⟩ := exists_char_of_trace D.host.F L (continuous_finset_sum _ fun ρ _ => (hθ ρ).2) fun x => by
    show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace]
  refine ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => ?_⟩
  rw [h2, GlobalTheory.DualPairCompare.sum_infFam θ' hθ', ← GlobalTheory.DualPairCompare.sum_infFam θ hθ]
  rfl

end GlobalTheory.StdAdelicChar

end
