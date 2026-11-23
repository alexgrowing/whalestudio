import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan

noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

namespace DictInter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tau (w : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ
    TensorProduct.map ((Algebra.trace F E) ∘ₗ LinearMap.mulLeft F w) LinearMap.id

lemma tau_tmul (w e : E) (a : Af F) : tau w (e ⊗ₜ[F] a) = Algebra.trace F E (w * e) • a := by
  first
    | simp [tau]
    | rfl

variable (F E) in

def dualSet : Set E := {w | ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range}

lemma tau_mul_left (w a : E) (r : E ⊗[F] Af F) :
    tau w ((a ⊗ₜ[F] (1 : Af F)) * r) = tau (w * a) r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_assoc]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy]

lemma tau_mul_right (w : E) (b : Af F) (r : E ⊗[F] Af F) :
    tau w (((1 : E) ⊗ₜ[F] b) * r) = b * tau w r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]

lemma tau_incl (w e : E) :
    tau w (Formalism.UG.inclE (F := F) (Af F) e) = algebraMap F (Af F) (Algebra.trace F E (w * e)) := by
  show tau w (e ⊗ₜ[F] (1 : Af F)) = _
  rw [tau_tmul, Algebra.algebraMap_eq_smul_one]

lemma algebraMap_mem_intAd (x : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F x) ∈ Formalism.UG.intAd F := by
  intro v
  have h1 : Valued.v (((algebraMap (𝓞 F) F x : F)) : v.adicCompletion F) ≤ 1 := by
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
  first
    | exact h1
    | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1

lemma of_algebraMap_mem_intAd (f : F) (h : algebraMap F (Af F) f ∈ Formalism.UG.intAd F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) f ?_
  intro v
  have hv : Valued.v ((f : F) : v.adicCompletion F) ≤ 1 := h v
  first
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv

def tSet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Set (E ⊗[F] Af F) :=
  {r | ∀ w ∈ dualSet F E, tau w r ∈ Formalism.UG.intAd F}

lemma one_mem_tSet : (1 : E ⊗[F] Af F) ∈ tSet F E := by
  show ∀ w ∈ dualSet F E, tau w ((1 : E) ⊗ₜ[F] (1 : Af F)) ∈ Formalism.UG.intAd F
  intro w hw
  have hw1 := (show ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range from hw) 1
  obtain ⟨x, hx⟩ := hw1
  rw [tau_tmul, ← Algebra.algebraMap_eq_smul_one]
  have hx' : Algebra.trace F E (w * (1 : E)) = algebraMap (𝓞 F) F x := by
    rw [hx]
    rfl
  rw [hx']
  exact algebraMap_mem_intAd x

private theorem mul_algebraMap_mem_dualSet {w : E} (hw : w ∈ dualSet F E) (a : 𝓞 E) :
    w * algebraMap (𝓞 E) E a ∈ dualSet F E := by
  show ∀ b : 𝓞 E, Algebra.trace F E (w * algebraMap (𝓞 E) E a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
  intro b
  have h := (show ∀ b : 𝓞 E, Algebra.trace F E (w * (b : E)) ∈ (algebraMap (𝓞 F) F).range from hw) (a * b)
  rw [mul_assoc]
  exact h

lemma mem_tSet (r : E ⊗[F] Af F) (hr : r ∈ IntAf F E) : r ∈ tSet F E := by
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  suffices h : ∀ s ∈ tSet F E, r * s ∈ tSet F E by
    have h1 := h 1 one_mem_tSet
    rwa [mul_one] at h1
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨a, rfl⟩ := he
      intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_left]
      exact (show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) _ (mul_algebraMap_mem_dualSet hw a)
    · intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_right]
      exact mul_mem hb ((show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) w hw)
  | zero =>
    intro s _
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w _
    rw [zero_mul, map_zero]
    exact zero_mem _
  | one =>
    intro s hs
    rwa [one_mul]
  | add x y _ _ hx hy =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [add_mul, map_add]
    exact add_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
      ((show ∀ w ∈ dualSet F E, tau w (y * s) ∈ Formalism.UG.intAd F from hy s hs) w hw)
  | neg x _ hx =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [neg_mul, map_neg]
    exact neg_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_assoc]
    exact hx _ (hy s hs)

end DictInter

open DictInter in
theorem dual_intersection : DInter := by
  intro F E _ _ _ _ _ e he
  have ht := mem_tSet (F := F) (E := E) _ he
  have key : ∀ w ∈ dualSet F E, Algebra.trace F E (w * e) ∈ (algebraMap (𝓞 F) F).range := by
    intro w hw
    apply of_algebraMap_mem_intAd
    rw [← tau_incl]
    exact (show ∀ w ∈ dualSet F E, tau w (Formalism.UG.inclE (F := F) (Af F) e) ∈ Formalism.UG.intAd F from ht) w hw
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    first
      | exact FractionalIdeal.dual_ne_zero (𝓞 F) F h1
      | exact FractionalIdeal.dual_ne_zero h1
  have hmem : e ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    rw [Algebra.traceForm_apply, mul_comm]
    apply key
    show ∀ b : 𝓞 E, Algebra.trace F E (a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
    intro b
    have hb := ha (b : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    rwa [Algebra.traceForm_apply] at hb
  rw [FractionalIdeal.dual_dual] at hmem
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  exact ⟨x, hx⟩

end PIW.AdelClassFin
