import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay.DHMem

open GlobalTheory.HeisDeriv
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem hasDerivAt_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) (pureA F f g) x)
      (pureA F (heisD F (fun i => evI F (w.1 i)) w.2 f) g x) 0 := by
  set v : κ → mixedEmbedding.mixedSpace F := fun i => evI F (w.1 i) with hv
  set z : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F w.2 z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) with hQ
  have hline : ∀ t : ℝ, schr ψ (realAd F t • w) (pureA F f g) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) *
        (f (z + t • v) * g (fun i => (x i).2)) := by
    intro t
    simp only [schr, Prod.smul_fst, Prod.smul_snd]
    set A : AF F := x ⬝ᵥ (realAd F t • w.2) + ⅟(2 : AF F) * ((realAd F t • w.1) ⬝ᵥ (realAd F t • w.2)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ w.2) = ∑ i, z i * evI F (w.2 i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add,
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • w.1) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    have hfin : (fun i => ((x + realAd F t • w.1) i).2) = fun i => (x i).2 := by
      funext i
      show (x i).2 + (realAd F t).2 * (w.1 i).2 = (x i).2
      rw [show (realAd F t).2 = 0 from rfl, zero_mul, add_zero]
    rw [hψ.2.2 A hAt2, htr]
    show _ * (f (fun i => evI F ((x + realAd F t • w.1) i)) * g (fun i => ((x + realAd F t • w.1) i).2)) = _
    rw [harg, hfin]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (g (fun i => (x i).2)))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  show _ = heisD F v w.2 f z * g (fun i => (x i).2)
  simp only [heisD_apply, mult_apply, ← hP]
  simp
  ring

theorem exists_hasDerivAt (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) :
    ∃ Φ' ∈ schA F κ, ∀ x, HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) Φ x) (Φ' x) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨pureA F (heisD F (fun i => evI F (w.1 i)) w.2 f) g, Submodule.subset_span ⟨_, g, hg, rfl⟩,
      fun x => hasDerivAt_pureA ψ hψ w f g x⟩
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    refine (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.zero_apply, mul_zero]
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨Φ₁', m₁, d₁⟩ := h₁
    obtain ⟨Φ₂', m₂, d₂⟩ := h₂
    refine ⟨Φ₁' + Φ₂', add_mem m₁ m₂, fun x => ?_⟩
    refine ((d₁ x).add (d₂ x)).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.add_apply, mul_add]
  | smul a Φ _ h =>
    obtain ⟨Φ', m, d⟩ := h
    refine ⟨a • Φ', Submodule.smul_mem _ a m, fun x => ?_⟩
    refine ((d x).const_mul a).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.ThetaDecay.DHMem

open GlobalTheory.ThetaDecay.DHMem in

theorem GlobalTheory.ThetaDecay.dH_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ w : (κ → AF F) × (κ → AF F), IsArch w → ∀ Φ ∈ schA F κ, dH ψ w Φ ∈ schA F κ := by
  intro F _ _ κ _ ψ hψ w _ Φ hΦ
  obtain ⟨Φ', hΦ', hd⟩ := exists_hasDerivAt ψ hψ w Φ hΦ
  have : dH ψ w Φ = Φ' := funext fun x => (hd x).deriv
  rw [this]
  exact hΦ'

end
