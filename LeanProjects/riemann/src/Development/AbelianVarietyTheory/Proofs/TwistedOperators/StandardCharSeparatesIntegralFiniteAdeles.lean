import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdCharSep

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_of_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1) : ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
    push_cast
    exact mul_right_cancel₀ hne hn
  exact_mod_cast h2

theorem psi_of_trace_int {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ∃ z : ℤ, Algebra.trace ℚ F x = z) : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 := by
  obtain ⟨z, hz⟩ := h
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, hz, Complex.exp_eq_one_iff]
  exact ⟨z, by push_cast; ring⟩

theorem psi_int_mul {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (s : F)
    (hs : ∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z)
    (w : Af F) (hw : ∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (w * algebraMap F (Af F) s)) = 1 :=
  GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 s (fun a => psi_of_trace_int hψ _ (hs a)) w hw

theorem mem_of_dual (k : F) (h : ∀ s : F, (∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z) →
    ∃ z : ℤ, Algebra.trace ℚ F (k * s) = z) : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = k := by
  have h1 : k ∈ FractionalIdeal.dual ℤ ℚ
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
    rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ (GlobalTheory.AdLat.one_ne_zero_fracIdeal F))]
    intro s hs
    rw [FractionalIdeal.mem_dual (GlobalTheory.AdLat.one_ne_zero_fracIdeal F)] at hs
    obtain ⟨z, hz⟩ := h s (fun a => by
      obtain ⟨y, hy⟩ := hs (a : F) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      refine ⟨y, ?_⟩
      rw [Algebra.traceForm_apply] at hy
      rw [mul_comm, ← hy]
      simp)
    exact ⟨z, by rw [Algebra.traceForm_apply, hz]; simp⟩
  rw [FractionalIdeal.dual_dual] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem exists_sep : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := by
  intro F _ _ ψ hψ b hb
  by_contra H
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) b
  have hbk : b = algebraMap F (Af F) k + (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) := by abel
  obtain ⟨o, ho⟩ := mem_of_dual k (fun s hs => by
    have hb1 : ψ (pairA F 0 (b * algebraMap F (Af F) s)) = 1 := by
      by_contra hne
      exact H ⟨s, hne, fun w hw => psi_int_mul hψ s hs w hw⟩
    have hc1 := psi_int_mul hψ s hs _ hk
    have e : pairA F 0 (b * algebraMap F (Af F) s) = pairA F 0 (algebraMap F (Af F) (k * s)) +
        pairA F 0 ((b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s) := by
      refine Prod.ext (add_zero 0).symm ?_
      show b * algebraMap F (Af F) s = algebraMap F (Af F) (k * s) +
        (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s
      rw [map_mul]
      ring
    rw [e, AddChar.map_add_eq_mul, hc1, mul_one] at hb1
    exact trace_int_of_psi hψ _ hb1)
  apply hb
  intro v
  rw [hbk]
  refine add_mem ?_ (hk v)
  show ((k : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [← ho]
  exact GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v o

end GlobalTheory.StdCharSep
