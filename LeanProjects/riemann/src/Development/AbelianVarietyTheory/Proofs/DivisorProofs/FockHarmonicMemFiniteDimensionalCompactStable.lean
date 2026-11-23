import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.FockAlg.HarmStable MvPolynomial

namespace GlobalTheory.FockAlg.FinHarm

variable {σ : Type}

def lowDeg (σ : Type) (N : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨆ d : Fin (N + 1), homog σ d

instance [Finite σ] (N : ℕ) : FiniteDimensional ℂ (lowDeg σ N) := by
  haveI : ∀ d : ℕ, FiniteDimensional ℂ (homog σ d) := fun d =>
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  unfold lowDeg
  infer_instance

theorem mem_lowDeg_self (P : MvPolynomial σ ℂ) : P ∈ lowDeg σ P.totalDegree := by
  obtain ⟨N, hN⟩ : ∃ N, N = P.totalDegree := ⟨_, rfl⟩
  rw [← hN]
  have hs := sum_homogeneousComponent P
  rw [← hN] at hs
  rw [← hs]
  refine Submodule.sum_mem _ fun e he => ?_
  have he' : e < N + 1 := Finset.mem_range.1 he
  exact Submodule.mem_iSup_of_mem (⟨e, he'⟩ : Fin (N + 1))
    (homogeneousComponent_mem e P)

theorem DegZero.map_lowDeg {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (N : ℕ)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowDeg σ N) : K P ∈ lowDeg σ N := by
  have hle : lowDeg σ N ≤ (lowDeg σ N).comap K :=
    iSup_le fun d x hx => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem d (hK d x hx))
  exact hle hP

end GlobalTheory.FockAlg.FinHarm

namespace GlobalTheory.FockAlg

open FinHarm

theorem fin_harm : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧
      (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧
      KStable (fockAct2 P Q R S) H0 := by
  intro P Q R S h hh
  have hh' : h ∈ sub2 P Q R S := by
    rw [← SetLike.mem_coe, coe_fockHarmonicsSecondMemberSubmodule]; exact hh
  refine ⟨sub2 P Q R S ⊓ lowDeg _ h.totalDegree, ?_, ⟨hh', mem_lowDeg_self h⟩, ?_, ?_, ?_⟩
  · exact Submodule.finiteDimensional_of_le inf_le_right
  · intro v hv
    rw [← coe_fockHarmonicsSecondMemberSubmodule]; exact hv.1
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct1 hY) _ hw.2⟩
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct2 hY) _ hw.2⟩

end GlobalTheory.FockAlg
