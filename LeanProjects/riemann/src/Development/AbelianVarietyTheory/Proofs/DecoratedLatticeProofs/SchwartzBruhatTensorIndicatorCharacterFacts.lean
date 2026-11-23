import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

noncomputable section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix

namespace GlobalTheory.FinPl.SBFacts

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem charInd_mem (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hK : IsCompact (Q.lat : Set (n → k)) := GlobalTheory.FinPl.Comm.isCompact_lat Q.lat
  refine ⟨?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
    by_cases hy : y ∈ Q.lat
    · refine ⟨(fun z => z - y) ⁻¹' (Q.ker : Set (n → k)), (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat Q.ker).preimage (by fun_prop),
        by simp [Q.ker.zero_mem], fun z hz => ?_⟩
      have hw : Q.HasVal (z - y) 0 := Pair.mem_ker.1 hz
      have hz' : Q.HasVal z (Q.ev y) := by
        simpa using hw.add (Pair.hasVal_ev hy)
      have hzl : z ∈ Q.lat := hz'.mem
      simp only [charInd, vecInd, if_pos hzl, if_pos hy, hz'.ev_eq]
    · refine ⟨(Q.lat : Set (n → k))ᶜ, hK.isClosed.isOpen_compl, hy, fun z hz => ?_⟩
      have hz' : z ∉ Q.lat := hz
      simp only [charInd, vecInd, if_neg hz', if_neg hy, mul_zero]
  · have hy' : y ∉ Q.lat := hy
    simp only [charInd, vecInd, if_neg hy', mul_zero]

end GlobalTheory.FinPl.SBFacts

theorem GlobalTheory.FinPl.sb_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) →
      GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧
    ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, fun Λ hΛ => ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  haveI := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
