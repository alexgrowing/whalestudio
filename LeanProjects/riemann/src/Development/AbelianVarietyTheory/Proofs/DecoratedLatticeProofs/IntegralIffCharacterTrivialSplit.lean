import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIntChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_of_le_one {ψk : AddChar k Circle} (hc : HasConductor ψk 1) {y : k} (hy : valuation k y ≤ 1) : ψk y = 1 :=
  (hc 1).2 (by simp) y (by simpa using hy)

theorem trivial_iff_mem {ψk : AddChar k Circle} (hc : HasConductor ψk 1) {ξ : k} (hξ : valuation k ξ = 1) (t : k) :
    (∀ c ∈ 𝒪[k], ψk (t * c / ξ) = 1) ↔ t ∈ 𝒪[k] := by
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hξ
  constructor
  · intro h
    by_cases ht : t = 0
    · rw [ht]; exact zero_mem _
    have h1 := (hc (t / ξ)).1 (fun y hy => by
      have hc' : y * ξ / t ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_div₀, map_mul, hξ, mul_one]
        rw [map_div₀, hξ, div_one] at hy
        exact div_le_one_of_le₀ hy zero_le'
      have := h _ hc'
      rwa [show t * (y * ξ / t) / ξ = y by field_simp] at this)
    rw [Valuation.mem_integer_iff]
    simpa [map_div₀, hξ] using h1
  · intro ht c hc'
    apply triv_of_le_one hc
    rw [map_div₀, hξ, div_one]
    exact (Valuation.mem_integer_iff _ _).1 (mul_mem ht hc')

theorem int_iff_psiE : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), valuation k ((ofSplit q).xi) = 1 → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ s ∈ GlobalTheory.FinPl.idAt D (· = q.v), (s ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ ∀ o ∈ GlobalTheory.FinPl.intAt D (· = q.v), psiE ψ (s * o) = 1) := by
  intro D k _ _ _ _ q ψ ψk hξ hχ hc s hs
  have hι : ∀ y, psiE ψ (q.sec y) = ψk (y / (ofSplit q).xi) := fun y => GlobalTheory.LocBesChar.psiE_ι (ofSplit q) hχ y
  have hone : ∀ y, valuation k y ≤ 1 → psiE ψ (q.sec y) = 1 := fun y hy => by
    rw [hι, triv_of_le_one hc (by rw [map_div₀, hξ, div_one]; exact hy)]; rfl
  constructor
  · intro hsI o ho
    have hso : s * o ∈ GlobalTheory.FinPl.idAt D (· = q.v) := Ideal.mul_mem_right _ _ hs
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitIntComp.mem_intAt_iff q hs).1 hsI
    obtain ⟨h3, h4⟩ := (GlobalTheory.SplitIntComp.mem_intAt_iff q ho.1).1 ho
    rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q hso, psiE_add, GlobalTheory.LocBesChar.psiE_cA, hone, hone, one_mul]
    · rw [map_mul, map_mul]; exact (Valuation.mem_integer_iff _ _).1 (mul_mem h2 h4)
    · rw [map_mul]; exact (Valuation.mem_integer_iff _ _).1 (mul_mem h1 h3)
  · intro h
    rw [GlobalTheory.SplitIntComp.mem_intAt_iff q hs]
    constructor
    · rw [← trivial_iff_mem hc hξ]
      intro c hc'
      have hm : q.sec c ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
        simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff q 1 c).2 (by simpa using hc')
      have := h _ hm
      rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right, hι, mul_comm c] at this
      exact Circle.coe_inj.1 (this.trans Circle.coe_one.symm)
    · rw [← trivial_iff_mem hc hξ]
      intro c hc'
      have hm : cA D (q.sec c) ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
        simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff q 1 c).2 (by simpa using hc')
      have := h _ hm
      rw [mul_comm, GlobalTheory.Core.Mi.LatMatch.cA_sec_mul, GlobalTheory.LocBesChar.psiE_cA, hι, mul_comm c] at this
      exact Circle.coe_inj.1 (this.trans Circle.coe_one.symm)

end GlobalTheory.SplitIntChar

end
