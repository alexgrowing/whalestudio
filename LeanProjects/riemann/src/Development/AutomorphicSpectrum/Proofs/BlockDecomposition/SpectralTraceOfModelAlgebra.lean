import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SpecModel

theorem twTr_unit (hL : LocAlg) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}
    (σ : SmIrr (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) (KL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) :
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hL E n w σ _ hlev f f hf hf
  obtain ⟨h8, -, -, -, -, -, -, h9⟩ := hL E n w σ _ hlev _ _ h7 h7
  have e : ((KL n w : Set (UL n w)).indicator fun _ => (((KL n w).relIndex (KL n w) : ℕ) : ℂ)) =
      (KL n w : Set (UL n w)).indicator 1 := by
    rw [Subgroup.relIndex_self]
    congr 1
    funext _
    simp
  rw [e] at h8 h9
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.finite_of_finrank_pos (by omega)
  rw [h8, h9, LinearMap.trace_one, h1]
  simp

theorem finprod_split {P : Type} (S : Set P) (B : Finset P) (hB : (↑B : Set P) ⊆ S) (F G : P → ℂ)
    (T : {w // w ∈ B} → ℂ) (hT : ∀ w, T w = F w.1) (hG : ∀ w ∈ S, w ∉ B → F w = G w)
    (hfin : ((S \ ↑B) ∩ Function.mulSupport F).Finite) :
    ∏ᶠ w ∈ S, F w = (∏ᶠ w ∈ S \ ↑B, G w) * ∏ w, T w := by
  have hon : ((↑B : Set P) ∩ Function.mulSupport F).Finite := B.finite_toSet.inter_of_left _
  have hB' : ∏ᶠ w ∈ (↑B : Set P), F w = ∏ w, T w := by
    rw [finprod_mem_coe_finset, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun w _ => (hT w).symm
  have hC : ∏ᶠ w ∈ S \ ↑B, F w = ∏ᶠ w ∈ S \ ↑B, G w :=
    finprod_mem_congr rfl fun w hw => hG w hw.1 hw.2
  have hS : ↑B ∪ (S \ ↑B) = S := Set.union_sdiff_cancel hB
  rw [← hS, finprod_mem_union' Set.disjoint_sdiff_right hon hfin, hS, hB', hC, mul_comm]

theorem specTrace : UModel → LocAlg → SpecTrace := by
  intro hU hL E _ _ _ n S B hB K' hK' hKB ι _ σ hfd hone g
  have : ∀ (i : ι) (w : {w // w ∈ B}), FiniteDimensional ℂ (fixed (σ i w.1).ρ (K' w.1)) :=
    fun i w => hfd i w.1 (hB w.2)
  obtain ⟨d, blk, u, h1, h2, h3⟩ := hU ι {w // w ∈ B} (fun i w => ↥(fixed (σ i w.1).ρ (K' w.1)))
    (fun i w => locOp (σ i w.1) (K' w.1) (g w.1))
  refine ⟨d, blk, u, h1, ?_, ?_⟩
  · intro k f hf hloc
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hoff : ((S \ ↑B) ∩ Function.mulSupport
        fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id).Finite := by
      have hev := hK'.2.and hf.2
      rw [Filter.eventually_cofinite] at hev
      refine hev.subset ?_
      rintro w ⟨⟨hwS, hwB⟩, hne⟩ ⟨e1, e2⟩
      apply hne
      have hlev := hK'.1 w
      have hH := hf.1 w
      rw [e1] at hlev hH
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = 1
      rw [e1, e2]
      exact twTr_unit hL (σ i w) hlev (hone i w hwS hwB) hH
    refine finprod_split S B hB (fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id)
      (fun w => twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id)
      (fun w => LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k)) ?_ ?_ hoff
    · intro w
      show LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k) =
        twTr (σ i w.1).ρ (KL n w.1) (K' w.1) (f w.1) LinearMap.id
      rw [← hloc i w.1 w.2]
      exact (hL E n w.1 (σ i w.1) (K' w.1) (hK'.1 w.1) (f w.1) (f w.1) (hf.1 w.1) (hf.1 w.1)).1.symm
    · intro w hwS hwB
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
        twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id
      rw [hKB w hwS hwB]
  · intro i₀ hi
    exact h3 i₀ fun w => hi w.1 w.2

end GlobalTheory.CompanionTheory.SpecModel

end
