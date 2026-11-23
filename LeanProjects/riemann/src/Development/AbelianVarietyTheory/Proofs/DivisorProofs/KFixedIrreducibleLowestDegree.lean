import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterComponentDegreeLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleTensorInvariantSubspaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section

namespace GlobalTheory.KFixIrr

open Formalism.BasicNotions.TH

theorem tprod_mem_chiPart {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (x : ι → ℚ)
    (g : ι → Pol P Q R S) (hg : ∀ w, g w ∈ chiOne P Q R S (x w)) :
    PiTensorProduct.tprod ℂ g ∈ chiPart ι P Q R S x := by
  rw [mem_chiPart]
  intro w X hX
  rw [GlobalTheory.TensIrr.atPl_tprod, (mem_chiOne _ _).1 (hg w) X hX, MultilinearMap.map_update_smul,
    Function.update_eq_self]

theorem tprod_ne_zero' {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (v : ι → V)
    (hv : ∀ w, v w ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h
  have := congrArg (GlobalTheory.TensIrr.prodForm (V := fun _ : ι => V) ℓ) h
  rw [GlobalTheory.TensIrr.prodForm_tprod, map_zero] at this
  simp [hℓ] at this

theorem lowest_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (x : ι → ℚ), P ≤ R → Q ≤ S →
    (∀ w, ∃ k k' : ℕ, 0 < k ∧ 0 < k' ∧ x w - Formalism.BasicNotions.TH.cPair R S = k ∧ x w + Formalism.BasicNotions.TH.cPair R S = k') →
    ∀ m : ℕ, (∀ m' < m, GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m' = ⊥) →
    ∀ N : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S),
      N ≤ GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
      (∀ w (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T ∈ N) →
      N = ⊥ ∨ N = GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m := by
  intro ι _ _ P Q R S x hPR hQS hx m hm N hN hNst
  choose k k' hk hk' ek ek' using hx
  let d : ι → ℕ := fun w => P * k w + Q * k' w
  let H : ι → Submodule ℂ (Pol P Q R S) := fun w => lowOne P Q R S (x w) (d w)

  have low : ∀ n (g : ι → Pol P Q R S), (∀ w, g w ∈ chiOne P Q R S (x w)) → ∑ w, (g w).totalDegree ≤ n →
      PiTensorProduct.tprod ℂ g = 0 ∨ (∑ w, d w ≤ n ∧ (n = ∑ w, d w → ∀ w, g w ∈ H w)) := by
    intro n g hg hs
    by_cases h0 : ∃ w, g w = 0
    · obtain ⟨w, hw⟩ := h0
      exact Or.inl (MultilinearMap.map_coord_zero _ w hw)
    push_neg at h0
    have hle : ∀ w, d w ≤ (g w).totalDegree := fun w => GlobalTheory.T.character_component_degree_lower_bound P Q R S (x w) (k w) (k' w) (ek w) (ek' w) (g w) (hg w) (h0 w)
    have hsum : ∑ w, d w ≤ ∑ w, (g w).totalDegree := Finset.sum_le_sum fun w _ => hle w
    refine Or.inr ⟨hsum.trans hs, fun hn w => ?_⟩
    have heq : ∑ w, d w = ∑ w, (g w).totalDegree := le_antisymm hsum (hn ▸ hs)
    have := (Finset.sum_eq_sum_iff_of_le (fun w _ => hle w)).1 heq w (Finset.mem_univ w)
    exact (mem_lowOne _ _ _).2 ⟨hg w, this.symm.le⟩
  have below : ∀ n < ∑ w, d w, chiPart ι P Q R S x ⊓ degLE ι P Q R S n = ⊥ := by
    intro n hn
    rw [eq_bot_iff]
    intro T hT
    have := GlobalTheory.T.character_part_tensor_span ι P Q R S x n T hT
    rw [Submodule.mem_bot]
    refine (Submodule.span_le.2 ?_ : _ ≤ ⊥) this
    rintro _ ⟨g, hg, hs, rfl⟩
    rcases low n g hg hs with h | h
    · simp [h]
    · exact absurd h.1 (not_le.2 hn)
  have atD : chiPart ι P Q R S x ⊓ degLE ι P Q R S (∑ w, d w) = tensSpan H := by
    apply le_antisymm
    · intro T hT
      refine (Submodule.span_le.2 ?_) (GlobalTheory.T.character_part_tensor_span ι P Q R S x _ T hT)
      rintro _ ⟨g, hg, hs, rfl⟩
      rcases low _ g hg hs with h | h
      · simp [h]
      · exact tprod_mem_tensSpan H g (h.2 rfl)
    · rw [tensSpan, Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨tprod_mem_chiPart x g fun w => ((mem_lowOne _ _ _).1 (hg w)).1, tprod_mem_degLE g ?_⟩
      exact Finset.sum_le_sum fun w _ => ((mem_lowOne _ _ _).1 (hg w)).2
  have hne : ∀ w, H w ≠ ⊥ := fun w => GlobalTheory.T.lowest_degree_component_nonzero P Q R S (x w) (k w) (k' w) hPR hQS (hk w) (hk' w) (ek w) (ek' w)
  have spanne : tensSpan H ≠ ⊥ := by
    choose v hv hv0 using fun w => Submodule.exists_mem_ne_zero_of_ne_bot (hne w)
    intro h
    have := tprod_mem_tensSpan H v hv
    rw [h, Submodule.mem_bot] at this
    exact tprod_ne_zero' v hv0 this
  rcases lt_trichotomy m (∑ w, d w) with hlt | heq | hgt
  · left
    rw [eq_bot_iff]
    exact hN.trans (below m hlt).le
  · subst heq
    rw [atD] at hN ⊢
    haveI : ∀ w, FiniteDimensional ℂ (H w) := fun w =>
      Submodule.finiteDimensional_of_le (inf_le_right : H w ≤ MvPolynomial.restrictTotalDegree (Ln P Q R S) ℂ (d w))
    exact GlobalTheory.T.irreducible_tensor_invariant_subspace ι (Pol P Q R S) {Z : Mat R S // IsKC Z} (fun _ z => fockAct2 P Q R S z.1) H (fun w => inferInstance) hne
      (fun w z v hv => GlobalTheory.T.lowest_degree_component_invariant P Q R S (x w) (d w) z.1 z.2 v hv)
      (fun w N' hN' hst => GlobalTheory.T.lowest_degree_component_irreducible P Q R S (x w) (k w) (k' w) hPR hQS (hk w) (hk' w) (ek w) (ek' w) N' hN'
        (fun Z hZ f hf => hst ⟨Z, hZ⟩ f hf))
      N hN (fun w z T hT => hNst w z.1 z.2 T hT)
  · exact absurd (atD ▸ hm _ hgt) spanne

end GlobalTheory.KFixIrr

end
