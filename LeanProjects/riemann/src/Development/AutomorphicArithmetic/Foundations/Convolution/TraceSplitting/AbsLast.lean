import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PowIndep
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CharIndep
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.AutomorphicForms.MeasuresGL

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}

private theorem fixed_fd (U : Subgroup (Gw n v)) (hU : CO U) (σ : SmIrr (Gw n v)) :
    FiniteDimensional ℂ (fixedVectors σ.ρ U) := by
  have h := PositivityTheory.Exh.irreducibleAdmissibleGL (v.adicCompletion K) n σ.V σ.ρ σ.smooth σ.irred
  have h2 := h.2 U hU.2 hU.1
  have e : GlobalTheory.PRep.fixed σ.ρ U = fixedVectors σ.ρ U := by
    ext x
    constructor
    · intro hx g hg
      simpa using hx ⟨g, hg⟩
    · intro hx g
      simpa using hx g g.2
  rw [← e]
  exact h2

private theorem td : TotallyDisconnectedSpace (Gw n v) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → v.adicCompletion K))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

open UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed in
theorem UpperTheory.ConvolutionTheory.T.absLast :
    UpperTheory.ConvolutionTheory.T.AbsLast := by
  intro K _ _ n v _ _ m _ U hU ι _ τ a Z τ₀ c Z₀ hc hZ₀ h0 hZ hfix hid
  by_contra hno
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ₀
  have hk : ((Multiset.filter (· = ζ) Z₀).card : ℂ) ≠ 0 := by
    have : 0 < (Multiset.filter (· = ζ) Z₀).card :=
      Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
    exact_mod_cast this.ne'
  let σ : Option ι → SmIrr (Gw n v) := fun o => o.elim τ₀ τ
  let C : Option ι → ℂ := fun o => o.elim (c * ((Multiset.filter (· = ζ) Z₀).card : ℂ))
    (fun i => -(a i * ((Multiset.filter (· = ζ) (Z i)).card : ℂ)))
  haveI : m.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL (v.adicCompletion K) n m
  haveI : LocallyCompactSpace (Gw n v) :=
    hU.1.locallyCompactSpace_of_mem_nhds_of_group (hU.2.mem_nhds U.one_mem)
  haveI : T2Space (Gw n v) := Units.isEmbedding_embedProduct.t2Space
  haveI : TotallyDisconnectedSpace (Gw n v) := td
  have key := UpperTheory.ConvolutionTheory.C.charIndep (Gw n v) m U hU (Option ι) σ C (fun o => fixed_fd U hU (σ o)) ?_ none hfix
  · have hset : {o : Option ι | Nonempty ((σ o).ρ.Equiv (σ none).ρ)} = {none} := by
      ext o
      cases o with
      | none => exact ⟨fun _ => rfl, fun _ => ⟨Representation.Equiv.refl (σ none).ρ⟩⟩
      | some i =>
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, reduceCtorEq, iff_false]
        exact fun h => hno ⟨i, h⟩
    rw [hset, finsum_mem_singleton] at key
    exact (mul_ne_zero hc hk) key
  · intro φ s hφ hinv hs
    have e := hid φ (s none) (fun i => s (some i)) hφ hinv (hs none) (fun i => hs (some i))
    have p := UpperTheory.ConvolutionTheory.C.powIndep (Option ι)
      (fun o => o.elim (c * s none) (fun i => -(a i * s (some i))))
      (fun o => o.elim Z₀ Z)
      (fun o => by cases o with
        | none => exact h0
        | some i => exact hZ i)
      (by
        filter_upwards [e] with j hj
        rw [Fintype.sum_option]
        simp only [Option.elim]
        have : ∑ i, -(a i * s (some i)) * ((Z i).map (· ^ j)).sum
            = -∑ i, a i * ((Z i).map (· ^ j)).sum * s (some i) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [this, ← hj]
        ring) ζ
    rw [Fintype.sum_option] at p ⊢
    simp only [Option.elim] at p
    have : ∑ i, C (some i) * s (some i)
        = ∑ i, -(a i * s (some i)) * ((Multiset.filter (· = ζ) (Z i)).card : ℂ) :=
      Finset.sum_congr rfl (fun i _ => by simp only [C, Option.elim]; ring)
    rw [this]
    have h1 : C none = c * ((Multiset.filter (· = ζ) Z₀).card : ℂ) := rfl
    rw [h1]
    linear_combination p
