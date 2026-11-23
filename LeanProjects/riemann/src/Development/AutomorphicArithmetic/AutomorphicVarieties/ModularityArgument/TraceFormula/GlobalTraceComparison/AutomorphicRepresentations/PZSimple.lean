import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zSimple_pf :
    GenLoc → LocComm → SphOp → YLoc → ZSimple := by
  intro hG hC hS hY E _ _ _ n S Z N hSec hZ hN π y W hW hst
  have key : ∀ U : Submodule ℂ (Sm E n), U ≤ y.Y →
      (∀ i, Sl S i → ∀ f, IsHecke (N i.1) f → ∀ x ∈ U, Lw N i.1 i.2 f x ∈ U) →
      U = ⊥ ∨ U = y.Y := by
    intro U hU hUs
    have hgen := hG E n S Z N hSec hZ hN U (hU.trans y.fix) hUs
    have hs := y.simple (U.comap y.Y.subtype) (by
      intro h hh x hx
      have hmem : ((y.r h x : y.Y) : Sm E n) ∈ U := by
        rw [y.act h hh x]
        exact hgen h hh _ hx
      exact hmem)
    rcases hs with hs | hs
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hU hx⟩ : y.Y) ∈ U.comap y.Y.subtype := hx
      rw [hs] at hx'
      have h0 := (Submodule.mem_bot ℂ).1 hx'
      exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val h0)
    · right
      refine le_antisymm hU fun x hx => ?_
      have hx' : (⟨x, hx⟩ : y.Y) ∈ U.comap y.Y.subtype := by
        rw [hs]
        exact Submodule.mem_top
      exact hx'
  have scal : ∀ i, Sl S i → i.1 ∉ Z → ∀ f, IsHecke (N i.1) f →
      ∃ c : ℂ, ∀ x ∈ y.Y, Lw N i.1 i.2 f x = c • x := by
    intro i hi hiZ f hf
    haveI := y.fd
    haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
    have hNw : N i.1 = KGL i.1 n := (hN i.1).2.2.2 hiZ
    let T : Module.End ℂ y.Y := (Lw N i.1 i.2 f).restrict
      (fun x hx => hY E n S Z N hSec hZ hN π y i hi f hf x hx)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    refine ⟨c, ?_⟩
    let U : Submodule ℂ (Sm E n) := y.Y ⊓ LinearMap.ker (Lw N i.1 i.2 f - c • LinearMap.id)
    have memU : ∀ x, x ∈ U ↔ x ∈ y.Y ∧ Lw N i.1 i.2 f x = c • x := by
      intro x
      simp [U, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hcomm : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ y.Y,
        Lw N i.1 i.2 f (Lw N k.1 k.2 g x) = Lw N k.1 k.2 g (Lw N i.1 i.2 f x) := by
      intro k hk g hg x hx
      by_cases hik : i = k
      · subst hik
        have hxf : x ∈ fixed (rw' n i.1 i.2) (N i.1) := ((hC E n S Z N hSec hZ hN i hi f hf).1 x (y.fix hx)).1
        rw [hNw] at hf hg hxf
        simp only [Lw]
        rw [hNw]
        exact hS E n i.1 (Sm E n) (rw' n i.1 i.2) f g hf hg x hxf
      · exact LinearMap.congr_fun ((hC E n S Z N hSec hZ hN i hi f hf).2 k hk hik g hg).eq x
    have hUs : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ U, Lw N k.1 k.2 g x ∈ U := by
      intro k hk g hg x hx
      obtain ⟨hxY, hxe⟩ := (memU x).1 hx
      refine (memU _).2 ⟨hY E n S Z N hSec hZ hN π y k hk g hg x hxY, ?_⟩
      rw [hcomm k hk g hg x hxY, hxe, map_smul]
    have hvU : (v : Sm E n) ∈ U := by
      refine (memU _).2 ⟨v.2, ?_⟩
      have h1 : T v = c • v := hv.apply_eq_smul
      exact congrArg Subtype.val h1
    rcases key U inf_le_left hUs with h0 | h1
    · exfalso
      rw [h0] at hvU
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))
    · intro x hx
      rw [← h1] at hx
      exact ((memU x).1 hx).2
  refine key W hW fun i hi f hf x hx => ?_
  by_cases hiZ : i.1 ∈ Z
  · exact hst i.1 hiZ i.2 f hf x hx
  · obtain ⟨c, hc⟩ := scal i hi hiZ f hf
    rw [hc x (hW hx)]
    exact W.smul_mem c hx
