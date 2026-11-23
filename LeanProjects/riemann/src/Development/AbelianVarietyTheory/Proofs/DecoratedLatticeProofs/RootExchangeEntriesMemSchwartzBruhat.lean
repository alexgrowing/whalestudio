import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EntrySB
open scoped Pointwise

theorem exists_nhds_add_eq {M E : Type*} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Zero E]
    {F : M → E} (hl : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ V ∈ nhds (0 : M), ∀ x, ∀ v ∈ V, F (x + v) = F x := by
  letI : TopologicalSpace E := ⊥
  haveI : DiscreteTopology E := ⟨rfl⟩
  have hT : (F '' tsupport F).Finite := (hc.isCompact.image hl.continuous).finite_of_discrete
  have hsep : ∀ a : E, ∃ W ∈ nhds (0 : M), a ≠ 0 → F ⁻¹' {a} + W ⊆ F ⁻¹' {a} := by
    intro a
    by_cases ha : a = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h ha).elim⟩
    · have hsub : F ⁻¹' {a} ⊆ tsupport F := fun y hy =>
        subset_tsupport F (by simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy; simp [Function.mem_support, hy, ha])
      have hK : IsCompact (F ⁻¹' {a}) := hc.isCompact.of_isClosed_subset (hl.isClopen_fiber a).isClosed hsub
      obtain ⟨W, hW, hW'⟩ := compact_open_separated_add_right hK (hl.isOpen_fiber a) le_rfl
      exact ⟨W, hW, fun _ => hW'⟩
  choose W hW hWs using hsep
  refine ⟨⋂ a ∈ F '' tsupport F, (W a ∩ -W a), (Filter.biInter_mem hT).2 fun a _ =>
    Filter.inter_mem (hW a) (neg_mem_nhds_zero M (hW a)), ?_⟩
  intro x v hv
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_neg] at hv
  by_cases hx : F x = 0
  · by_contra hne
    have hxv : x + v ∈ tsupport F := subset_tsupport F (by rw [Function.mem_support]; rwa [hx] at hne)
    have hb : F (x + v) ≠ 0 := fun h => hne (h.trans hx.symm)
    have := hWs (F (x + v)) hb (Set.add_mem_add (a := x + v) (b := -v) rfl (hv _ ⟨_, hxv, rfl⟩).2)
    simp only [add_neg_cancel_right, Set.mem_preimage, Set.mem_singleton_iff] at this
    exact hne this.symm
  · have hxs : x ∈ tsupport F := subset_tsupport F hx
    have := hWs (F x) hx (Set.add_mem_add (a := x) (b := v) rfl (hv _ ⟨_, hxs, rfl⟩).1)
    simpa using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Aff
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem affPt_add (p : ℕ) (x₀ v : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p (x₀ + v) e = affPt p x₀ e + fromBlocks v 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> simp [affPt, basePt] <;> ring

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem ch_fromBlocks (v : Matrix n n' k) :
    ch (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) = 0 := by
  simp [ch]

theorem corner_affPt (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    (Matrix.of fun i j => affPt p x₀ e (Sum.inl i) (Sum.inl j)) = x₀ := by
  ext i j
  simp [affPt, basePt, Free]

variable [MeasurableSpace k] [BorelSpace k]

theorem opE_mem_SB (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hF : F ∈ SB _) :
    GlobalTheory.RootEx.opE ψ ν p F ∈ SB (Matrix n n' k) := by
  obtain ⟨hl, hc⟩ := hF
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hVF⟩ := exists_nhds_add_eq hl hc
    have hι : Continuous fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
      continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const
    have hW : (fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) ⁻¹' V ∈ nhds (0 : Matrix n n' k) := by
      apply hι.continuousAt.preimage_mem_nhds
      simpa [fromBlocks_zero] using hV
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
    rw [← map_add_left_nhds_zero x₀, Filter.eventually_map]
    filter_upwards [hW] with v hv
    simp only [GlobalTheory.RootEx.opE]
    congr 1
    funext e
    rw [affPt_add, hVF _ _ hv, ch_add, ch_fromBlocks, add_zero]
  · have hpr : Continuous fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        (Matrix.of fun i j => M (Sum.inl i) (Sum.inl j) : Matrix n n' k) :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    refine HasCompactSupport.intro (hc.isCompact.image hpr) fun x₀ hx₀ => ?_
    have h0 : ∀ e, F (affPt p x₀ e) = 0 := fun e => image_eq_zero_of_notMem_tsupport fun hm =>
      hx₀ ⟨_, hm, corner_affPt p x₀ e⟩
    simp [GlobalTheory.RootEx.opE, h0]

end Aff

end GlobalTheory.EntrySB

open GlobalTheory.EntrySB in

theorem GlobalTheory.StepData.xi_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle), Continuous ψ →
  ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ _ ν _ μ Φ J b h' h
  have := Submodule.smul_mem (SB (Matrix n n' k)) ((((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ))
    (opE_mem_SB ψ ν 1 (GlobalTheory.SplitWeil.om_mem_SB μ h' h Φ.2))
  convert this using 1
  funext x
  simp [xi, flat]
