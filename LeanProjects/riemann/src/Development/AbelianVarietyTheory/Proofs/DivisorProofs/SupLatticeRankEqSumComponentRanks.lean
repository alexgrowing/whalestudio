import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents

noncomputable section

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem finrank_iSup_of_indep {R V ι : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

theorem rankOn_eq_finrank_span (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ D.host.E) :
    rankOn U Z G = finrank c.F (Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G))) := by
  have hset : (partLat U Z G : Set (cuspW Xo c U G)) =
      Submodule.inclusion (cuspOn_le U Z G) '' (latOn U Z G : Set (cuspOn U Z G)) := by
    simp [partLat]
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.inclusion_injective (cuspOn_le U Z G)) _))

end GlobalTheory.RankAdd

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem cuspOn_comap_indep {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ D.host.E) :
    iSupIndep (fun Z : Comp Xo c => (cuspOn U Z G).comap (cuspW Xo c U G).subtype) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), (cuspOn U j G).comap (cuspW Xo c U G).subtype) ≤
      LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact GlobalTheory.CuspSplit.idem_mul_eq_zero (Ne.symm hj) (Submodule.mem_comap.1 hy)
  have h0 := hle hx'
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply] at h0
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x :=
        (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn (Submodule.mem_comap.1 hx)).symm
    _ = 0 := h0

set_option maxHeartbeats 1000000 in

theorem rankW_eq_finsum_rankOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  intro D H Dw l Xo c r U x V dict G hU hG
  obtain ⟨-, -, -, hsup⟩ := GlobalTheory.CuspSplit.splits D H Dw l Xo c r U V dict hU G
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)

  obtain ⟨-, ⟨s, hs⟩, htop⟩ := hG
  haveI : FiniteDimensional c.F (cuspW Xo c U G) := by
    refine Module.Finite.of_fg_top ⟨s, ?_⟩
    rw [← htop, ← hs, Submodule.span_span_of_tower]
  set S : Comp Xo c → Submodule c.F (cuspW Xo c U G) :=
    fun Z => Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) with hSdef
  have hspan : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⨆ Z, S Z := by
    apply le_antisymm
    · rw [Submodule.span_le, ← hsup]
      intro y hy
      have hle : (⨆ Z : Comp Xo c, partLat U Z G) ≤ (⨆ Z, S Z).restrictScalars (𝓞 c.F) :=
        iSup_le fun Z z hz => (le_iSup S Z) (Submodule.subset_span hz)
      exact hle hy
    · exact iSup_le fun Z => Submodule.span_mono (by rw [← hsup]; exact le_iSup (fun Z => partLat U Z G) Z)
  have hind : iSupIndep S := (cuspOn_comap_indep U G).mono fun Z =>
    Submodule.span_le.2 fun y hy => Submodule.mem_comap.2 (GlobalTheory.CuspSplit.coe_mem_of_mem_partLat hy)
  rw [finsum_eq_sum_of_fintype]
  show finrank c.F (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))) = _
  rw [hspan, finrank_iSup_of_indep S hind]
  exact Finset.sum_congr rfl fun Z _ => (rankOn_eq_finrank_span U Z G).symm

end GlobalTheory.RankAdd
