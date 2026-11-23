import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FrameBack

theorem idAt_of_place {D : D7} (P : Pl D → Prop) (v : Pl D) (hv : P v) {a : AE D} (h : a ∈ idAt D (· = v)) :
    a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h ⊢
  exact ⟨h.1, fun w => h.2 ⟨w.1, fun hw => w.2 (hw ▸ hv)⟩⟩

theorem mem_latV_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (P : Pl D → Prop)
    (v : Pl D) (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (hw ▸ hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => idAt_of_place P v hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem mul_sec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (a : AE D) (x : k) : a * q.sec x = q.sec (q.pr a * x) := by
  have h : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
  have h2 := q.sec_pr (a * q.sec x)
  rw [map_mul, q.pr_sec, mul_left_comm, h] at h2
  exact h2.symm

theorem frame_back : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) (L N : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop), P q.v → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V g L N P → ∀ (Y : Type) [Fintype Y] (β β' : Matrix (Fin V.rank) Y k), β = (Formalism.L2.Theta.mt V g).map q.pr * β' → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V N (· = q.v)) → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β' *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v) := by
  intro D k _ _ _ _ q V g L N P hP hL hN hM Y _ β β' hβ hb y
  have hmv : Formalism.L2.Theta.mt V g *ᵥ (fun i => q.sec ((β' *ᵥ y) i)) = fun i => q.sec ((β *ᵥ y) i) := by
    funext i
    rw [hβ, ← Matrix.mulVec_mulVec]
    generalize β' *ᵥ y = z
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, mul_sec]
  have hu : ∀ i, (fun i => q.sec ((β' *ᵥ y) i)) i ∈ idAt D (· = q.v) := fun i => q.sec_mem_idAt _
  have hu' : ∀ i, (fun i => q.sec ((β *ᵥ y) i)) i ∈ idAt D (· = q.v) := fun i => q.sec_mem_idAt _
  rw [hb y, ← mem_latV_iff V N hN.1 P q.v hP _ hu', ← mem_latV_iff V L hL.1 P q.v hP _ hu,
    hM _ (fun i => idAt_of_place P q.v hP (hu i)), hmv]

end GlobalTheory.FinPl.FrameBack
