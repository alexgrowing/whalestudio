import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePatchedAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.ShapeExProof

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem places {v : VCom c} {o : TDat c k ι} (hpre : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨hpre.nodup, hpre.all, hpre.inj, hpre.tP, fun i => (hpre.char i).2⟩

theorem gluedCore_congr {ρ : ℕ} {B : BesLev D ρ} {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {L L' : Lat B.V₀}
    {q : Unif k} {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n}
    (hL : latV B.V₀ L' (· = p.v) = latV B.V₀ L (· = p.v)) (g : GluedCore B L q β β₀ P) : GluedCore B L' q β β₀ P :=
  ⟨g.unit, g.sum, g.norm, fun y => by rw [hL]; exact g.lat y⟩

end GlobalTheory.SeeSaw.ShapeExProof

namespace GlobalTheory.SeeSaw.ShapeExProof

theorem shapeEx : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  intro D c v k _ _ _ _ ι o hc hdisj hNT hpre hNv hgP hLZ
  obtain ⟨N0, M0, β₀, hN0, hgood0, hsplit0, hglued0⟩ := GlobalTheory.T.exists_lattices_goodPosition_all_places D c v k ι o hc hNT hpre hLZ
  have key : ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀),
      (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j) ∧ ∀ x ∈ v.gP, latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
      (∀ j ρ h, ∀ x ∈ v.gP, latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
      (∀ x, GoodAt { v with N := N } { o with M := M } x) ∧
      (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M } x) ∧
      (∀ j ρ h, ∀ x, x ∉ v.gP → latV _ (M j ρ h) (· = x) = latV _ (M0 j ρ h) (· = x)) := by
    rcases v.gP.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
    · refine ⟨N0, M0, fun j hj => ⟨hN0 j hj, fun x hx => by simp [hE] at hx⟩, fun j ρ h x hx => by simp [hE] at hx,
        fun x => ⟨(hgood0 x).1, (hgood0 x).2⟩, fun x hx => ⟨(hsplit0 x hx).1, (hsplit0 x hx).2⟩, fun _ _ _ _ _ => rfl⟩
    · have hsdM : ∀ j ρ h, IsSelfDualC _ (o.M j ρ h) := fun j ρ h => ((hgP x0 hx0).1.bf j ρ h).sdV₀
      have hsdM0 : ∀ j ρ h, IsSelfDualC _ (M0 j ρ h) := fun j ρ h => ((hgood0 x0).bf j ρ h).sdV₀
      have hpN : ∀ j, ∃ L : Lat (c.V j), j < D.R.m → (IsSelfDualC (c.V j) L ∧
          (∀ x ∈ v.gP, latV (c.V j) L (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV (c.V j) L (· = x) = latV (c.V j) (N0 j) (· = x)) := by
        intro j
        by_cases hj : j < D.R.m
        · obtain ⟨L, h1, h2, h3⟩ := GlobalTheory.T.exists_selfDual_lattice_patched_at_places D (c.V j) (N0 j) (v.N j) (hN0 j hj) (hNv j hj) v.gP
          exact ⟨L, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨N0 j, fun h => absurd h hj⟩
      choose N hN using hpN
      have hpM : ∀ j ρ h, ∃ L : Lat (c.bes j ρ h).V₀, IsSelfDualC _ L ∧
          (∀ x ∈ v.gP, latV _ L (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV _ L (· = x) = latV _ (M0 j ρ h) (· = x) := fun j ρ h =>
        GlobalTheory.T.exists_selfDual_lattice_patched_at_places D _ (M0 j ρ h) (o.M j ρ h) (hsdM0 j ρ h) (hsdM j ρ h) v.gP
      choose M hM using hpM
      have hat : ∀ x, (x ∈ v.gP → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x)) ∧
          (x ∉ v.gP → (GoodAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → SplitAt { v with N := N } { o with M := M } x)) := by
        intro x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c v k ι o N M x (fun j hj => ⟨hNv j hj, (hN j hj).1, (hN j hj).2.1 x hx⟩)
            (fun j ρ h => ⟨hsdM j ρ h, (hM j ρ h).1, (hM j ρ h).2.1 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c { v with N := N0 } k ι { o with M := M0, β₀ := β₀ } N M x
            (fun j hj => ⟨hN0 j hj, (hN j hj).1, (hN j hj).2.2 x hx⟩)
            (fun j ρ h => ⟨hsdM0 j ρ h, (hM j ρ h).1, (hM j ρ h).2.2 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
      refine ⟨N, M, fun j hj => ⟨(hN j hj).1, (hN j hj).2.1⟩, fun j ρ h => (hM j ρ h).2.1, fun x => ?_, fun x hxT => ?_,
        fun j ρ h => (hM j ρ h).2.2⟩
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).1 (hgP x hx).1
        · exact ((hat x).2 hx).1 (hgood0 x)
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).2 (hgP x hx).2
        · exact ((hat x).2 hx).2 (hsplit0 x hxT)
  obtain ⟨N, M, hN, hM, hgood, hsplit, hoff⟩ := key
  have hd : ∀ j, ∃ d : WO (c.X j) (c.X (j + 1)) →₀ ℂ, CombAt (· ∈ v.tP) d ∧ (j < D.R.m → ∀ f,
      Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L (· ∈ v.tP) f →
      OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
        (comb c.ψ _ _ d f)) := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨d, hdc, hdr⟩ := ((GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D) k ι o.p o.I (· ∈ v.tP) (places hpre) (Fin (c.X (j + 1)).rank)
        (Fin (c.X j).rank) c.ψ hc.std (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L
        (hc.x j hj.le).sd (hc.x (j + 1) hj).sd (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).1 (fun i => GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)
      exact ⟨d, hdc, fun _ => hdr⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hj⟩
  choose dT hdC hdR using hd
  have hpT : ∀ i, (o.p i).v ∉ v.gP := fun i hg =>
    Finset.disjoint_left.mp hdisj hg ((hpre.tP _).mpr ⟨i, rfl⟩)
  refine ⟨N, dT, M, β₀, hN, hM, hdC, ⟨⟨hpre.1, hpre.2, hpre.3, hpre.4, hpre.5, hpre.6, hpre.7, hpre.8, hpre.9, hpre.10, hpre.11⟩,
    fun x => ⟨(hgood x).1, (hgood x).2⟩, fun x hx => ⟨(hsplit x hx).1, (hsplit x hx).2⟩,
    fun j ρ h i => gluedCore_congr (hoff j ρ h _ (hpT i)) (hglued0 j ρ h i), fun j hj => hdR j hj, fun j => rfl⟩⟩

end GlobalTheory.SeeSaw.ShapeExProof
