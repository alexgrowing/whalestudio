import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LatShape

theorem coreFrame_beta_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    {F F' : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F) (h' : p.IsCoreFrame B s FA F') : F.β = F'.β := by
  ext r (a | u)
  · rw [h.1, h'.1]
  · cases u
    rw [h.2, h'.2]

theorem exists_shape_integral_in_normal_frames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) ∧ ∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  have hfin := GlobalTheory.T.level_places_finite W hP
  have hsep := GlobalTheory.T.level_places_under_eq W hP
  have hsc : ∀ PP hP j, sc PP hP j ≠ 0 := by
    intro PP hP j h0
    have := (hFY PP hP).1 j
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hxi : ∀ PP hP, (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro PP hP h0
    have e := (hFY PP hP).2.1 0
    have v2 := (hFY PP hP).1 (0 + 1 + 1)
    rw [e, h0, mul_zero, map_zero] at v2
    exact zero_ne_one v2
  let I := {PP : Pl D.host.E // PP ∈ (pk W).Pg ∨ QAll W PP}
  haveI : Finite I := hfin.to_subtype
  have hinj : ∀ i i' : I, (l i.1 i.2).q.v = (l i'.1 i'.2).q.v → i = i' := by
    intro i i' e
    rw [(l i.1 i.2).under, (l i'.1 i'.2).under] at e
    exact Subtype.ext (hsep _ _ i.2 i'.2 e)
  have hA : ∀ j, ∃ N' : GlobalTheory.FinPl.Lat (Yc D j), (j < D.R.m → IsSelfDualC (Yc D j) N') ∧
      ∀ PP h c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) N' := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.exists_self_dual_lattice_chain W hP j hj
      obtain ⟨N', hsd, hint⟩ := GlobalTheory.T.exists_move_selfDual_lattice_split_frames D (Yc D j) L₀ hL₀ I (fun i => (l i.1 i.2).k) (fun i => (l i.1 i.2).q)
        (fun _ => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (D.R.m - 1 - j))
        (fun i => FY i.1 i.2 j (D.R.m - 1 - j) (by have := (l i.1 i.2).hs; omega)) hinj
      refine ⟨N', fun _ => hsd, fun PP h c hc => ?_⟩
      obtain rfl : c = D.R.m - 1 - j := by have := (l PP h).hs; omega
      exact hint ⟨PP, h⟩
    · refine ⟨⊥, fun h => absurd h hj, fun PP h c hc => ?_⟩
      exfalso
      have := (l PP h).hs
      omega
  choose N₁ hN₁sd hN₁int using hA
  have hB : ∀ j ρ h, ∃ M' : GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀, IsSelfDualC (y.bes j ρ h).V₀ M' ∧
      ∀ PP hP (hj : j ≤ (l PP hP).s + 1)
        (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)),
        (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ →
        IntIn (l PP hP).q _ F₀ M' := by
    intro j ρ h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.local_component_measure_relation W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY j ρ h
    have hj : ∀ i : I, j ≤ (l i.1 i.2).s + 1 := fun i => by have := (l i.1 i.2).hs; omega
    have hex : ∀ i : I, ∃ F : Frame (l i.1 i.2).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit),
        (ofSplit (l i.1 i.2).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc i.1 i.2 j) ((l i.1 i.2).FX j (hj i)) F := by
      intro i
      exact ((@GlobalTheory.LocMod.normalFrames_and_basePoint_exist D (l i.1 i.2).k _ _ _ _ (ofSplit (l i.1 i.2).q)
        (hxi i.1 i.2)).1 _ ρ _ _ _ (hsc i.1 i.2 j)).1
    choose F hF using hex
    obtain ⟨M', hsd, hint⟩ := GlobalTheory.T.exists_move_selfDual_lattice_split_frames D (y.bes j ρ h).V₀ L₀ hL₀ I (fun i => (l i.1 i.2).k) (fun i => (l i.1 i.2).q)
      (fun _ => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit) F hinj
    refine ⟨M', hsd, fun PP hP hj' F₀ hF₀ => ?_⟩
    have e := coreFrame_beta_eq _ _ _ _ (hF ⟨PP, hP⟩) hF₀
    intro z
    rw [← e]
    exact hint ⟨PP, hP⟩ z
  choose M₁ hM₁sd hM₁int using hB
  have hoffT := GlobalTheory.T.local_component_measure_value W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  have hbf := GlobalTheory.T.local_component_measure_bound W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  have hfb := GlobalTheory.T.local_component_measure_scalar W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  have hsp := GlobalTheory.T.local_component_measure_equation W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  let G' : Finset (GlobalTheory.FinPl.Pl D) := hfin.toFinset.image (fun PP => PP.under (𝓞 D.host.F))
  have hG' : ∀ x, x ∈ G' ↔ ∃ PP, (PP ∈ (pk W).Pg ∨ QAll W PP) ∧ PP.under (𝓞 D.host.F) = x := by
    intro x
    simp only [G', Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hdisj' : Disjoint G' v.tP := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    obtain ⟨PP, hPP, rfl⟩ := (hG' x).1 hx
    rcases hPP with hg | hq
    · exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hg, rfl⟩) hxT
    · exact hoffT PP hq hxT
  obtain ⟨N, dT, M, β₀, hN, -, hC, hS⟩ := GlobalTheory.T.seeSawLatticeShapeExists_proof D (commOf (pk W) u (mkGeo m b₀)) { v with gP := G', N := N₁ } k ι
    { o with M := M₁ } hc hdisj' (by show IsSelfDualC D.sp.X' v.NT; rw [hvNT]; exact hLT)
    ⟨hPre.nodup, hPre.all, hPre.inj, hPre.tP, hPre.char, hPre.latT, hPre.line, hPre.tau, hPre.lam, hPre.normT, hPre.topT⟩
    hN₁sd (fun x hx => by
      obtain ⟨PP, hPP, rfl⟩ := (hG' x).1 hx
      exact ⟨⟨hbf PP hPP, hfb PP hPP⟩, ⟨(hsp PP hPP).core, (hsp PP hPP).top⟩⟩)
    (fun n h x hx => by
      obtain ⟨LZ, h1, h2⟩ := hLZ n h x hx
      refine ⟨LZ, h1, ?_⟩
      show GlobalTheory.FinPl.OrthAt _ _ v.NT LZ x
      rw [hvNT]
      exact h2)
  refine ⟨N, dT, M, β₀, ?_, hC, fun j hj => (hN j hj).1, ?_⟩
  · exact ⟨⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, hS.pre.char, hS.pre.latT, hS.pre.line, hS.pre.tau, hS.pre.lam,
      hS.pre.normT, hS.pre.topT⟩, fun x => ⟨(hS.good x).bf, (hS.good x).fb⟩,
      fun x hx => ⟨(hS.split x hx).core, (hS.split x hx).top⟩, hS.glued, hS.rep, hS.ram⟩
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    have hx : (l PP h).q.v ∈ G' := by rw [(l PP h).under]; exact (hG' _).2 ⟨PP, h, rfl⟩
    have e : GlobalTheory.FinPl.latV (Yc D j) (N j) (· = (l PP h).q.v) = GlobalTheory.FinPl.latV (Yc D j) (N₁ j) (· = (l PP h).q.v) :=
      (hN j hj).2 _ hx
    intro z
    rw [e]
    exact hN₁int j PP h c hc z

end GlobalTheory.Fam.LatShape

end
