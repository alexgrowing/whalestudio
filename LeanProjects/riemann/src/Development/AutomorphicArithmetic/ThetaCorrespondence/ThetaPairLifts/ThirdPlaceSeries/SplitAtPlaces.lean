import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TuplePlaceUnderNotMemTP

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitAtPlaces
theorem splitAt_places_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), SplitAt { v with N := N₁ } { o with M := M₁ } (PP.under (𝓞 D.host.F)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ hbas FY sc hFY N₁ M₁ hN₁ hFYN hM₁ hcore PP hP
  have hq : (l PP hP).q.v = PP.under (𝓞 D.host.F) := (l PP hP).under
  obtain ⟨hsc, hstep, hhz, -, -, hτ⟩ := hFY PP hP
  have hξ : valuation (l PP hP).k (ofSplit (l PP hP).q).xi = 1 := by
    have h1 := hsc (0 + 1 + 1)
    rw [hstep 0, map_mul, hsc 0, one_mul] at h1
    exact h1
  have hxi : (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ
    exact zero_ne_one hξ
  have key : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ LL : GlobalTheory.FinPl.Lat (y.bes j ρ h).L, IsSelfDualC _ LL ∧
      GlobalTheory.FinPl.OrthAt (y.bes j ρ h).o (M₁ j ρ h) (a.x j).L LL (l PP hP).q.v ∧
      ∀ t : (l PP hP).k, (t ∈ 𝒪[(l PP hP).k] ↔ (fun i => (l PP hP).q.sec
        ((fun i => sc PP hP j * (ofSplit (l PP hP).q).pr ((y.bes j ρ h).ζ i)) i * t)) ∈ GlobalTheory.FinPl.latV _ LL (· = (l PP hP).q.v)) := by
    intro j ρ h
    have hj : j ≤ (l PP hP).s + 1 := by have := (l PP hP).hs; omega
    have hs0 : sc PP hP j ≠ 0 := by
      intro h0
      have h1 := hsc j
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (l PP hP).k (ofSplit (l PP hP).q) hxi).1 _ ρ ((y.bes j ρ h).lev (a.x j).vol)
      (sc PP hP j) ((l PP hP).FX j hj) hs0).1
    have hIntM := hcore PP hP j ρ h hj F₀ hF₀
    have hA : IsSelfDualC (D.sp.X j) (a.x j).L := (hIs.x j (by omega)).sd
    refine GlobalTheory.T.exists_selfDualLineLattice_splitting_sum D (l PP hP).k (l PP hP).q (y.bes j ρ h).V₀ (D.sp.X j) (y.bes j ρ h).L (y.bes j ρ h).o (M₁ j ρ h)
      (a.x j).L _ ((l PP hP).FX j hj) F₀ _ (hM₁ j ρ h) hA ⟨_, GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D _⟩ hF₀.1 (fun r => ?_)
      hIntM ((l PP hP).latX j hj)
    rw [hF₀.2 r]
    simp only [GlobalTheory.MixPer.vecB, Matrix.mulVec, dotProduct, Matrix.map_apply, GlobalTheory.LocMod.Place.pr, map_sum, map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hx : PP.under (𝓞 D.host.F) ∉ v.tP := by
    rcases hP with hP' | hP'
    · intro ht
      exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hP', rfl⟩) ht
    · exact _root_.GlobalTheory.tuplePlace_under_notMem_tP_alt W u hW a y m b₀ k ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ
        hbas FY sc hFY PP hP'
  refine ⟨fun j ρ h => ?_, fun j h => ?_⟩
  · obtain ⟨LL, hLL, hO, -⟩ := key j ρ h
    exact ⟨LL, hLL, hq ▸ hO⟩
  · have hjs : j = (l PP hP).s := by have := (l PP hP).hs; omega
    subst hjs
    obtain ⟨LL, hLL, hO, hLLw⟩ := key _ 0 h
    obtain ⟨LZ₀, hLZ₀, -⟩ := hLZ _ h (l PP hP).q.v (hq ▸ hx)
    obtain ⟨LZ, hLZsd, hLZO, hLZw⟩ := GlobalTheory.T.exists_selfDualLineLattice_splitting_sum D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1 + 1)) D.sp.X' a.Lz
      (a.oT _ h) (a.x ((l PP hP).s + 1 + 1)).L a.LT _ (l PP hP).FT (l PP hP).FM
      (fun i => (ofSplit (l PP hP).q).pr (a.ζ₀ i)) (hIs.x _ (by omega)).sd hsdT ⟨LZ₀, hLZ₀⟩
      (fun r b => by rw [(l PP hP).last]; rfl) (fun r => by rw [(l PP hP).last]; rfl) (l PP hP).latM (l PP hP).latT
    refine ⟨LL, LZ, hLL, hLZsd, hq ▸ hO, hNT ▸ hq ▸ hLZO, ?_⟩
    intro w hw
    rw [← hq] at hw ⊢
    rw [hvτ]
    have hmap := GlobalTheory.T.splitPlace_line_similitude_maps_selfDual_lattice D (l PP hP).k (l PP hP).q (y.bes _ 0 h).L a.Lz (y.τ _ h) LL LZ _ _ (-(ofSplit (l PP hP).q).xi)
      (l PP hP).unit hLL hLZsd (y.bes _ 0 h).line.1 hpre.line.1 hLLw hLZw (by rw [Valuation.map_neg]; exact hξ)
      (by rw [hτ h]; funext i; simp only [Pi.smul_apply, smul_eq_mul]; ring) (hTau _ h).1
    exact GlobalTheory.T.lineHomAdjointTwist_mem_completedHomLattice D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1)) (y.bes _ 0 h).L a.Lz (y.τ _ h)
      (a.x ((l PP hP).s + 1)).L LL LZ (l PP hP).unit (hIs.x _ (by omega)).sd hLL hLZsd hmap w hw
end GlobalTheory.SplitAtPlaces
end
