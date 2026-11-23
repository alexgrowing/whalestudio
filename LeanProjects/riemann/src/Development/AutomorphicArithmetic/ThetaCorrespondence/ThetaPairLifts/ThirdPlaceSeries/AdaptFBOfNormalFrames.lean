import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.AdaptSplit
open GlobalTheory.FinPl (latV MonoAt PrimAt ColsAt idAt intAt colMul Lat SplitPt)
open GlobalTheory.FinPl.FrameLat
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
end GlobalTheory.Fam.AdaptSplit
open GlobalTheory.Fam.AdaptSplit in
theorem GlobalTheory.Fam.adaptFB_of_normalFrames_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).ψ ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) (PP.under (𝓞 D.host.F)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hT0 hτ hNT hζ hsd hgP htP hdis hPre hOrth hbas FY sc hFr N₁ M₁ hsdN hIntN hsdM hIntM PP hP j σ h
  obtain ⟨hsc, -, hhz, hbes, hjac, -⟩ := hFr PP hP
  have hs := (l PP hP).hs
  have hU := (l PP hP).unit
  rw [← (l PP hP).under]
  have hj1 : j + 1 + (2 * (σ + 1)) = (l PP hP).s + 1 := by omega
  have hj2 : j + 1 + 1 + (2 * σ + 1) = (l PP hP).s + 1 := by omega
  have hJ := hjac j (σ + 1) h (2 * (σ + 1)) hj1
  have hB := hbes (j + 1 + 1) σ (idx_step h) (2 * σ + 1) hj2
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes _ _ _ _ _ hB
  have hM := hIntM PP hP (j + 1 + 1) σ (idx_step h) (by omega) F₀ hF₀
  have hV := hsdN (j + 1) (by omega)
  have hV₀ := (hIs.x (j + 1) (by omega)).sd
  have hW' := hsdN (j + 1 + 1) (by omega)
  have hLJ := line_jac (l PP hP).q hU _ (hsc _) (hhz _ _ _) hJ hV (hIntN PP hP (j + 1) _ hj1)
  have hLB := line_bes (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hW' (hIntN PP hP (j + 1 + 1) _ hj2)
  refine ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hV, hV₀, hW', hsdM _ _ _, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.JacMono.monoAt_of_jacFrame (l PP hP).q hU _ hV hV₀ (hsc _) (hhz _ _ _) hJ (hIntN PP hP (j + 1) _ hj1)
      ((l PP hP).latX (j + 1) (by omega))
  · exact monoAt_of_besFrame (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hF₀ hW' (hsdM _ _ _) (hIntN PP hP (j + 1 + 1) _ hj2) hM
  · exact primAt_of_lines (l PP hP).q hU hIs.std _ _ hLJ
  · intro i b hb
    rw [hU.2, hLJ i b hb]
    exact (hLB i b hb).symm
end
end
