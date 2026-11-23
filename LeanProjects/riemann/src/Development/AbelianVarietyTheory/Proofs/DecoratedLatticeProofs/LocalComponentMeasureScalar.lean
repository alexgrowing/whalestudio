import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfJacFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfSplitW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMemLatVIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJacFramePairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumPrStar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BeszPairings
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.AdaptSplit

open GlobalTheory.FinPl (latV MonoAt PrimAt ColsAt idAt intAt colMul Lat SplitPt)
open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem monoAt_of_besFrame (hU : q.UnitAA) {σ : ℕ} (B : BesLev D σ) {n : Type} [Fintype n] [DecidableEq n] {s : k}
    (hs : valuation k s = 1) (hz : valuation k ((ofSplit q).hz B) = 1) {FA : Frame k B.A.rank n}
    {F : Frame k B.V.rank (n ⊕ Fin (2 * σ + 1))} {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} (hF : (ofSplit q).IsBesFrame B s FA F)
    (hcore : (ofSplit q).IsCoreFrame B s FA F₀) {L : Lat B.V} {L₀ : Lat B.V₀} (hL : IsSelfDualC B.V L)
    (hL₀ : IsSelfDualC B.V₀ L₀) (h : IntIn q B.V F L) (h₀ : IntIn q B.V₀ F₀ L₀) : MonoAt B.d L L₀ q.v := by
  obtain ⟨-, b1, b2, b3, b4⟩ := hF
  have hxi : valuation k (ofSplit q).xi = 1 := GlobalTheory.MonoSplit.xi_unit q hU
  refine GlobalTheory.MonoSplit.monoAt_of_splitW q B.d hL hL₀
    (GlobalTheory.MonoSplit.splitW_of_frame q B.d F F₀ _ _ (fun i => ?_) (fun i => ?_)
      (fun r a => ?_) (fun l hl r => ?_) b2 b4 h h₀)
  · rw [map_mul, map_pow, hs, hxi, one_pow, mul_one]
  · rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, Valuation.map_neg, hs, hz, hxi, map_one]
    simp
  · refine (b1 r a).trans ?_
    change ((_ * _ : Matrix _ _ _).map (GlobalTheory.MonoSplit.prE q) * _ : Matrix _ _ _) r a = _
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun t _ => congrArg _ (hcore.1 t a).symm
  · refine (b3 l hl r).trans ?_
    change _ * GlobalTheory.MonoSplit.prE q _ = _
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, mul_left_comm]
    exact congrArg _ (hcore.2 t).symm

theorem line_jac (hU : q.UnitAA) {ρ : ℕ} (J : JacLev D ρ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {s hh : k}
    (hs : valuation k s = 1) (hz : valuation k hh = 1) {F₀ : Frame k J.W₀.rank n} {F : Frame k J.W.rank (n ⊕ Fin c)}
    (hF : (ofSplit q).IsJacFrame J s hh F₀ F) {L : Lat J.W} (hL : IsSelfDualC J.W L) (h : IntIn q J.W F L) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = q.v)) : colMul J.d.jX i a ∈ latV J.W L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  obtain ⟨b, m, hb, hA, hB, hC⟩ := GlobalTheory.JacFramePair.isJacFrame_pairing D k (ofSplit q) ρ J s hh n c F₀ F hF hs hz
    (GlobalTheory.MonoSplit.xi_unit q hU) i
  exact GlobalTheory.SplitLine.line_mem_latV_iff D k q J.W L _ F _ b m hL h hb hA hB hC a ha

theorem line_bes (hU : q.UnitAA) {σ : ℕ} (B : BesLev D σ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {s : k}
    (hs : valuation k s = 1) (hz : valuation k ((ofSplit q).hz B) = 1) {FA : Frame k B.A.rank n}
    {F : Frame k B.V.rank (n ⊕ Fin c)} (hF : (ofSplit q).IsBesFrame B s FA F) {L : Lat B.V} (hL : IsSelfDualC B.V L)
    (h : IntIn q B.V F L) (i : Fin (σ + 1)) (a : AE D) (ha : a ∈ idAt D (· = q.v)) :
    colMul (xLast B.d (vecB B.o B.ζ)) i a ∈ latV B.V L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · obtain ⟨m, hA, hB, hC⟩ := GlobalTheory.BesPair.besz_pairings D k (ofSplit q) σ B s n c FA F hF hs hz
    have e := GlobalTheory.SplitLine.line_mem_latV_iff D k q B.V L _ F _ s m hL h hs hA hB hC a ha
    convert e using 2
    funext r
    simp [GlobalTheory.FinPl.colMul, xLast, HypDec.j0, rat, ratV, Matrix.mulVec, dotProduct, map_sum]
  · obtain ⟨b, m, hb, hA, hB, hC⟩ := GlobalTheory.BesPair.bes_cols D k (ofSplit q) σ B s n c FA F hF hs hz
      (GlobalTheory.MonoSplit.xi_unit q hU) i'
    have e := GlobalTheory.SplitLine.line_mem_latV_iff D k q B.V L _ F _ b m hL h hb hA hB hC a ha
    convert e using 2
    funext r
    simp [GlobalTheory.FinPl.colMul, xLast, HypDec.jX, rat]

theorem psiE_triv_iff (hU : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {s : AE D}
    (hs : s ∈ idAt D (· = q.v)) : (∀ o ∈ intAt D (· = q.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = q.v) := by
  obtain ⟨ψk, hk, hc⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  have hxi : valuation k (ofSplit q).xi = 1 := GlobalTheory.MonoSplit.xi_unit q hU
  have hc' : ∀ x : k, (∀ y : k, valuation k y ≤ valuation k x → ψk y = 1) ↔ x ∈ 𝒪[k] := fun x => by
    rw [hc x, Units.val_one, map_one, Valuation.mem_integer_iff]
  have half : ∀ t : AE D, (∀ o ∈ intAt D (· = q.v), psiE ψ (t * o) = 1) → q.pr t ∈ 𝒪[k] := by
    intro t ht
    by_cases h0 : q.pr t = 0
    · rw [h0]; exact zero_mem _
    refine (hc' _).1 fun y hy => ?_
    have hr : y / q.pr t ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have h1 := ht _ (hU.1 _ (sec_mem_intAt q _ hr)).1
    rw [mul_left_comm, mul_comm t, sec_mul_right, div_mul_cancel₀ _ h0] at h1
    exact Circle.ext ((hk y).trans h1)
  constructor
  · intro h
    refine (GlobalTheory.SplitLine.mem_intAt_iff_pr q hs).2 ⟨half s h, half _ fun o ho => ?_⟩
    rw [← GlobalTheory.LocBesChar.psiE_cA, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    exact h _ (GlobalTheory.JacMono.conj_intAt q ho)
  · intro h o ho
    have hb := GlobalTheory.IwaDecomp.intAt_mul' h ho
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitLine.mem_intAt_iff_pr q hb.1).1 hb
    rw [GlobalTheory.LocBesChar.psiE_supp (ofSplit q) hk ((idem_iff q _).1 hb.1), (hc' 1).2 (one_mem _) _ ?_]
    · rfl
    · rw [map_div₀, hxi, div_one, map_one]
      exact (Valuation.mem_integer_iff _ _).1 (add_mem h1 h2)

theorem primAt_of_lines (hU : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (L : Lat S)
    (h : ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = q.v), colMul d.jX i a ∈ latV S L (· = q.v) ↔ a ∈ intAt D (· = q.v)) :
    PrimAt ψ d L q.v := by
  intro i j _ s hs
  rw [psiE_triv_iff q hU hψ hs]
  constructor
  · intro H
    have hε : q.e + cA D q.e ∈ intAt D (· = q.v) :=
      ⟨sum_mem_idAt q, by
        rw [RingHom.map_add]
        exact add_mem (e_mem_intAt q).2 (GlobalTheory.JacMono.conj_intAt q (e_mem_intAt q)).2⟩
    have h1 := (h i _ (Ideal.mul_mem_right _ _ hs)).1 (H _ ((h j _ hε.1).2 hε))
    rwa [mul_comm, (idem_iff q s).1 hs] at h1
  · intro H a ha
    have h1 : a ∈ idAt D (· = q.v) := by
      have h2 := GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX (latV_supp ha) j
      rwa [GlobalTheory.JacMono.mulVec_colMul, d.pX_jX, GlobalTheory.FinPl.colMul, Matrix.one_apply_eq, mul_one] at h2
    exact (h i _ (Ideal.mul_mem_right _ _ hs)).2 (GlobalTheory.IwaDecomp.intAt_mul' H ((h j a h1).1 ha))

end GlobalTheory.Fam.AdaptSplit

open GlobalTheory.Fam.AdaptSplit in

theorem GlobalTheory.Fam.adaptFB_of_normalFrames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (pk W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) (PP.under (𝓞 D.host.F)) := by
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
