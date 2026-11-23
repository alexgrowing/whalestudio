import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

noncomputable section

namespace GlobalTheory.LvT.Built.TopEq

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
  {u : Pr.Word} {A : Amb X}

theorem kerOf_xiTop (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) {T : ChTh W sel mu u m2} (hT : ChTh.Ok (Ch := Ch) cst T)
    (al : L.β (m2 + 1)) (c : TopStep.TopDepth R cst.M) (g : FrmG (L.levG (m2 + 1) al) (L.levQ (m2 + 1) al))
    (g' : FrmG (TopStep.topLevG Ch (rPsymF (R := R) Ch)) (TopStep.topLevQ R sel mu c.pos)) (p : ChPt (R := R) sel mu u (m2 + 1))
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) (p' : ChPt (R := R) sel mu u R.m) :
    kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (g • p).deco.1.N (frsF sel mu (g • p)) (g' • p').deco.1.N
        (frsF sel mu (g' • p')) (TopStep.XiTop Ch sel mu cst m2 (g • p) ((fun v => g.1.1 v) '' Y) (g' • p')) =
      frmRho (colValF W sel mu u R.m) _ _ g' ∘ₗ
        kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p')
          (TopStep.XiTop Ch sel mu cst m2 p Y p') ∘ₗ frmRho (colValF W sel mu u (m2 + 1)) _ _ g⁻¹ := by
  have hY' : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N := (ybSet_gmap sel mu cst _ g.1.1 Y).2 hY
  have hd := (TopStep.tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  obtain ⟨κ, a, hκ, ha, ea⟩ := TopLaw.exists_pass hd g p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := TopLaw.exists_pass hd g' p'
  have key := GlobalTheory.kerOf_gmap_frames T.top (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _
    hT.top g.1 g'.1 p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (TopStep.XiTop Ch sel mu cst m2 p Y p')
    (TopStep.XiTop Ch sel mu cst m2 (g • p) ((fun v => g.1.1 v) '' Y) (g' • p')) (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K)
    ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩
    (GlobalTheory.TopXiInv.xiTop_invariant Ch sel mu cst m2 u hPr hL.hm hL.cst_ok hL.depthQ p Y p' hY) fun x =>
      TopLaw.xiTop_law c hX hPr hsel hL (Or.inr ⟨hs, rfl⟩) hY hY' hκ hκ' ha ha' x (TopLaw.phiT_act _ _ _ _ _ _ _)
  rw [funext hκ, funext hκ']
  refine key.trans ?_
  have ei : (∏ P, a P)⁻¹ = (L.levG (m2 + 1) al).chr g.2.1⁻¹ * (L.levQ (m2 + 1) al).chr g.2.2⁻¹ := by
    rw [ea, mul_inv, map_inv, map_inv]
  exact (congrArg (fun z : X.Kˣ => (z : X.K) • _) (congrArg₂ (· * ·) ea' ei)).trans (TopLaw.smul_comp_smul _ _ _ _ _)

theorem ker_xiOver (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) (hT : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    {j : ℕ} (h : j = R.m) (al : L.β (m2 + 1)) {Λ : LevFam X.E X.K (R.N j) Pr.vGs}
    {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (hΛ : Λ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levG j) (hΘ : Θ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levQ j)
    (g : FrmG (L.levG (m2 + 1) al) (L.levQ (m2 + 1) al)) (g' : FrmG Λ Θ) (p : ChPt (R := R) sel mu u (m2 + 1))
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) (p' : ChPt (R := R) sel mu u j) :
    GlobalTheory.KerT.ker W Ch sel mu cst A u (m2 + 1) j (g • p).deco.1.N (frsF sel mu (g • p)) (g' • p').deco.1.N (frsF sel mu (g' • p'))
                 (xiOver Ch sel mu cst m2 h (g • p) ((fun v => g.1.1 v) '' Y) (g' • p')) =
      frmRho (colValF W sel mu u j) _ _ g' ∘ₗ
        GlobalTheory.KerT.ker W Ch sel mu cst A u (m2 + 1) j p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p')
          (xiOver Ch sel mu cst m2 h p Y p') ∘ₗ frmRho (colValF W sel mu u (m2 + 1)) _ _ g⁻¹ := by
  subst h
  obtain rfl := hΛ.trans (topLev_levG_m_eq Ch sel mu cst _)
  obtain rfl := hΘ.trans (topLev_levQ_m_eq Ch sel mu cst _)
  have e3 : (chTh W Ch sel mu cst A u m2).top = stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u R.m) :=
    stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u (m2 + 1) (by have := hL.hm; omega) (W.lamTrue u R.m)
  have key := kerOf_xiTop hX hPr hsel hS hL hs hT al default g g' p hY p'
  rw [e3] at key
  exact key

theorem kAt_top_equiv (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X) (hX : X.Ok) (hPr : Pr.Ok) (_hCh : Ch.Ok) (hsel : IsSel X sel)
    (hTS : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S) (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true)
    (hT : ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2)) (hi : i + 1 = R.m) b b'
    (g : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).G b)
    (g' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).G b')
    (d : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).D b)
    (d' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).D b') :
    kAt W Ch sel mu cst L A u i b b'
        (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).actD b; g • d)
        (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).actD b'; g' • d') =
      (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).rho X.emb (W.lamTrue u (i + 1)) b' g' ∘ₗ
        kAt W Ch sel mu cst L A u i b b' d d' ∘ₗ
          (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).rho X.emb (W.lamTrue u i) b g⁻¹ := by
  obtain rfl : i = m2 + 1 := by have := hL.hm; omega
  have hY := PtAt.mem_ybSet d hi
  unfold kAt
  rw [xiAt_last Ch sel mu cst L hi, xiAt_last Ch sel mu cst L hi]
  obtain ⟨_ | al, hb⟩ := b
  · exact absurd (hb.2 (by omega)) (by simp)
  exact ker_xiOver hX hPr hsel ⟨hTS, hg⟩ hL hs hT hi al (levGAt_of_le sel mu L _ hi.ge b') (levQAt_of_le sel mu L _ hi.ge b')
    g g' d.1.1 hY d'.1.1

end GlobalTheory.LvT.Built.TopEq
