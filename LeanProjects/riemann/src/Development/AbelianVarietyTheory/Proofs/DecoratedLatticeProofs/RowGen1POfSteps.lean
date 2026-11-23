import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenericTermsPointsAgreeGroupSumsCorankOne

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
open Formalism.L2.SG.Pf

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scT_sc_genSet {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) :
    (scT X).sc (scT X).genSet = X.one X.genSet := by
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

theorem rowGen1P_of_steps (hCh : PN.NGChain) (hC : StepClass1) (hN : StepNormals1) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLoc1) (hTB : GlobalTheory.SnPos.StepThmBGP) : RowGen1P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨CB, hCB, a₁, b₁, hTB2⟩ := hTB Cg cb Cw cT CT C0 hcb hcT (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, a₂, b₂, hS2⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  obtain ⟨a₃, b₃, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨a₄, b₄, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨a₅, b₅, hH2⟩ := stepHeightG_of_normOne hO Cg cb Cw cT CT C0
  obtain ⟨a₆, b₆, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨a₇, b₇, hT2⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨a₈, b₈, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨a₉, b₉, hV2⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh meanAmplitudeGeneric_holds C1 C0n (C1 + C0n + 38) CB CSt Cgs CTs
    hCB hCSt hCg hCT le_rfl
  refine ⟨Cn, hCn, max a₀ (max a₁ (max a₂ (max a₃ (max a₄ (max a₅ (max a₆ (max a₇ (max a₈ a₉)))))))),
    max b₀ (max b₁ (max b₂ (max b₃ (max b₄ (max b₅ (max b₆ (max b₇ (max b₈ b₉)))))))),
    fun C' Cl e1 e2 D large₂ X Y u hTies hH0 hSt hT ha => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := e1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := e2
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hH0, hSt, hT⟩
  obtain ⟨hb, X0, ψ, hTie⟩ := hT2 C' Cl p7 q7 D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl p6 q6 D large₂ X Y u u hc hb X0 ψ hTie
  have hBk' : MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) (Irat * kapU D) (Ire * kapU D) :=
    massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨ν, hν⟩ := hE2 C' Cl p8 q8 D large₂ X Y u u hc
  obtain ⟨s, hs1, hs0, hsb, hLe⟩ :=
    hL2 C' Cl p0 q0 D large₂ X Y u hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  have hSum := hTB2 C' Cl p1 q1 D large₂ X Y u hTies hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  generalize bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq = B at hBk' hLe
  have hSz := hS2 C' Cl p2 q2 D large₂ X Y u u hc
  have hrd : 0 < D.host.rdE := by
    obtain ⟨-, -, hrd, -⟩ := hSz
    have hv : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
    rwa [hv] at hrd
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk'
  set ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA * 2 *
      HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ PN.eN D.R.rS *
      nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ)) γ with hng
  obtain ⟨hPt, -, -, hAmp⟩ := GlobalTheory.Core.One.genericTerms_points_agree_groupSums_corankOne D X Y u (sc s ν) ν ng
  have hVan : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u (sc s ν) (ptPN t) = 0 → (Y.tO u u).vec t = 0 := by
    intro t ht h0
    obtain ⟨g, hg⟩ := J2of_sc Y u u s ν (ptPN t)
    rw [hg] at h0
    have hp : (0 : ℝ) < (s g : ℝ) ^ 2 := by have := hs0 g; positivity
    exact hV2 C' Cl p9 q9 D large₂ X Y u hc ν hν t ht ((mul_eq_zero.1 h0).resolve_left hp.ne')
  have hIn : GenInputs (scT (Y.tO u u)) (NOf1 Y u (sc s ν) ν ng) D.R.f C1 C0n (C1 + C0n + 38) CB large₂.sc.b
      (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
      (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f))
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) 2 (Ire * kapU D) := by
    refine ⟨hC D X Y u hT _ _ _, hAmp hVan, hN2 C' Cl p3 q3 D large₂ X Y u hc _ _ _, ?_,
      localInputG_of_le _ _ _ _ _ hLe (fun γ => rfl), ?_, ?_, ?_, ?_⟩
    · exact fun γ hγ => hP2 C' Cl p4 q4 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun γ hγ => measureInputG_sc Y u s ν _ hsb ng γ ((hPt γ).1 hγ)
    · exact fun γ _ => ⟨nPt_nonneg _ hrd _ _ γ, le_rfl⟩
    · exact fun γ hγ => hH2 C' Cl p5 q5 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun S hS => hSum (sc s ν) ng S (fun γ hγ => (hPt γ).1 (hS γ hγ))
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (scT (Y.tO u u)) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOf1 Y u (sc s ν) ν ng) _ B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) 2 (Irat * kapU D) (Ire * kapU D)
  rw [hcard] at key
  have r := key ha hG hNI hFI (ngSizes_of hSz hb0 le_rfl zero_le_two le_rfl) hIn
  rw [hdd] at r
  unfold PB.Terms.RowMain at r
  rw [scT_sc_genSet] at r
  exact r

end GlobalTheory.Core.One
