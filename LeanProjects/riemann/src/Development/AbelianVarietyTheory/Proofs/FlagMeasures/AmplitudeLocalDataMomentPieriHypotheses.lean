import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctionalStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetupGap

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  have hnum := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (h / 2) := hnum.1.2.2.2.2
  have hDG : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 →
      (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := by
    intro ν hν
    obtain ⟨hp, hds⟩ := hF ν hν
    exact ⟨hp, hds, h / 2, (hnum.2 ν hν).2.2.1, hok⟩
  have hex : ∀ ν : Fin (2 * r + k + 1) → ℤ,
      ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hν : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r (PI.BesselPeriodGGP.eps48 k r)
        (fun a => lam a + (ν a : ℝ)) (h / 2) (R ν) Wp z π u μW μN μG νq (hDG ν hν)
        (hnum.2 ν hν).2.2.1 hok hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hν⟩
  choose l hl using hex
  refine ⟨l, ?_⟩
  unfold Setup SideFam
  refine ⟨hN, hF, hS, fun ν hν => ⟨hl ν hν, ?_, ?_⟩⟩
  · exact mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hν).1
  · intro w hw
    exact hd _ (R ν) (hDG ν hν) w hw

theorem exists_setup_both : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hzt R hR
  have := FiniteDimensional.complete ℂ W.Wp
  have := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  obtain ⟨hNum, -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU
  obtain ⟨hNum', -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := hZ.1
  obtain ⟨hπ, hπ', hzb, hzb', hT, hT', hμG, hμW, -, hμW', -, hμN, hνS, hνS'⟩ := hW
  have hTw : 0 < Tz D.R.k D.R.rS W.z := by
    rw [hT]
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.1 : 0 < (D.mem w).A.T)
  have hTw' : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [hT']
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.2.1 : 0 < (D.mem w').A.T)
  have hNH : PI.BesselPeriodGGP.IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμN]
    refine GlobalTheory.haarLie_isHaarOn_Nset _ _ _ ?_ ENNReal.ofReal_lt_top
    unfold kapN
    exact ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ)
  have hS1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨hzb, hTw, ⟨_, hπ⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ hzb hTw hπ hU, hμW, hNH, hμG, hνS⟩
  have hS2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨hzb', hTw', ⟨_, hπ'⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ hzb' hTw' hπ' hU', hμW', hNH, hμG,
      hνS'⟩
  have hM1 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wp W.z W.π U
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW W.μN W.μG W.νS t ht hNt
    (hzt W.z hzb).1 (hzt W.z hzb).2 hS1).1
  have hM2 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wq W.z' W.π' U'
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW' W.μN W.μG W.νS' t ht hNt
    (hzt W.z' hzb').1 (hzt W.z' hzb').2 hS2).1
  obtain ⟨c, hc, hsch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 D.R.k D.R.rS
    (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) W.μG hμG
  obtain ⟨l, hl⟩ := exists_setup hH hNum hR hM1 hc (fun mu Q h => (hsch mu Q h).1)
  obtain ⟨l', hl'⟩ := exists_setup hH hNum' hR hM2 hc (fun mu Q h => (hsch mu Q h).1)
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetupGap
