import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem GlobalTheory.Lev.conj_frameMatrix_submatrix_equiv {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (βF : Matrix (Fin N) Y k) (γF : Matrix Y (Fin N) k) (hβγ : βF * γF = 1) (hγβ : γF * βF = 1) (σ : Fin N ≃ Y)
    (gk : GL Y k) (Pi Bi B P G X Xi : Matrix (Fin N) (Fin N) k) (hG : G = βF * gk.val * γF) (hX : X = Pi * (Bi * G * B) * P)
    (hBP : B * P = βF.submatrix id σ) (hBB : Bi * B = 1) (hPP : Pi * P = 1) (hXi : Xi * X = 1) :
    X = gk.val.submatrix σ σ ∧ Xi = (gk⁻¹).val.submatrix σ σ := by
  subst hG
  have hMM : βF.submatrix id σ * γF.submatrix σ id = 1 := by
    rw [Matrix.submatrix_mul_equiv βF γF id σ id, hβγ, Matrix.submatrix_id_id]
  have hN : Pi * Bi = γF.submatrix σ id := by
    have h1 : (Pi * Bi) * βF.submatrix id σ = 1 := by
      rw [← hBP]
      calc Pi * Bi * (B * P) = Pi * ((Bi * B) * P) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBB, Matrix.one_mul, hPP]
    calc Pi * Bi = (Pi * Bi) * (βF.submatrix id σ * γF.submatrix σ id) := by rw [hMM, Matrix.mul_one]
      _ = γF.submatrix σ id := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hX' : X = gk.val.submatrix σ σ := by
    have e0 : X = (Pi * Bi) * (βF * gk.val * γF) * (B * P) := by rw [hX]; simp only [Matrix.mul_assoc]
    rw [e0, hN, hBP]
    have e1 : γF.submatrix σ id * (βF * gk.val * γF) = (γF * (βF * gk.val * γF)).submatrix σ id := by
      rw [Matrix.submatrix_mul γF _ σ id id Function.bijective_id, Matrix.submatrix_id_id]
    rw [e1, ← Matrix.submatrix_mul _ βF σ id σ Function.bijective_id]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγβ, Matrix.one_mul, Matrix.mul_assoc, hγβ, Matrix.mul_one]
  refine ⟨hX', ?_⟩
  have hR : gk.val.submatrix σ σ * (gk⁻¹).val.submatrix σ σ = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ σ σ σ, Units.mul_inv, Matrix.submatrix_one_equiv]
  calc Xi = Xi * (gk.val.submatrix σ σ * (gk⁻¹).val.submatrix σ σ) := by rw [hR, Matrix.mul_one]
    _ = (gk⁻¹).val.submatrix σ σ := by rw [← Matrix.mul_assoc, ← hX', hXi, Matrix.one_mul]

set_option maxHeartbeats 400000 in
theorem GlobalTheory.Lev.conj_frame_matrix : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → (∀ i j, q.prF he ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val i j) = gk.val (σ i) (σ j)) ∧ ∀ i j, q.prF he (((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val i j) = (gk⁻¹).val (σ i) (σ j) := by
  intro D k _ _ _ _ q PP he V β Y _ _ F σ b hmov g gk hloc
  have hm : (mt V (b⁻¹ * g * b)).map q.pr = (mt V b⁻¹).map q.pr * (mt V g).map q.pr * (mt V b).map q.pr := by
    rw [mt_mul, mt_mul, Matrix.map_mul, Matrix.map_mul]
  have hc : ∀ A : Matrix (Fin V.rank) (Fin V.rank) (AE D), (A.map (toEAf D)).map (q.prF he) = A.map q.pr := by
    intro A; ext i j; simp [Matrix.map_apply, GlobalTheory.FinPl.SplitPt.prF_toEAf]
  have hX : (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val.map (q.prF he) =
      (β⁻¹).val.map (q.prF he) * (mt V (b⁻¹ * g * b)).map q.pr * β.val.map (q.prF he) := by
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, ← hc]
    rfl
  rw [hm] at hX
  obtain ⟨bt, hbt⟩ : ∃ bt : Matrix (Fin V.rank) (Fin V.rank) (AE D), bt.map (toEAf D) = β.val := by
    choose s hs using fun i j => GlobalTheory.ResLoc.toEAf_surj (D := D) (β.val i j)
    exact ⟨Matrix.of s, by ext i j; simp [hs]⟩
  have hM : ((mt V b * bt).map q.pr) = F.β.submatrix id σ := hmov bt hbt
  have hBP : (mt V b).map q.pr * β.val.map (q.prF he) = F.β.submatrix id σ := by
    rw [← hM, ← hbt, hc, Matrix.map_mul]
  have hBB : (mt V b⁻¹).map q.pr * (mt V b).map q.pr = 1 := by
    have h := mt_mul_inv V b⁻¹
    rw [inv_inv] at h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : (β⁻¹).val.map (q.prF he) * β.val.map (q.prF he) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (mt V g).map q.pr = F.β * gk.val * F.γ := hloc.2
  have hXi : ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val.map (q.prF he) *
      (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val.map (q.prF he) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2⟩ := GlobalTheory.Lev.conj_frameMatrix_submatrix_equiv F.β F.γ F.βγ F.γβ σ gk _ _ _ _ _ _ _ hG hX hBP hBB hPP hXi
  exact ⟨fun i j => congrArg (fun M => M i j) h1, fun i j => congrArg (fun M => M i j) h2⟩
