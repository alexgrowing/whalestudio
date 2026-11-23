import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchInput
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FunctionalsSeparateFromRealInput
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.Occ
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.SeedBaseCases.SeedBOf
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.SchurFiniteDimensionality.IsFdOfSchurK
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.HolomorphicMoments.MomentHigherEstimateHolds
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigOfLow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMatrixCoefficientIntertwiner

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace

namespace UpperTheory.Lit.Branch

variable {n : ℕ}

def sumNum (e : Option (Fin n) ≃ Fin (n + 1)) : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.optionEquivSumPUnit (Fin n)).symm.trans e

theorem emb_sumNum (e : Option (Fin n) ≃ Fin (n + 1)) (h : Mat n) : GlobalTheory.CompanionTheory.PairingAnalysis.emb (sumNum e) h = embH e h := by
  ext a b
  simp only [GlobalTheory.CompanionTheory.PairingAnalysis.emb, embH, sumNum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> simp [Equiv.optionEquivSumPUnit]

variable {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
  {mu : Fin n → ℝ} {B : ℝ}

theorem fits_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.Fits ε ε' (sumNum e) := by
  refine ⟨?_, fun a => ?_⟩
  · simpa [GlobalTheory.CompanionTheory.PairingAnalysis.zi, sumNum, Equiv.optionEquivSumPUnit] using hP.signs.1
  · simpa [sumNum, Equiv.optionEquivSumPUnit] using hP.signs.2 a

theorem par_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.Par ε lam ε' mu B := by
  have hs := hP.signs
  refine ⟨by linarith [hP.three_le], ?_, ?_, hP.hlam, hP.hmu, hP.bound.1, hP.bound.2, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hP.neg
    exact ⟨e (some i), by rw [hs.2 i, hi]⟩
  · calc #{a | ε a = false} ≤ #{i | ε' i = false} := by
          refine Finset.card_le_card_of_surjOn (fun i => e (some i)) ?_
          intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
          cases hsa : e.symm a with
          | none =>
            have : a = e none := by rw [← hsa, Equiv.apply_symm_apply]
            rw [this, hs.1] at ha
            exact absurd ha (by decide)
          | some i =>
            have : a = e (some i) := by rw [← hsa, Equiv.apply_symm_apply]
            refine ⟨i, ?_, this.symm⟩
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
            rw [← hs.2 i, ← this, ha]
      _ ≤ #{i | ε' i = true} := hP.pos
      _ ≤ #{a | ε a = true} := by
          refine Finset.card_le_card_of_injOn (fun i => e (some i)) ?_ ?_
          · intro i hi
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hs.2 i, hi]
          · intro i _ j _ hij
            simpa using hij
  · intro a b hab
    have h1 := hP.gap a b hab
    have h2 : (0 : ℝ) ≤ (↑n + 1) ^ 3 := by positivity
    linarith
  · intro a b hab
    have h1 := hP.gap' a b hab
    have h2 : (0 : ℝ) ≤ (↑n + 1) ^ 3 := by positivity
    linarith

theorem heWord_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.HeWord ε lam ε' mu := by
  intro x y hxy hz
  have h := hP.word x y hxy hz
  simp only [ne_eq] at h
  unfold Xor'
  tauto

private theorem exists_uj_umat_eq_of_mem_UJset {m : ℕ} {ε : Fin m → Bool} {h : Mat m} (hh : h ∈ UJset ε) :
    ∃ g : UJ ε, umat g = h := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  have h1 : (Jm ε * hᴴ * Jm ε) * h = 1 := by
    calc (Jm ε * hᴴ * Jm ε) * h = Jm ε * (hᴴ * Jm ε * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh', hJ]
  exact ⟨⟨⟨h, Jm ε * hᴴ * Jm ε, mul_eq_one_comm.mp h1, h1⟩, hh⟩, rfl⟩

private theorem embH_mem_UJset_of_signs {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool}
    {ε' : Fin n → Bool} (hs : Signs e ε ε') {h : Mat n} (hh : h ∈ UJset ε') : embH e h ∈ UJset ε := by
  have hJ : Jm ε = embH e (Jm ε') := by
    ext a b
    have ha := e.apply_symm_apply a
    have hb := e.apply_symm_apply b
    simp only [embH, Formalism.REAL.Jm, Matrix.diagonal_apply]
    rcases hA : e.symm a with _ | i <;> rcases hB : e.symm b with _ | j <;> rw [hA] at ha <;>
      rw [hB] at hb <;> subst ha <;> subst hb <;> simp [hs.1, hs.2]
  have hC : (embH e h)ᴴ = embH e hᴴ := by
    ext a b
    simp only [embH, Matrix.conjTranspose_apply]
    rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> simp
  rw [GlobalTheory.SepReal.ProjSm.mem_iff] at hh ⊢
  rw [hC, hJ, ← embH_mul, ← embH_mul, hh]

private theorem isU_comp_umat_of_isURepOn {m : ℕ} {ε : Fin m → Bool} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {ρ : Mat m → K →L[ℂ] K} (hρ : IsURepOn (UJset ε) ρ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε => ρ (umat g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ρ 1 = 1
    exact hρ.1.1
  · intro a b
    have h := hρ.1.2 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε a) _ (GlobalTheory.SepReal.RealAsm.umat_mem ε b)
    show ρ (umat a * umat b) = _
    rw [h]
    rfl
  · intro g x
    exact hρ.2.1 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε g) x
  · intro x
    exact (hρ.2.2 x).comp_continuous (GlobalTheory.SepReal.RealAsm.continuous_umat ε)
      (GlobalTheory.SepReal.RealAsm.umat_mem ε)

private theorem isURepOn_embH_of_signs {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool}
    {ε' : Fin n → Bool} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (hs : Signs e ε ε') {π : Mat (n + 1) → K →L[ℂ] K} (hπ : IsURepOn (UJset ε) π) :
    IsURepOn (UJset ε') (fun h => π (embH e h)) := by
  have hc : Continuous (embH e) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [embH]
    rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> first | fun_prop | exact continuous_const
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hπ.2.1 _ (embH_mem_UJset_of_signs hs hg) v,
    fun v => (hπ.2.2 v).comp hc.continuousOn (fun h hh => embH_mem_UJset_of_signs hs hh)⟩
  · simp only [embH_one]
    exact hπ.1.1
  · simp only [embH_mul]
    exact hπ.1.2 _ (embH_mem_UJset_of_signs hs ha) _ (embH_mem_UJset_of_signs hs hb)

theorem projLarge_of (hS : PositivityTheory.RgHe.A.SchurEigenProjectionExists) (hB : PositivityTheory.RgHe.A.BigProjP) : ProjLarge := by
  unfold ProjLarge ForPair
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ v₀ hv₀
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS mu σ hσ
  have hK : PositivityTheory.RgHe.SchurK ε' σ (muG ε') d⁻¹ := by
    refine ⟨inv_pos.2 hd.1, fun v w v' w' => ⟨(hd.2 v w v' w').1, ?_⟩⟩
    refine (hd.2 v w v' w').2.trans ?_
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  obtain ⟨S, hKS⟩ := hσ.2.2.2.2.2.1
  obtain ⟨x, hxS, hx0, -⟩ := hKS.2.2.2.1
  have hxL : x ∈ lowKSub ε' mu σ := by
    unfold Formalism.MainNotions.S.lowKSub
    exact Submodule.mem_sSup_of_mem hKS hxS
  set w : H' := ((‖x‖ : ℂ)⁻¹) • x with hwdef
  have hwL : w ∈ lowKSub ε' mu σ := Submodule.smul_mem _ _ hxL
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  have hfit := fits_of hP
  have hpar := par_of hP
  obtain ⟨hint, i, η, hiso, hieq, hη, hηi, hηa⟩ := hS n ε lam ε' mu B (sumNum e) H H' π σ (muG ε')
    inferInstance hfit hpar hπ hσ (heWord_of hP) d⁻¹ hK w hwL hw1
  obtain ⟨g₀, hg₀s, hg₀⟩ := hB n ε lam ε' mu B (sumNum e) H H' π σ (muG ε') inferInstance hfit hpar
    hπ hσ d⁻¹ hK w hwL hw1 hint i η hiso hieq hη hηi hηa v₀ hv₀.2 hv₀.1
  have hB1 := GlobalTheory.SepReal.RealAsm.one_le_B hP
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hX : 0 ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  refine ⟨i, ContinuousLinearMap.adjoint i,
    ⟨?_, hiso, fun v y => (ContinuousLinearMap.adjoint_inner_right i y v).symm⟩,
    umat g₀, GlobalTheory.SepReal.RealAsm.umat_mem ε g₀, ?_, ?_⟩
  · intro h hh y
    obtain ⟨g, rfl⟩ := exists_uj_umat_eq_of_mem_UJset hh
    have h2 := hieq g y
    rwa [emb_sumNum] at h2
  · rw [show (10 : ℝ) * ((n : ℝ) + 1) = ((10 * (n + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    show Real.sqrt (Formalism.REAL.hs (umat g₀)) ≤ _
    rw [← Real.sqrt_sq (pow_nonneg hX (10 * (n + 1)))]
    apply Real.sqrt_le_sqrt
    rw [← pow_mul]
    convert hg₀s using 2 <;> ring
  · have hL : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by nlinarith)
    have h1 : 1 ≤ big 100 n B *
        Real.exp (-(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * ((n : ℝ) + 1) * B))) := by
      unfold big
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h3 : 100 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B) +
          -(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * ((n : ℝ) + 1) * B)) =
          100 * (((n : ℝ) + 1) ^ 3 * (n : ℝ) * Real.log (8 * ((n : ℝ) + 1) * B)) := by ring
      rw [h3]
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity) hn) hL)
    exact h1.trans (mul_le_mul_of_nonneg_left hg₀ (GlobalTheory.SepReal.RealAsm.big_pos _ _ _).le)

theorem eigMap_of (hE : PositivityTheory.RgHe.A.EigA) (hT : PositivityTheory.RgHe.A.TMap) : EigMap := by
  unfold EigMap ForPair
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ d hd w₀ hw₀ hint j P hjP v hv hPv
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  have hU' : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε' => σ (umat g)) := isU_comp_umat_of_isURepOn hσ.2.2.1
  have hU : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε' => π (embH e (umat g))) :=
    isU_comp_umat_of_isURepOn (ρ := fun h => π (embH e h)) (isURepOn_embH_of_signs hP.signs hπ.2.2.1)
  have hFd : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsFd (muG ε') (fun g : UJ ε' => σ (umat g)) d := hd
  have hiso : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsIsoMap (fun g : UJ ε' => σ (umat g)) (fun g => π (embH e (umat g))) j :=
    ⟨fun g x => hjP.1 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε' g) x, hjP.2.1⟩
  have hadj : ContinuousLinearMap.adjoint j = P := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← inner_conj_symm, ← hjP.2.2 x y]
    exact inner_conj_symm _ _
  obtain ⟨w, c, hw0, hc, hb⟩ := hE (muG ε') (fun g : UJ ε' => σ (umat g))
    (fun g => π (embH e (umat g))) d hU' hU hFd w₀ hw₀ hint j hiso v hv
  rw [hadj] at hc
  have hcpos : 0 < c :=
    lt_of_lt_of_le (div_pos (pow_pos (norm_pos_iff.2 hPv) 2) (by linarith [hd.1])) hc
  obtain ⟨T, hT, hTv⟩ := hT (muG ε') (fun g : UJ ε' => σ (umat g)) (fun g => π (embH e (umat g))) d
    hU' hU hFd v hv w c hcpos.ne' (fun b => (hb b).2)
  refine ⟨w, c, T, hw0, hc, fun b => (hb b).2, ?_, hTv⟩
  intro h hh x
  obtain ⟨g, rfl⟩ := exists_uj_umat_eq_of_mem_UJset hh
  exact hT g x

end UpperTheory.Lit.Branch

end

namespace UpperTheory.Lit

theorem realInputE_holds : Branch.RealInputE :=
  Branch.realInputE
    (Branch.projLarge_of (PositivityTheory.RgHe.A.Pf.seedB_of PositivityTheory.RgHe.LowestKTypeModel.seed PositivityTheory.RgHe.occ)
      (PositivityTheory.RgHe.A.Pf.bigProjP PositivityTheory.RgHe.A.Pf.momentP CompanionTheory.Lime.T3.analytic_estimates))
    (Branch.eigMap_of GlobalTheory.CompanionTheory.RgHeA.eigA GlobalTheory.CompanionTheory.RgHeA.TMapPf.tMap)

theorem functionalsSeparate_free (P : GlobalTheory.FunPr.Hypotheses₂) (hH : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent) : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  functionalsSeparate_of_input P hH hSW realInputE_holds

end UpperTheory.Lit
