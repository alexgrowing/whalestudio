import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormsOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardOrbitsLeExp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NcardYbSetLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstCoupledKernelFiniteDatumLevelSizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelFiniteDatumBoundedLevelSizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardMatrixStepIndicesLeExpStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelBoundAtEmbeddingAnyLevelPrimeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem factors_leS : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  intro hB hT hV hL hR hP
  obtain ⟨Cd, hdat⟩ := GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size
  obtain ⟨C₁, hC₁, hker⟩ := GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime hB hT hV hL hR hP Cd
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.ChainClassNumbersS.classNumbers_leS
  obtain ⟨Ci, hCi, hidx⟩ := GlobalTheory.T.card_matrixStep_indices_le_exp
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.CouplingCosetsS.ncard_ybSet_le
  refine ⟨C₁ + (Cc + Ci + Cy), by positivity, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B b hY hK hF hE hFD M _ hM ρ
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hU := errUnit_nonneg N (hPr.T_prime u).one_lt.le
  have hm := N.R.two_le_m
  set U := errUnit N (Pr.T u) with hUdef
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1) with hσ
  set Q := KerChain.ofCol W Ch sel mu cst I
    (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE with hQ
  set kb : ℕ → ℝ := fun j => kernelBound_sq N δ (Pr.T u) C₁ j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1 with hkb
  have hlift : ∀ j, kb j + 2 * ((Cc + Ci + Cy) * U) ≤
      liftBound_sq N s W Ch sel mu cst I B cD pl u δ (C₁ + (Cc + Ci + Cy)) M ρ j := fun j =>
    kernelBound_ge N δ _ _ _ j _ _ _ _ _ _
  have hpos : ∀ {n : ℕ} (lam : X.Tau → DomWeight n),
      ((Matrix.of fun i j => pairVr X.emb lam 1 (bVV X.K lam i) (bVV X.K lam j)).map
        (placeUnder s.σ₀ hM.1 ρ).embedding).PosSemidef := fun lam => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb _ lam _).1
  have hsq := fun {n : ℕ} (lam : X.Tau → DomWeight n) => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb n lam σ).2
  have hk := hker CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD
  obtain ⟨hc1, hc2, -⟩ := hcl CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hi1 := hidx CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hfam : ∀ j, ∀ φ : (Q.F j).Forms, 0 ≤ (famIpAt (Q.F j) (Q.hF j) (placeUnder s.σ₀ hM.1 ρ) φ φ).re := by
    intro j φ
    unfold famIpAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b' _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    refine mul_nonneg (by positivity) ?_
    exact (sqAt_nonneg (W.lamTrue u j) σ _).trans_eq (hsq (W.lamTrue u j) _).symm
  have hone : (1 : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (Cd * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h0 h1)
  refine ⟨fun i hi φ => ?_, fun φ => ?_⟩
  · have h1 := GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz X.K Q i (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (i + 1))) (Real.exp (Cc * U)) (Real.exp (Cc * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (fun _ => hpos (W.lamTrue u i))
      (fun _ => hpos (W.lamTrue u (i + 1))) (hc1 i (by omega)) (hc1 (i + 1) (by omega)) (by
        intro al be p p' x
        have h2 := hk i (i + 1) rfl (by omega) _ (frsF sel mu p) _ (frsF sel mu p') ⟨p.deco.2.lat, p.deco.2.uni⟩
          ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ (hdat CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p') M hM ρ x
        have e : (Q.kk i al be).k p p' = matK W Ch sel mu cst I (chTh W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2)) i al be p p' := by
          exact congrArg (fun k : ClsKer _ _ => k.k p p') (dif_pos (show i < N.R.m - 2 by omega))
        rw [e]
        exact (hsq (W.lamTrue u (i + 1)) _).trans_le (h2.trans_eq (congrArg _ (hsq (W.lamTrue u i) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam i φ))
    have b1 : (Fintype.card (Q.F i).β : ℝ) ≤ Real.exp (Ci * U) := hi1 i (by omega)
    have b2 : (Fintype.card (Q.F (i + 1)).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (i + 1) (by omega)
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) * Real.exp (kb (i + 1)) := by gcongr
      _ ≤ _ := by
        simp only [← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (hlift _))
        nlinarith [mul_nonneg hCy hU]
  · have hNle : N.R.N (N.R.m - 2 + 1) ≤ N.Nm := by
      unfold NumDatum.Nm Ranks.N
      have : N.R.m - 2 + 1 ≤ N.R.m := by omega
      gcongr
    have h1 := GlobalTheory.T.coupled_class_sum_cauchy_schwarz X.K Q (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (N.R.m - 2 + 1))) (Real.exp (kb N.R.m))
      (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cy * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
      (fun _ => hpos (W.lamTrue u (N.R.m - 2))) (hpos (W.lamTrue u (N.R.m - 2 + 1))) (hpos (W.lamTrue u N.R.m))
      (hc1 (N.R.m - 2) (by omega)) (hc1 (N.R.m - 2 + 1) (by omega) b) hc2
      (fun p => (hyb CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ hNle).2 _ p.deco.2.lat) (by
        intro al p₀ p Y hYm x
        have h2 := hk (N.R.m - 2) (N.R.m - 2 + 1) rfl (by omega) _ (frsF sel mu p₀) _ (frsF sel mu p)
          ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩ ⟨p.deco.2.lat, p.deco.2.uni⟩ _
          ((GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H al p₀ p Y).mono hone) M hM ρ x
        have e : (Q.cp al).k1 p₀ p Y = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2) (W.lamTrue u (N.R.m - 2 + 1)))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀) p.deco.1.N (frsF sel mu p)
            (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2)) _).symm))) (by
        intro al p d Y hYm x
        have h2 := hk (N.R.m - 2 + 1) N.R.m (by omega) (by omega) _ (frsF sel mu p) _ (frsT sel mu u d)
          ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _
          ((GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hYm).mono hone) M hM ρ x
        have e : (Q.cp al).k2 p Y d = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2 + 1) (W.lamTrue u N.R.m))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) (tilQ sel mu u d).1.N
            (frsT sel mu u d) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u N.R.m) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam _ φ))
    have b1 : (Fintype.card (Q.F Q.n).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (N.R.m - 2) (by omega)
    have e1 : N.R.m - 2 + 1 = N.R.m - 1 := by omega
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) ^ 2 * Real.exp (Cc * U) * Real.exp (Cy * U) ^ 2 *
          Real.exp (kb (N.R.m - 2 + 1)) * Real.exp (kb N.R.m) := by gcongr
      _ ≤ _ := by
        simp only [sq, ← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (add_le_add (hlift _) (hlift _)))
        rw [e1]
        nlinarith [mul_nonneg hCy hU, mul_nonneg hCi hU]

end GlobalTheory.Core.Ht2
