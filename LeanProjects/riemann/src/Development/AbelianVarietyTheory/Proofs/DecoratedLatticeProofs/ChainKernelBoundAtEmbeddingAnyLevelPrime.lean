import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormsOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightsRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormMuInvDetZeroOrOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimesStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2.KernelS

theorem kernel_le_sharp (hB : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound) (hT : FamilyTie) (hV : FamilyVectors) (hL : PeriodLattices)
    (hR : CosetRefinement) (hP : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod) (C : ℕ) : ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl,
      FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m →
      ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu))
        (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' →
      ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ
        (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ),
        CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j)
          (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst)
            (cBof sel mu cst u) L fr L' fr' Ξ)
          (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
            (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1)) := by
  obtain ⟨CK, hCK, hnum⟩ := GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound C
  refine ⟨CK, hCK, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD i j hj hi L fr L' fr' hL1 hL2 Ξ hΞ M _ hM ρ
  subst hj
  have H' := H
  obtain ⟨hHost, hWt, hCh, hAn, hmu, hsh, hI, hSz, hRows⟩ := H'
  obtain ⟨trd, -, -, -, tf, -, tE, -, tcc⟩ := GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr hHost
  obtain ⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩ := hHost
  obtain ⟨-, -, -, hprod, hTodd, hgodd, hS⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨hstep, hnu⟩ := GlobalTheory.Core.Ht2.StepRowsS.weights_rows CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi
  have hcrv : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨tcc, hAn.1⟩
  have hY := GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc
  have hev : ∀ l, Even (N.R.N l) := fun l => by
    unfold Ranks.N
    exact N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)
  have hlt : N.R.N i < N.R.N (i + 1) := by
    unfold Ranks.N
    nlinarith
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ hAn.2.1 (hV D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY) _ _ (hev i) (hev (i + 1))
  have hE0 := hT D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE0
  have hgpos : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have hfpos : 0 < N.R.f := by unfold Ranks.f Ranks.n; positivity
  have hBpos := hI.cst_ok.B_pos
  have hcA : cAof sel mu cst = (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.A) := by unfold cAof; rw [hprod, pow_mul]
  have hcB : cBof sel mu cst u = Pr.T u * (Pr.g 0 * Pr.g 1) * (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1) := by
    unfold cBof
    have h1 : N.R.f * cst.B = (N.R.f * cst.B - 1) + 1 := by
      have := Nat.mul_pos hfpos hBpos
      omega
    rw [hprod, ← pow_mul]
    conv_lhs => rw [h1]
    ring
  have hodd : Odd (cAof sel mu cst * cBof sel mu cst u) := by
    have h1 : Odd (Pr.g 0 * Pr.g 1) := (hgodd 0).mul (hgodd 1)
    rw [hcA, hcB]
    exact h1.pow.mul ((hTodd.mul h1).mul h1.pow)
  have hInd := hR X (ambOf s B χ cD) _ _ (Sall sel mu u) _ hX.ok (fun P hP => (hS P hP).2) hodd
    (hL D X s _ dl B χ cD hX.ok hs hadm hpsi tcc hAn.1 hAn.2.1 hAn.2.2 hY _ _ (Sall sel mu u) (hev i) (hev (i + 1))
      (fun P hP => (hS P hP).1) (GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B))
  have hJ := hFD i hi
  have hc0 : ∀ τ, cD τ ≠ 0 := (GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc hAn.1) hAn.2.2).1
  have hsc : ‖((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1))
      (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr *
        (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L' fr')⁻¹)‖ ≤ 1 := by
    rw [map_mul, map_inv₀, norm_mul, norm_inv]
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L fr
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h1 | h1 <;>
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L' fr'
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h2 | h2 <;> rw [h1, h2] <;> norm_num
  unfold stepC
  rw [hcB] at hInd hJ ⊢
  have key := block hB D X s _ dl B χ cD _ hX.ok hs hcrv B.t0 hc0 _ _ hlt ((hev i).mul_right _) hE0
    (W.lamTrue u i) (W.nuW u (i + 1)) (W.lamTrue u (i + 1)) hstep (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst)
    (Pr.T u * (Pr.g 0 * Pr.g 1)) ((Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1)) (by rw [hcA]; positivity)
    (Nat.mul_pos (hPr.T_prime u).pos hgpos) (by positivity) hInd hJ sel (mUof Ch mu i) (muAt Ch sel mu cst i) L fr L' fr' hL1 hL2
    Ξ _ hΞ M hM.1 ρ hM.2.1 hM.2.2.1 (hM.2.2.2 i hi) hsc
  have hn := hnum N δ (Pr.T u) i X.Tau pl (W.nuW u (i + 1)) (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N i) (N.R.N (i + 1))) hi (hPr.T_prime u).two_le (fun τ => (hstep τ).1) hnu
  intro x
  refine (key x).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine le_trans (le_of_eq ?_) hn
    simp only [supConst, tf, tE, ← trd, hg, Equiv.apply_symm_apply]
  · exact sqAt_nonneg _ _ _

end GlobalTheory.Core.Ht2.KernelS
