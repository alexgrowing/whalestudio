import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShortRuleOfRaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZNonnegAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZSqNonnegOfSqDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogShortThetaSeriesDenominatorBoundLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealIntegralTrivAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevelStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovInt

set_option maxHeartbeats 1000000 in

theorem integral_smul_thLa : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.log_shortThetaSeriesDenominatorBound_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab
  obtain ⟨hpos, hlog⟩ := hC D T j Y e o Lb a n hH
  refine ⟨intZ D (T.Q.Dw j) Y.d.l₂ n a ^ 2, pow_pos hpos 2, ?_, ?_⟩
  · rw [Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith
  · intro x0 La N P hU hTb hTM hN hP y hval s hs y₁ hy₁
    choose x0' hx0' using fun b => Submodule.Quotient.mk_surjective _ (x0 b)
    have hx : x0 = fun b => (Submodule.Quotient.mk (x0' b) : LevQc (T.Q.Dw j) Y.d.l₂) := funext fun b => (hx0' b).symm
    subst hx
    rw [GlobalTheory.RawSpan.phiHat_indPhi_mk] at hval
    have hsec : (y : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
      have := GlobalTheory.AllWt.cuspW_le_secZ (U := Y.U) (wtZ a n) y.2
      rwa [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat] at this
    have hR := GlobalTheory.RawSpan.isShortRule_of_raw nab hnab hU hTM hN hP x0' _ hsec hval
    obtain ⟨-, hp1, -, hfr, -, -, -, -, -, -, -, -, -, hn8, -, -⟩ := hH
    have hM0 : Y.d.l₂.M ≠ 0 := by
      intro h0
      have hc := GlobalTheory.PlaceInt.card_fun_levQ _ _ (T.Q.Dw j) Y.d.l₂ n
      have hex : Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
      rw [h0, zero_pow hex] at hc
      have : intZ D (T.Q.Dw j) Y.d.l₂ n a = 0 := by unfold intZ; rw [hc]; simp
      omega
    have hβ : betaH (Dw := T.Q.Dw j) Y.d.c₂ La ≠ 0 := GlobalTheory.RawSpan.betaH_ne_zero La
    have hg := Submodule.smul_mem _ (betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ hsec
    have hlevI := GlobalTheory.RawSpan.idCover_isLev nab n
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = intZ D (T.Q.Dw j) Y.d.l₂ n a := ⟨_, rfl⟩
    rw [← hZ]
    refine GlobalTheory.AllWt.mem_supLat.2 ?_
    intro la v hv
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul Y.d.c₂.F, hy₁]
    have hV := isVal_valSet la v hv
    have hZ0 : Z ≠ 0 := by rw [hZ]; exact hpos.ne'
    by_cases hb : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ∣ Y.d.l₂.M
    · obtain ⟨ℓ₀, hℓ₀, hm₀, hd₀⟩ := hb
      have hsI := GlobalTheory.T.intersectedLattice_detIdeal_integral_trivAt_prime D.host.E _ (T.Q.Dw j) _ Y.d.c₂ n La ℓ₀ hℓ₀ (GlobalTheory.IntCuspLat.trivAt_of_dvd hTM hd₀) la hm₀ s hs
      rw [smul_comm]
      refine GlobalTheory.IdemInt.nonneg_smul hV hsI ?_
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          ((Z : Y.d.c₂.F)) • ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      have hyZ2 : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          (betaH (Dw := T.Q.Dw j) Y.d.c₂ La * ((Z ^ 2 : ℕ) : Y.d.c₂.F)) •
          ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [smul_smul]
        congr 1
        field_simp
      by_cases h : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ^ 2 ∣ Y.d.l₂.M
      · obtain ⟨ℓ, hℓ, hm, hsq⟩ := h
        have htr : La.TrivAt ℓ := GlobalTheory.IntCuspLat.trivAt_of_dvd hTM
          (dvd_trans (dvd_pow_self ℓ two_ne_zero) hsq)
        rw [hyZ2, hZ]
        exact GlobalTheory.CovInt.SqLev.smul_intZ_sq_nonneg_of_sq_dvd D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la ℓ hℓ hm hsq htr v hv
      · push_neg at h
        rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
        have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
        refine add_nonneg (by exact_mod_cast h1) ?_
        rw [hZ]
        exact GlobalTheory.CovInt.smul_intZ_nonneg_away D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la h v hv
    · push_neg at hb
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (s • (y : Rul Y.d.Xo₂ Y.d.c₂)) =
          ((Z : Y.d.c₂.F)) • ((s * betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
      have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
      refine add_nonneg (by exact_mod_cast h1) ?_
      rw [hZ]
      exact GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
        (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
        la hb s hs v hv

end GlobalTheory.CovInt
