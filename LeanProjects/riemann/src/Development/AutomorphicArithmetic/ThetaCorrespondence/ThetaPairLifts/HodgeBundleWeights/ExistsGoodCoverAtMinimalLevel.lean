import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovGmin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem minimal_level_cover_is_good : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  intro _
  obtain ⟨CA, hCA0, hA⟩ := GlobalTheory.CovGmin.span_thFam
  obtain ⟨CB, hCB0, hB⟩ := GlobalTheory.RawThetaSup.homN_smul_raw_le
  obtain ⟨CC, hCC0, hC⟩ := GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral
  refine ⟨CA + CB + CC + 391, by linarith only [hCA0, hCB0, hCC0], ?_⟩
  intro D T hJ j hp hq hf hj Y e o hG Lb hL hM hE hfr ho a n hDom hev hn hpos hsz
  have hH : GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n :=
    ⟨hJ, hp, hq, hf, hj, hG, hL, hM, hE, hfr, ho, hDom, hev, hn, hpos, hsz⟩
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂
  obtain ⟨Na, hNa, hlog, hint⟩ := hC D T j Y e o Lb a n hH nab hnab
  have hspan := hA D T j Y e o Lb a n hH nab hnab
  have hB' := hB D T j Y e o Lb a n hH nab hnab
  clear hA hB hC
  have hκ : 1 ≤ sizeK (T.Q.Dw j) a n := by
    have h1 := GlobalTheory.RawThetaSup.two_mul_card_psi T.Q.H
    have h2 : 1 ≤ n / 2 * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q)) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    have h3 : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) := by
      exact_mod_cast h2
    rw [GlobalTheory.RawThetaSup.sizeK_eq]
    exact h3.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hNaE : (Na : ℝ) ≤ Real.exp (CC * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.2 hNa)).1 hlog
  have hFE : Real.exp (fieldSz Y.d.c₂.F) ≤ Real.exp (391 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    Real.exp_le_exp.2 ((hG.size.trans ho).trans
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) (sq_nonneg _)) hκ))
  refine ⟨{w | w ∈ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ ∀ σ, Y.nrm (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n)}, fun _ h => h.1, ?_, fun _ h => h.2⟩
  refine span_eq_top_of_multiples (Y.V (wtZ a n)) _ _ hspan Na hNa ?_
  rintro y ⟨x0, La, N, P, -, hU, hTb, hTM, hO, hP, hρ, hy⟩
  obtain ⟨s, hs0, hs1, hs2⟩ := GlobalTheory.T.exists_small_scalar_reflexIdeal_selfDualLattice D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.c₂ n La hU
  refine ⟨s, hs0, fun y₁ hy₁ hc => ⟨hint x0 La N P hU hTb hTM hO hP y hy s hs1 y₁ hy₁, fun σ => ?_⟩⟩
  have hsup := hB' _ x0 La N P hU hTM hO hP hρ y hy s _ (Real.exp_pos _).le
    (fun σ => (hs2 σ).trans (pow_le_pow_left₀ (Real.exp_pos _).le hFE 2)) σ
  have hfin := nrm_le_of_eq_smul D T.toCore j Y (wtZ a n) σ _ _ Na _ _
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le) hNaE hc hsup
  rw [exp_consts] at hfin
  exact hfin
end GlobalTheory.CovGmin
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_cover_at_minimal_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  first | exact @_root_.GlobalTheory.CovGmin.minimal_level_cover_is_good | exact _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good | (intros; apply _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good <;> assumption)
end
