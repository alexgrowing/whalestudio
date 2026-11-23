import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLocCharUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

theorem norm_map_of_finOrder {K : Type} [Field K] (σ : K →+* ℂ) {ζ : Kˣ} (h : IsOfFinOrder ζ) : ‖σ (ζ : K)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one, norm_one]

theorem norm_muInvDet {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    (ht : Ch.Tied G.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j < R.m) {n : ℕ}
    (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) :
    ‖G.σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr)‖ = 1 := by
  have hU : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ), ‖(((G.mu0 ⟨j, hj⟩).locK P x : ℂˣ) : ℂ)‖ = 1 := fun P x =>
    (ht.mu0 ⟨j, hj⟩).unitary _
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      ‖G.σ₀ (Ch.muVal ⟨j, hj⟩ P : X.K)‖ = 1 := fun P hP => by
    rw [ht.muVal _ P hP]
    exact hU P (Formalism.L2.Host.unif P)
  have hfin := GlobalTheory.CharVal.finOrder_tup mu
  have h1 : ∀ P : rowSG Pr sel mu, ‖G.σ₀ (cst.muq (j + 1) P)‖ = 1 := by
    intro P
    have hq : ‖G.σ₀ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
      norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
    obtain ⟨hd, hn⟩ := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [hL.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl, norm_mul, norm_inv, hU, Units.val_inv_eq_inv_val, map_inv₀,
        norm_inv, hq]
      simp
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hL.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        norm_mul, norm_inv, norm_inv, hq, hval _ hg]
      simp
  have h2 : ‖G.σ₀ (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N)‖ = 1 := by
    unfold muOff
    refine finprod_induction (fun x => ‖G.σ₀ x‖ = 1) (by simp)
      (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · simp
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dif_pos hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul, norm_inv, norm_inv,
        hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX hPr hsel hv), norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
      simp
  rw [muInvDet, map_mul, norm_mul, h2, one_mul, map_prod, norm_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (j + 1) P) _
    ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2) (Units.ne_zero _)
  rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, h1, norm_map_of_finOrder _ hζ, one_zpow, one_mul]

def chiLat {D : D7} {X : Fields} (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) : ℂ :=
  χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N))

theorem norm_chiLat {D : D7} {X : Fields} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ} (hX : X.Ok) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) : ‖chiLat s χ n N‖ = 1 := by
  obtain ⟨-, t2, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  rw [chiLat, t6]
  generalize GlobalTheory.CharVal.detLat N = I at h1 h2
  obtain ⟨c1, h, y, hh, hy, hyI⟩ := GlobalTheory.NormOneIdeal.pow_eq_span_norm_one X.E I J h1 h2
  have hn : ∀ n : ℕ, TaylorLogMetric.N1 D (GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (I ^ n)) := fun n =>
    GlobalTheory.CharVal.normOne_idTo hs (c1 n) (by rw [← mul_pow, h2, one_pow])
  have hp : ∀ n : ℕ, χ (GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (I ^ n)) = χ (GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s I) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Submodule.one_eq_span, GlobalTheory.CharVal.chi_span hs hχ (by simp)]
      simp
    | succ n ih => rw [pow_succ, pow_succ, t2, hχ.1 _ _ (hn n) (GlobalTheory.CharVal.normOne_idTo hs h1 h2), ih]
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 ?_
  rw [← norm_pow, ← hp, ← hyI, GlobalTheory.CharVal.chi_span hs hχ hy, map_prod, norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have h4 := congrArg (s.σ₀.comp (X.emb τ)) hy
  rw [map_mul, hX.conjE, map_one] at h4
  have h5 := congrArg norm h4
  rw [norm_mul, Complex.norm_conj, norm_one, ← sq] at h5
  have h6 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5
  rw [RingHom.comp_apply] at h6
  rw [map_zpow₀, norm_zpow, h6, one_zpow]

end GlobalTheory.GO
