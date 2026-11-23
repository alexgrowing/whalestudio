import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulus

theorem norm_eq_one_of_locK {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ}
    {j : Fin m} {χ : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (h : IsMu0 Ch σ₀ e j χ)
    (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ) (y : X.K) (hy : σ₀ y = ((χ.locK P x : ℂˣ) : ℂ)) (σ : X.K →+* ℂ) :
    ‖σ y‖ = 1 := by
  have h0 : ((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (hPr.g_prime 0).ne_zero) (by exact_mod_cast (hPr.g_prime 1).ne_zero)
  obtain ⟨M, z, hM, -, -, hz⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E χ
    (divs (((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E))) (GlobalTheory.CharVal.productRule χ)
    (fun v hv => h.unr v fun i hi => hv ((Formalism.L2.Col.mem_divs h0 v).2 (by
      fin_cases i
      exacts [v.asIdeal.mul_mem_right _ hi, v.asIdeal.mul_mem_left _ hi]))) h.tame P x
  obtain ⟨n, -, hn⟩ := h.inf
  have hz' := congrArg Units.val hz
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hn z, ← hy, Units.val_one] at hz'
  have hsq : ∀ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ 2 =
      σ₀ (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) := by
    intro τ
    have h1 : X.embC σ₀ τ z ≠ 0 := (map_ne_zero _).2 z.ne_zero
    have h2 := hX.conjE (X.embC σ₀ τ) z
    rw [map_div₀]
    change _ = X.embC σ₀ τ z / X.embC σ₀ τ (star (z : X.E))
    rw [h2, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h1]
  have key : y ^ (M * 2) * ∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ = 1 := by
    apply σ₀.injective
    rw [map_one, map_mul, map_pow, map_prod, pow_mul]
    have h3 : ∏ τ, σ₀ ((X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ) =
        (∏ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ n τ) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, ← hsq, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [h3, ← mul_pow, hz', one_pow]
  have h4 : ‖σ (∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ)‖ = 1 := by
    rw [map_prod, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 : ‖(σ.comp (X.emb τ)) z‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 z.ne_zero)
    have h2 := hX.conjE (σ.comp (X.emb τ)) z
    rw [RingHom.comp_apply] at h1
    rw [RingHom.comp_apply, RingHom.comp_apply] at h2
    rw [map_zpow₀, norm_zpow, map_div₀, norm_div, h2, Complex.norm_conj, div_self h1, one_zpow]
  have h5 := congrArg (fun t => ‖σ t‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, h4, mul_one, map_one, norm_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h5

theorem norm_muInvDet {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs)
    (ht : Ch.Tied G.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j < R.m) {n : ℕ}
    (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ) :
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr)‖ = 1 := by
  have hU := fun P x y hy => norm_eq_one_of_locK hX hPr (ht.mu0 ⟨j, hj⟩) P x y hy σ
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      ‖σ (Ch.muVal ⟨j, hj⟩ P : X.K)‖ = 1 := fun P hP =>
    hU P (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have hfin := GlobalTheory.CharVal.finOrder_tup mu
  have h1 : ∀ P : rowSG Pr sel mu, ‖σ (cst.muq (j + 1) P)‖ = 1 := by
    intro P
    have hq : ‖σ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
      GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
    have h1 := hL.muqG j hj P (hS P) (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
    have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
        (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
      rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
    have h3 := hU P.1 _ _ h2
    rwa [map_inv₀, map_mul, norm_inv, norm_mul, hq, mul_one, inv_eq_one] at h3
  have h2 : ‖σ (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N)‖ = 1 := by
    unfold muOff
    refine finprod_induction (fun x => ‖σ x‖ = 1) (by simp)
      (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · simp
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dif_pos hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul, norm_inv, norm_inv,
        hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX hPr hsel hv),
        GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
      simp
  rw [muInvDet, map_mul, norm_mul, h2, one_mul, map_prod, norm_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (j + 1) P) _
    ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _)
      (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2) (Units.ne_zero _)
  rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, h1, GlobalTheory.GO.norm_map_of_finOrder _ hζ, one_zpow, one_mul]

theorem norm_muInvDet_zero_or_one : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → ∀ (n : ℕ) (L : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ), ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 0 ∨ ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 1 := by
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h i hi n L fr σ
  obtain ⟨hH, -, ⟨-, hσ, -, ⟨eta, ht⟩, -, hsel⟩, -, hmu, -, hI, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, hX, -, -, hPr, -⟩ := hH
  rw [← hσ] at ht
  refine Or.inr (norm_muInvDet hX.ok hPr hsel (fun P => ?_) ht hI hi L fr σ)
  classical
  subst hmu
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · have h0 := twistPrimes_trivialTuple_empty sel Sg
    exact absurd (h0 ▸ h) (Finset.notMem_empty _)

end GlobalTheory.ScalarModulus
