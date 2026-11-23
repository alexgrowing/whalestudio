import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFiniteApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRelationModelsMatrixSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualUniformDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFixesScaledLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEvaluation

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ExpandSummPair

open GlobalTheory.ExpandXDenom GlobalTheory.IsoXArchDecay GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

theorem denom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d₁ n₁ : ℕ} {X : Spc F E n} {W₁ : Spc F E d₁} {X₁ : Spc F E n₁} (M₁ : Model σ X W₁) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁) (hM₁ : M₁.IsGood B.ψ) (hM₂ : M₂.IsGood B.ψ)
    (hev : IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e') (hB : B.IsGood σ)
    (hsp : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') (hxy0 : form σ X.J H.x H.y = 1)
    (φ : Fn F n d₁) (hφ : φ ∈ schA F (Fin n × Fin d₁)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : Fin d₁ → E,
      e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
  obtain ⟨r, s, r', s', hX, hW⟩ := hsp
  have hstd : IsStd B.ψ := hB.std
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hB.cm

  have hxy : form σ X.J H.y H.x = 1 := by
    have h1 := hxy0
    have e1 : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσσ]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hX.herm]
      ring
    rw [e1, h1, map_one]

  have hJ : W₁.J.det ≠ 0 := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hW.sig v)
    rw [Matrix.det_smul] at h
    have h' : (W₁.J.map (B.emb v).1).det ≠ 0 := right_ne_zero_of_mul h
    intro h0
    apply h'
    have := RingHom.map_det (B.emb v).1 W₁.J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨m, β, D, hD, hDen⟩ := GlobalTheory.DenomTrace.integral_traces_bounded_denominators E (σ : E →+* E) W₁.J hJ

  choose yr zr hyz using fun j : Fin m => hM₁.rat (Matrix.vecMulVec H.x (fun i => (β j i : E)))
  obtain ⟨N, hN, hinv⟩ := GlobalTheory.SmallHeisFix.main F (Fin n × Fin d₁) B.ψ hstd.1 φ hφ m
    (fun j k => algebraMap F (Af F) (yr j k)) (fun j k => algebraMap F (Af F) (zr j k))
  refine ⟨D * N, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD hN), fun w hw => ?_⟩
  set T : AF F := pairA F 0 (N : Af F) with hT
  have hTa : ∀ q : F, T * algebraMap F (AF F) q = pairA F 0 ((N : Af F) * algebraMap F (Af F) q) := by
    intro q
    refine Prod.ext ?_ ?_
    · exact zero_mul _
    · rfl
  have hbeq : ∀ j, Matrix.vecMulVec (incV F H.x) (T • incV F (fun i => (β j i : E))) =
      Matrix.vecMulVec (T • incV F H.x) (incV F (fun i => (β j i : E))) := by
    intro j
    ext a c
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]

  have hfix : ∀ j, M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (T • incV F (fun i => (β j i : E)))) φ = φ := by
    intro j
    have e1 : Matrix.vecMulVec (incV F H.x) (T • incV F (fun i => (β j i : E))) =
        T • incM F (Matrix.vecMulVec H.x (fun i => (β j i : E))) := by
      ext a c
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, incM, incV, Matrix.map_apply, map_mul,
        mul_smul_comm]
    rw [Darboux.rho, e1, map_smul, hyz j]
    convert hinv j using 2
    refine Prod.ext ?_ ?_
    · funext k
      exact hTa (yr j k)
    · funext k
      exact hTa (zr j k)
  have htr : ∀ j, ∃ z : ℤ, Algebra.trace ℚ E ((fun i => ((N : ℕ) : E) * w i) ⬝ᵥ W₁.J *ᵥ fun i => (σ : E →+* E) (β j i)) = z := by
    intro j
    have hψ := ev_pairing_trivial B M₁ M₂ H.ι 1 _ e' hev hstd φ hφ _ _ ⟨_, rfl⟩ (hfix j) hw
    rw [← M₁.co.form, hbeq j, symp_vecMulVec, hxy, one_mul, hTa,
      ← map_natCast (algebraMap F (Af F)) N, ← map_mul, GlobalTheory.PsiNontriv.isStd_fin_rat hstd,
      Complex.exp_eq_one_iff] at hψ
    obtain ⟨z, hz⟩ := hψ
    refine ⟨-z, ?_⟩
    have hq : ((Algebra.trace ℚ F ((N : F) * Algebra.trace F E (-form σ W₁.J w fun i => (β j i : E))) : ℚ) : ℂ) = z := by
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      apply mul_left_cancel₀ hpi
      rw [hz]; ring
    have hq' : Algebra.trace ℚ F ((N : F) * Algebra.trace F E (-form σ W₁.J w fun i => (β j i : E))) = z := by
      exact_mod_cast hq
    have e1 : ((fun i => ((N : ℕ) : E) * w i) ⬝ᵥ W₁.J *ᵥ fun i => (σ : E →+* E) (β j i)) =
        -(algebraMap F E (N : F) * -form σ W₁.J w (fun i => (β j i : E))) := by
      rw [map_natCast, show (fun i => ((N : ℕ) : E) * w i) = ((N : ℕ) : E) • w from rfl, smul_dotProduct, smul_eq_mul,
        mul_neg, neg_neg]
      rfl
    rw [e1, map_neg, ← Algebra.trace_trace (R := ℚ) (S := F) (T := E), ← Algebra.smul_def, map_smul, smul_eq_mul, hq',
      Int.cast_neg]
  intro i
  obtain ⟨o, ho⟩ := hDen _ htr i
  exact ⟨o, by rw [← ho]; push_cast; ring⟩

theorem arch_decay {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d₁ n₁ : ℕ} {X : Spc F E n} {W₁ : Spc F E d₁} {X₁ : Spc F E n₁} (M₁ : Model σ X W₁) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁) (hM₁ : M₁.IsGood B.ψ) (hM₂ : M₂.IsGood B.ψ)
    (hev : IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e') (hB : B.IsGood σ)
    (hsp : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') (hxy0 : form σ X.J H.x H.y = 1)
    (φ : Fn F n d₁) (hφ : φ ∈ schA F (Fin n × Fin d₁)) (N K : ℕ) :
    ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := by
  obtain ⟨r, s, r', s', hX, hW⟩ := hsp
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin d₁)
  have hadm := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d₁ n₁ d₁ X W₁ X₁ W₁ M₁ M₂ H.ι 1 _ e' hM₁ hM₂ hev l hl
  obtain ⟨x', hx'⟩ := exists_dual_vec σ W₁.J (det_ne_zero_of_skew hW)
  have hyx : form σ X.J H.y H.x = 1 := by rw [form_swap_herm hB.cm hX.herm, hxy0, map_one]
  obtain ⟨t, ht⟩ := dualPair_family σ X.J W₁.J H.y H.x x' hyx hx'
  let Sm : Fin d₁ × Fin (Module.finrank F E) → Matrix (Fin n) (Fin d₁) (AE F E) := fun q =>
    inclR (F := F) (AF F) (Module.finBasis F E q.2) • Matrix.vecMulVec (incV F H.y) (incV F (Pi.single q.1 1))
  let Um : Fin d₁ × Fin (Module.finrank F E) → Matrix (Fin n) (Fin d₁) (AE F E) := fun p =>
    Matrix.vecMulVec (inclR (F := F) (AF F) (t p.2) • incV F H.x) (incV F (x' p.1))
  have hUI : ∀ p (a : AF F), a • Um p ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} := fun p a =>
    ⟨a • inclR (F := F) (AF F) (t p.2) • incV F (x' p.1), smul_vecMulVec_move _ _ _ _⟩
  have hinv : ∀ p (a : AF F), ∀ Ψ ∈ schA F (Fin n × Fin d₁),
      (l ∘ₗ e') (schr B.ψ (a • M₁.co.e (Um p)) Ψ) = (l ∘ₗ e') Ψ := fun p a Ψ hΨ => by
    rw [← map_smul, LinearMap.comp_apply, LinearMap.comp_apply]
    exact congrArg l (hev.inv _ (hUI p a) Ψ hΨ)
  obtain ⟨C₁, hC₁⟩ := scalar_decay B.ψ hB.std (fun q => M₁.co.e (Sm q)) (fun p => M₁.co.e (Um p))
    (fun p q => by rw [← M₁.co.form]; convert ht p q) (l ∘ₗ e') hadm
    hinv φ hφ K
  obtain ⟨A, hA, hAw⟩ := sum_places_le (F := F) (E := E) d₁
  refine ⟨max C₁ 0 * (1 + A) ^ K, fun w _ => ?_⟩
  let x : Fin d₁ × Fin (Module.finrank F E) → AF F := fun p =>
    realAd F 1 * algebraMap F (AF F) ((Module.finBasis F E).repr (w p.1) p.2)
  have hx : ∀ p, p2 (x p) = 0 := fun p => real_adele_mul_finite_part_zero _
  have hrho : M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) φ =
      schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) φ := by
    rw [Darboux.rho, vecMulVec_sum, map_sum]
    simp only [map_smul]
    rfl
  have hθ : thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) =
      (l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) φ) := by
    rw [hrho, LinearMap.comp_apply, hlθ _ (hev.maps _ (schr_mem_schA B.ψ hB.std _ _ hφ))]
  have hb := hC₁ x hx
  have hr : ∑ p, ∑ v : InfinitePlace F, ‖(x p).1 v‖ =
      ∑ p : Fin d₁ × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2) := by
    simp only [x, norm_realAd_mul_algebraMap]
  rw [hr] at hb
  set ρ := ∑ p : Fin d₁ × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2)
    with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hR := hAw w
  have hR0 : 0 ≤ ∑ i, ∑ v : InfinitePlace E, v (w i) := by positivity
  rw [hθ]
  have h1 : (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ (1 + A) ^ K * (1 + ρ) ^ K := by
    rw [← mul_pow]
    gcongr
    nlinarith [mul_nonneg hA hρ0]
  have h2 : (1 + ρ) ^ (-(K : ℝ)) * (1 + ρ) ^ K = 1 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
  have h3 : ‖(l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) φ)‖ ≤ max C₁ 0 * (1 + ρ) ^ (-(K : ℝ)) :=
    hb.trans (by gcongr; exact le_max_left _ _)
  calc _ ≤ (max C₁ 0 * (1 + ρ) ^ (-(K : ℝ))) * ((1 + A) ^ K * (1 + ρ) ^ K) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ = max C₁ 0 * (1 + A) ^ K * ((1 + ρ) ^ (-(K : ℝ)) * (1 + ρ) ^ K) := by ring
    _ = _ := by rw [h2, mul_one]

theorem decay {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d₁ n₁ : ℕ} {X : Spc F E n} {W₁ : Spc F E d₁} {X₁ : Spc F E n₁} (M₁ : Model σ X W₁) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁) (hM₁ : M₁.IsGood B.ψ) (hM₂ : M₂.IsGood B.ψ)
    (hev : IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e') (hB : B.IsGood σ)
    (hsp : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') (hxy0 : form σ X.J H.x H.y = 1)
    (φ : Fn F n d₁) (hφ : φ ∈ schA F (Fin n × Fin d₁)) (N K : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := by
  obtain ⟨S, hSf, hSs, hS⟩ := GlobalTheory.FinPartHeis.finPart_right F E σ B n d₁ X W₁ M₁ H.y hB hM₁ φ hφ N hN
  have hC : ∀ Φ, Φ ∈ S → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := fun Φ hΦ =>
    arch_decay B M₁ M₂ H e' hM₁ hM₂ hev hB hsp hxy0 Φ (hSs hΦ) N K
  choose! C hC using hC
  refine ⟨∑ Φ ∈ hSf.toFinset, max (C Φ) 0, fun w hw => ?_⟩
  obtain ⟨Φ, hΦS, hΦe⟩ := hS w hw
  rw [hΦe]
  calc _ ≤ C Φ := hC Φ hΦS w hw
    _ ≤ max (C Φ) 0 := le_max_left _ _
    _ ≤ _ := Finset.single_le_sum (f := fun Φ => max (C Φ) 0) (fun _ _ => le_max_right _ _) (hSf.mem_toFinset.2 hΦS)

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Ψ ∈ schA F (Fin n × Fin d), Summable (fun w : Fin d → E => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ))) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e _ hM₁ hev Ψ hΨ
  have hsp : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s' := ⟨r, s, r', s', hP.herm, hP.skew⟩
  have hxy0 : form σ X.J H.x H.y = 1 := hH.2.2.2.1
  obtain ⟨N, hN, hsupp⟩ := denom B M M₁ H e hP.good hM₁ hev hP.base hsp hxy0 Ψ hΨ
  obtain ⟨K, hA⟩ := GlobalTheory.ExpandSummX.summable_of_denom_decay' E d
  obtain ⟨C, hC⟩ := decay B M M₁ H e hP.good hM₁ hev hP.base hsp hxy0 Ψ hΨ N K hN
  have hz : ∀ w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)) ≠ 0 →
      ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
    intro w h0
    refine hsupp w fun h1 => h0 ?_
    rw [h1]
    simp [thetaSum]
  refine hA N _ hN hz (max C 0) fun w => ?_
  by_cases hw : ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o
  · exact (hC w hw).trans (le_max_left _ _)
  · have h0 : thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)) = 0 := by
      by_contra h
      exact hw (hz w h)
    rw [h0, norm_zero, zero_mul]
    exact le_max_right _ _

end GlobalTheory.ExpandSummPair
