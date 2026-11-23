import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFiniteApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFixesScaledLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualUniformDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThKCptBoundX

open scoped ENNReal in

theorem tsum_norm_le_of_bdd_pairing : ∀ {ι K : Type} (x : K → ι → ℂ), (∀ u, Summable fun i => ‖x u i‖) →
    (∀ c : ι → ℂ, (∃ b : ℝ, ∀ i, ‖c i‖ ≤ b) → ∃ C : ℝ, ∀ u, ‖∑' i, c i * x u i‖ ≤ C) →
    ∃ C : ℝ, ∀ u, ∑' i, ‖x u i‖ ≤ C := by
  intro ι K x hx hc
  have key : ∀ u (c : ι → ℂ) (b : ℝ), (∀ i, ‖c i‖ ≤ b) → Summable fun i => c i * x u i := fun u c b hb =>
    Summable.of_norm_bounded ((hx u).mul_left b) (fun i => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
  have hle : ∀ (c : lp (fun _ : ι => ℂ) ∞) i, ‖c i‖ ≤ ‖c‖ := fun c i => lp.norm_apply_le_norm ENNReal.top_ne_zero c i
  let T : K → lp (fun _ : ι => ℂ) ∞ →L[ℂ] ℂ := fun u =>
    LinearMap.mkContinuous
      { toFun := fun c => ∑' i, c i * x u i
        map_add' := fun c c' => by
          rw [← (key u _ _ (hle c)).tsum_add (key u _ _ (hle c'))]
          congr 1; funext i
          rw [lp.coeFn_add, Pi.add_apply, add_mul]
        map_smul' := fun a c => by
          rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
          congr 1; funext i
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc] }
      (∑' i, ‖x u i‖) (fun c => by
        show ‖∑' i, c i * x u i‖ ≤ (∑' i, ‖x u i‖) * ‖c‖
        have hs : Summable fun i => ‖c‖ * ‖x u i‖ := (hx u).mul_left _
        calc ‖∑' i, c i * x u i‖ ≤ ∑' i, ‖c i * x u i‖ :=
              norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
                (fun i => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _)) hs)
          _ ≤ ∑' i, ‖c‖ * ‖x u i‖ := Summable.tsum_le_tsum (fun i => by
                rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _))
              (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
                (fun i => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _)) hs) hs
          _ = (∑' i, ‖x u i‖) * ‖c‖ := by rw [tsum_mul_left, mul_comm])
  have hT : ∀ u c, T u c = ∑' i, c i * x u i := fun u c => rfl
  obtain ⟨C', hC'⟩ := banach_steinhaus (g := T) (fun c => by
    obtain ⟨C, hC⟩ := hc (fun i => c i) ⟨‖c‖, hle c⟩
    exact ⟨C, fun u => by rw [hT]; exact hC u⟩)
  refine ⟨max C' 0, fun u => ?_⟩
  let cu : ι → ℂ := fun i => starRingEnd ℂ (x u i) / (‖x u i‖ : ℂ)
  have hcu : ∀ i, ‖cu i‖ ≤ 1 := fun i => by
    simp only [cu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have hmem : Memℓp cu ∞ := memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; exact hcu i⟩
  let c : lp (fun _ : ι => ℂ) ∞ := ⟨cu, hmem⟩
  have hc1 : ‖c‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one (fun i => hcu i)
  have hmul : ∀ i, cu i * x u i = ((‖x u i‖ : ℝ) : ℂ) := fun i => by
    simp only [cu]
    rcases eq_or_ne (x u i) 0 with h | h
    · simp [h]
    · have hn : (‖x u i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
      push_cast; ring
  have e : T u c = ((∑' i, ‖x u i‖ : ℝ) : ℂ) := by
    rw [hT, Complex.ofReal_tsum]
    exact tsum_congr fun i => hmul i
  have h1 : ∑' i, ‖x u i‖ = ‖T u c‖ := by
    rw [e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun i => norm_nonneg _)]
  rw [h1]
  calc ‖T u c‖ ≤ ‖T u‖ * ‖c‖ := (T u).le_opNorm c
    _ ≤ ‖T u‖ * 1 := mul_le_mul_of_nonneg_left hc1 (norm_nonneg _)
    _ ≤ max C' 0 := by rw [mul_one]; exact (hC' u).trans (le_max_left _ _)

section Pairing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] [FiniteDimensional F E] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem symp_vecMulVec {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (ξ β : Fin n → E) (y x : Fin d → E) (T : AF F) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (Matrix.vecMulVec (incV F ξ) (incV F y))
      (Matrix.vecMulVec (T • incV F β) (incV F x)) =
      T * algebraMap F (AF F) (Algebra.trace F E (-(form σ JX ξ β * form σ JW y x))) := by
  have hT : hTens (cA σ) (incM F JX) (incM F JW) (Matrix.vecMulVec (incV F ξ) (incV F y))
      (Matrix.vecMulVec (T • incV F β) (incV F x)) =
      algebraMap (AF F) (AE F E) T * inclR (F := F) (AF F) (form σ JX ξ β * form σ JW y x) := by
    simp only [hTens, Matrix.vecMulVec_apply, Pi.smul_apply, incM, incV, Matrix.map_apply]
    simp only [form, dotProduct, Matrix.mulVec, Algebra.smul_def, map_mul, cA_inclR, AlgHom.commutes, map_sum,
      Finset.mul_sum, Finset.sum_mul]
    symm
    refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [symp, hT, show inclR (F := F) (AF F) (form σ JX ξ β * form σ JW y x) =
      (1 : AF F) ⊗ₜ[F] (form σ JX ξ β * form σ JW y x) from rfl, ← Algebra.smul_def, mul_smul_comm,
    map_smul, smul_eq_mul, show (-1 : AE F E) * ((1 : AF F) ⊗ₜ[F] (form σ JX ξ β * form σ JW y x)) =
      (1 : AF F) ⊗ₜ[F] (-(form σ JX ξ β * form σ JW y x)) by rw [neg_one_mul, TensorProduct.tmul_neg],
    trace_tmul, one_mul]

end Pairing

theorem ev_pairing_trivial : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), IsEv B M M₁ ι ι' I e → IsStd B.ψ →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ a b : Matrix (Fin n) (Fin d) (AE F E), b ∈ I → M.co.rho B.ψ b Φ = Φ →
      e (M.co.rho B.ψ a Φ) ≠ 0 → B.ψ ((M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2) = 1 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hev hstd Φ hΦ a b hbI hb hne
  set c := (M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2 with hc
  have hρa : M.co.rho B.ψ a Φ ∈ schA F _ := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd a Φ hΦ
  have h1 : e (M.co.rho B.ψ a Φ) = B.ψ (⅟(2 : AF F) * c) • e (schr B.ψ (M.co.e a + M.co.e b) Φ) := by
    conv_lhs => rw [← hb]
    show e (schr B.ψ (M.co.e a) (schr B.ψ (M.co.e b) Φ)) = _
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, map_smul]
  have h2 : e (M.co.rho B.ψ a Φ) = B.ψ (⅟(2 : AF F) * -c) • e (schr B.ψ (M.co.e a + M.co.e b) Φ) := by
    rw [← hev.inv b hbI _ hρa]
    show e (schr B.ψ (M.co.e b) (schr B.ψ (M.co.e a) Φ)) = _
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, map_smul, add_comm (M.co.e b)]
    congr 2
    rw [hc]; ring
  have hG : e (schr B.ψ (M.co.e a + M.co.e b) Φ) ≠ 0 := by
    intro h0; rw [h1, h0, smul_zero] at hne; exact hne rfl
  have h3 : B.ψ (⅟(2 : AF F) * c) = B.ψ (⅟(2 : AF F) * -c) := smul_left_injective ℂ hG (h1.symm.trans h2)
  have h4 : c = ⅟(2 : AF F) * c + ⅟(2 : AF F) * c := by
    rw [← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
  rw [h4, AddChar.map_add_eq_mul]
  conv_lhs => arg 2; rw [h3]
  rw [← AddChar.map_add_eq_mul, mul_neg, add_neg_cancel, AddChar.map_zero_eq_one]

theorem denom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (M₂ : Model σ X₁ W₁), form σ X.J H.x H.y = 1 → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), ∃ N : ℕ, 1 ≤ N ∧ ∀ w : Fin d₁ → E,
      e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
  intro F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH _ e' hev hB hsp φ hφ
  obtain ⟨r, s, r', s', hX, hW⟩ := hsp
  have hstd : IsStd B.ψ := hB.std
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hB.cm

  have hxy : form σ X.J H.y H.x = 1 := by
    have h1 := hH
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

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay GlobalTheory.IsoXArchDecay in

theorem arch_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (M₂ : Model σ X₁ W₁), form σ X.J H.x H.y = 1 → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ Φ ∈ schA F (Fin n × Fin d₁), ∀ N K : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := by
  intro F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH hM₂ e' hev hB hsig Φ hΦ N K hN
  obtain ⟨r, s, r', s', hX, hW⟩ := hsig
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin d₁)
  have hadm := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d₁ n₁ d₁ X W₁ X₁ W₁ M₁ M₂ H.ι 1 _ e' hM₁ hM₂ hev l hl
  obtain ⟨x', hx'⟩ := exists_dual_vec σ W₁.J (det_ne_zero_of_skew hW)
  have hyx : form σ X.J H.y H.x = 1 := by rw [form_swap_herm hB.cm hX.herm, hH, map_one]
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
    hinv Φ hΦ K
  obtain ⟨A, hA, hAw⟩ := sum_places_le (F := F) (E := E) d₁
  refine ⟨max C₁ 0 * (1 + A) ^ K, fun w _ => ?_⟩
  let x : Fin d₁ × Fin (Module.finrank F E) → AF F := fun p =>
    realAd F 1 * algebraMap F (AF F) ((Module.finBasis F E).repr (w p.1) p.2)
  have hx : ∀ p, p2 (x p) = 0 := fun p => real_adele_mul_finite_part_zero _
  have hrho : M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ =
      schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ := by
    rw [Darboux.rho, vecMulVec_sum, map_sum]
    simp only [map_smul]
    rfl
  have hθ : thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ)) =
      (l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ) := by
    rw [hrho, LinearMap.comp_apply, hlθ _ (hev.maps _ (schr_mem_schA B.ψ hB.std _ _ hΦ))]
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
  have h3 : ‖(l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ)‖ ≤ max C₁ 0 * (1 + ρ) ^ (-(K : ℝ)) :=
    hb.trans (by gcongr; exact le_max_left _ _)
  calc _ ≤ (max C₁ 0 * (1 + ρ) ^ (-(K : ℝ))) * ((1 + A) ^ K * (1 + ρ) ^ K) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ = max C₁ 0 * (1 + A) ^ K * ((1 + ρ) ^ (-(K : ℝ)) * (1 + ρ) ^ K) := by ring
    _ = _ := by rw [h2, mul_one]

theorem thetaSum_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (M₂ : Model σ X₁ W₁), form σ X.J H.x H.y = 1 → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), ∀ N K : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := by
  intro F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH hM₂ e' hev hB hsig φ hφ N K hN
  obtain ⟨S, hSf, hSs, hS⟩ := GlobalTheory.FinPartHeis.finPart_right F E σ B n d₁ X W₁ M₁ H.y hB hM₁ φ hφ N hN
  have hC : ∀ Φ, Φ ∈ S → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := fun Φ hΦ =>
    arch_decay F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH hM₂ e' hev hB hsig Φ (hSs hΦ) N K hN
  choose! C hC using hC
  refine ⟨∑ Φ ∈ hSf.toFinset, max (C Φ) 0, fun w hw => ?_⟩
  obtain ⟨Φ, hΦS, hΦe⟩ := hS w hw
  rw [hΦe]
  calc _ ≤ C Φ := hC Φ hΦS w hw
    _ ≤ max (C Φ) 0 := le_max_left _ _
    _ ≤ _ := Finset.single_le_sum (f := fun Φ => max (C Φ) 0) (fun _ _ => le_max_right _ _) (hSf.mem_toFinset.2 hΦS)

theorem summable_of_denom_decay' (E : Type) [Field E] [NumberField E] (n : ℕ) :
    ∃ K : ℕ, ∀ (N : ℕ) (h : (Fin n → E) → ℂ), 1 ≤ N → (∀ ξ, h ξ ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ∀ C : ℝ, (∀ ξ, ‖h ξ‖ * (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C) → Summable h := by
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice E (Fin n) one_pos
  set L := GlobalTheory.WeilM.denomLattice E (Fin n) 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  refine ⟨r, fun M h hM hsupp B hdec => ?_⟩
  have hB : 0 ≤ B := le_trans (by positivity) (hdec 0)
  let S : Set (Fin n → E) := {ξ | ∀ i, ∃ o : 𝓞 E, (M : E) * ξ i = o}
  let v : (Fin n → E) → (Fin n → mixedEmbedding.mixedSpace E) := fun ξ i => mixedEmbedding E ((M : E) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding E ((M : E) * ξ i) ∈ mixedEmbedding.integerLattice E
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : E) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective E (congrFun (congrArg Subtype.val hab) i)))
  let G : (Fin n → E) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact (hL.comp_injective hj).mul_left _
  have hbound : ∀ ξ : Fin n → E, ‖h ξ‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : h ξ = 0
    · rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace E, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := GlobalTheory.RatPointSum.norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding E ((M : E) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : ‖h ξ‖ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  exact Summable.of_norm_bounded hGs hbound

theorem summable_terms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (M₂ : Model σ X₁ W₁), form σ X.J H.x H.y = 1 → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), Summable (fun w : Fin d₁ → E => thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ))) := by
  intro F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH hM₂ e' he hB hXW φ hφ
  obtain ⟨N, hN, hsupp⟩ := denom F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH hM₂ e' he hB hXW φ hφ
  obtain ⟨K, hA⟩ := summable_of_denom_decay' E d₁
  obtain ⟨C, hC⟩ := thetaSum_decay F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H M₂ hH hM₂ e' he hB hXW φ hφ N K hN
  have hz : ∀ w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) ≠ 0 →
      ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
    intro w h0
    refine hsupp w fun h1 => h0 ?_
    rw [h1]
    simp [thetaSum]
  refine hA N _ hN hz (max C 0) fun w => ?_
  by_cases hw : ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o
  · exact (hC w hw).trans (le_max_left _ _)
  · have h0 : thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) = 0 := by
      by_contra h
      exact hw (hz w h)
    rw [h0, norm_zero, zero_mul]
    exact le_max_right _ _

theorem sum_norm_bdd : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ K : Set (unip σ X H), IsCompact K → ∃ C : ℝ, ∀ u ∈ K,
      Summable (fun w : Fin d → E => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))‖) ∧ ∑' w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))‖ ≤ C := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ _ d₂ H hH V₁ M₁ e _ hM₁ hEv Ψ hΨ K hK
  set l : (Fin d → E) → Fn F n d → ℂ := fun w Φ =>
    thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Φ)) with hl
  have hψ : IsStd B.ψ := hP.base.std
  have summ0 : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun w => l w Φ :=
    summable_terms F E σ B n d X W M hP.good d₂ V₁ H M₁ hH.2.2.2.1 hM₁ e hEv hP.base ⟨r, s, r', s', hP.herm, hP.skew⟩
  have summ : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun w => ‖l w Φ‖ := fun Φ hΦ => (summ0 Φ hΦ).norm
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin d₂ × Fin d)
  have hl₁ := GlobalTheory.ConeMeasV.comp_ev_mem_adm hP.good hM₁ hEv hl₀
  have hterm : ∀ w : Fin d → E, ∃ Lw ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d), Lw Φ = l w Φ := by
    intro w
    refine ⟨_, GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hl₁, fun Φ hΦ => ?_⟩
    have h1 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hΦ
    exact hl₀eq _ (hEv.maps _ h1)
  choose Lw hLw hLwe using hterm
  have adm : ∀ c : (Fin d → E) → ℂ, (∃ b : ℝ, ∀ w, ‖c w‖ ≤ b) →
      ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d), L Φ = ∑' w, c w * l w Φ := by
    rintro c ⟨b, hb⟩
    have hs : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun w => c w * l w Φ := fun Φ hΦ =>
      Summable.of_norm_bounded ((summ Φ hΦ).mul_left b) (fun w => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb w) (norm_nonneg _))
    let Lc : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
      { toFun := fun Φ => ∑' w, c w * l w Φ.1
        map_add' := fun Φ Φ' => by
          rw [← (hs _ Φ.2).tsum_add (hs _ Φ'.2)]
          congr 1
          funext w
          rw [← hLwe w _ (Φ + Φ').2, ← hLwe w _ Φ.2, ← hLwe w _ Φ'.2, Submodule.coe_add, map_add]
          ring
        map_smul' := fun a Φ => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← tsum_mul_left]
          congr 1
          funext w
          rw [← hLwe w _ (a • Φ).2, ← hLwe w _ Φ.2, Submodule.coe_smul, map_smul, smul_eq_mul]
          ring }
    obtain ⟨L, hL⟩ := LinearMap.exists_extend Lc
    have hLe : ∀ Φ (hΦ : Φ ∈ schA F (Fin n × Fin d)), L Φ = Lc ⟨Φ, hΦ⟩ := fun Φ hΦ => by
      have := LinearMap.congr_fun hL ⟨Φ, hΦ⟩
      simpa using this
    refine ⟨L, ?_, fun Φ hΦ => hLe Φ hΦ⟩
    intro g hg
    have hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f g ∈ schA F (Fin n × Fin d) :=
      fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
    choose T hT using fun w => hLw w g hg
    have hT' : ∀ w f, (c w • T w) f = c w * l w (pureA F f g) := fun w f => by
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, ← hT w f, hLwe w _ (hmem f)]
    haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    obtain ⟨en, hen⟩ := exists_surjective_nat (Fin d → E)
    let S : ℕ → Finset (Fin d → E) := fun N => (Finset.range N).image en
    have hS : Tendsto S atTop atTop := by
      refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)
      · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
      · obtain ⟨k, rfl⟩ := hen w
        exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
    haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
    have hlim : Tendsto (fun N f => (∑ w ∈ S N, c w • T w) f) atTop
        (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' w, c w * l w (pureA F f g)) := by
      rw [tendsto_pi_nhds]
      intro f
      simp only [ContinuousLinearMap.sum_apply, hT']
      exact (hs _ (hmem f)).hasSum.comp hS
    refine ⟨continuousLinearMapOfTendsto (fun N => ∑ w ∈ S N, c w • T w) hlim, fun f => ?_⟩
    show _ = linearMapOfTendsto _ _ hlim f
    rw [linearMapOfTendsto_apply, hLe _ (hmem f)]
    rfl
  have hpres : ∀ u : UA σ X.J, om (u, 1) Ψ ∈ schA F (Fin n × Fin d) := fun u =>
    (IsUWeilPair.isUSplitting hP.weil).pres (u, 1) Ψ hΨ
  obtain ⟨C, hC⟩ := tsum_norm_le_of_bdd_pairing (K := K) (fun u w => l w (om (u.1.1, 1) Ψ)) (fun u => summ _ (hpres _)) (fun c hc => by
    obtain ⟨L, hL, hLe⟩ := adm c hc
    have hcont : Continuous fun p : UA σ X.J × UA σ W.J => L (om p Ψ) :=
      (IsUWeilPair.isUSplitting hP.weil).cont L hL Ψ hΨ
    have hc2 : Continuous fun u : unip σ X H => L (om (u.1, 1) Ψ) :=
      hcont.comp (continuous_subtype_val.prodMk continuous_const)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
    exact ⟨C, fun u => by rw [← hLe _ (hpres _)]; exact hC u.1 u.2⟩)
  exact ⟨C, fun u hu => ⟨summ _ (hpres _), hC ⟨u, hu⟩⟩⟩

end GlobalTheory.ThKCptBoundX
