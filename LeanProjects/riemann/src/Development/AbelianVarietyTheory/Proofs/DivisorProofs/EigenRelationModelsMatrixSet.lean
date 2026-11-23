import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFixesScaledLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualUniformDenominatorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ExpandXDenom

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

end GlobalTheory.ExpandXDenom

open GlobalTheory.ExpandXDenom in

theorem GlobalTheory.ExpandXDenom.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), ∃ N : ℕ, 1 ≤ N ∧ ∀ w : Fin d₁ → E,
      e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
  intro _ F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH _ e' hev hB hsp φ hφ
  obtain ⟨r, s, r', s', hX, hW⟩ := hsp
  have hstd : IsStd B.ψ := hB.std
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hB.cm

  have hxy : form σ X.J H.y H.x = 1 := by
    have h1 := hH.xy
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
  obtain ⟨m, β, D, hD, hDen⟩ := GlobalTheory.T.trace_dual_uniform_denominator E (σ : E →+* E) W₁.J hJ

  choose yr zr hyz using fun j : Fin m => hM₁.rat (Matrix.vecMulVec H.x (fun i => (β j i : E)))
  obtain ⟨N, hN, hinv⟩ := GlobalTheory.T.schrodinger_fixes_scaled_lattice F (Fin n × Fin d₁) B.ψ hstd.1 φ hφ m
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
