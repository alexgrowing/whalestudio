import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFixesScaledLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualUniformDenominatorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ExpandDenom

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

theorem ev_rho_rho {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} (B : Base F E)
    (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀) (hψ : IsStd B.ψ) (w u : Matrix (Fin n) (Fin d) (AE F E))
    (hu : u ∈ iso0 (F := F) n H') (Ψ : Fn F n d) (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    e₀ (M.co.rho B.ψ w (M.co.rho B.ψ u Ψ)) =
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w u) • e₀ (M.co.rho B.ψ w Ψ) := by
  have hw : M.co.rho B.ψ w Ψ ∈ schA F (Fin n × Fin d) := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ w Ψ hΨ
  have key : M.co.rho B.ψ w (M.co.rho B.ψ u Ψ) =
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w u) • M.co.rho B.ψ u (M.co.rho B.ψ w Ψ) := by
    simp only [Darboux.rho]
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, GlobalTheory.ThetaQuasiRat.schr_schr, add_comm (M.co.e u), smul_smul,
      ← AddChar.map_add_eq_mul, M.co.form w u]
    congr 2
    have h : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
    linear_combination ((M.co.e w).1 ⬝ᵥ (M.co.e u).2 - (M.co.e u).1 ⬝ᵥ (M.co.e w).2) * h
  rw [key, map_smul, he.inv u hu _ hw]

end GlobalTheory.ExpandDenom

open GlobalTheory.ExpandDenom in

theorem GlobalTheory.ExpandDenom.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : Fin n → E,
      e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH _ e₀ he hB hM hXW Ψ hΨ
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  have hψ : IsStd B.ψ := hB.std

  have hJ : X.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact GlobalTheory.AdaptedPlaneIdeal.det_ne_zero_of_hasSig _ (hX.sig w) h0
  obtain ⟨m, β, D, hD, hDen⟩ := GlobalTheory.T.trace_dual_uniform_denominator E (σ : E →+* E) X.J hJ

  choose yr zr hyz using fun j : Fin m => hM.rat (Matrix.vecMulVec (fun i => (β j i : E)) H'.x)
  obtain ⟨N, hN, hinv⟩ := GlobalTheory.T.schrodinger_fixes_scaled_lattice F (Fin n × Fin d) B.ψ hψ.1 Ψ hΨ m
    (fun j k => algebraMap F (Af F) (yr j k)) (fun j k => algebraMap F (Af F) (zr j k))
  refine ⟨D * N, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD hN), fun ξ hξ => ?_⟩
  set T : AF F := pairA F 0 (N : Af F) with hT
  have hTa : ∀ q : F, T * algebraMap F (AF F) q = pairA F 0 ((N : Af F) * algebraMap F (Af F) q) := by
    intro q
    refine Prod.ext ?_ ?_
    · exact zero_mul _
    · rfl

  have hfix : ∀ j, M.co.rho B.ψ (Matrix.vecMulVec (T • incV F (fun i => (β j i : E))) (incV F H'.x)) Ψ = Ψ := by
    intro j
    have e1 : Matrix.vecMulVec (T • incV F (fun i => (β j i : E))) (incV F H'.x) =
        T • incM F (Matrix.vecMulVec (fun i => (β j i : E)) H'.x) := by
      ext a b
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, incM, incV, Matrix.map_apply, map_mul,
        smul_mul_assoc]
    rw [Darboux.rho, e1, map_smul, hyz j]
    convert hinv j using 2
    refine Prod.ext ?_ ?_
    · funext k
      exact hTa (yr j k)
    · funext k
      exact hTa (zr j k)
  have hform : form σ W.J H'.y H'.x = -1 := by
    have h1 := hH.xy
    have h2 : σ (form σ W.J H'.x H'.y) = -form σ W.J H'.y H'.x := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hW.skew, Finset.mul_sum, neg_mul, mul_neg,
        Finset.sum_neg_distrib, AlgHom.commutes]
      rw [Finset.sum_comm]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_)
      rw [GlobalTheory.AdelicU.cm_conj_conj hB.cm]
      ring
    rw [h1, map_one] at h2
    linear_combination h2

  have htr : ∀ j, ∃ z : ℤ, Algebra.trace ℚ E ((fun i => ((N : ℕ) : E) * ξ i) ⬝ᵥ X.J *ᵥ fun i => (σ : E →+* E) (β j i)) = z := by
    intro j
    have hu : Matrix.vecMulVec (T • incV F (fun i => (β j i : E))) (incV F H'.x) ∈ iso0 (F := F) n H' :=
      ⟨_, rfl⟩
    have h1 := ev_rho_rho B M M₁ H' e₀ he hψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) _ hu Ψ hΨ
    rw [hfix j, symp_vecMulVec, hform, mul_neg_one, neg_neg, hTa] at h1
    have h2 : B.ψ (pairA F 0 ((N : Af F) * algebraMap F (Af F) (Algebra.trace F E (form σ X.J ξ fun i => (β j i : E))))) = 1 := by
      by_contra hne
      apply hξ
      have h3 : (1 - B.ψ (pairA F 0 ((N : Af F) * algebraMap F (Af F) (Algebra.trace F E (form σ X.J ξ fun i => (β j i : E)))))) •
          e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ) = 0 := by
        rw [sub_smul, one_smul, ← h1, sub_self]
      exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm hne))
    rw [← map_natCast (algebraMap F (Af F)) N, ← map_mul, GlobalTheory.PsiNontriv.isStd_fin_rat hψ,
      Complex.exp_eq_one_iff] at h2
    obtain ⟨z, hz⟩ := h2
    refine ⟨z, ?_⟩
    have hq : ((Algebra.trace ℚ F ((N : F) * Algebra.trace F E (form σ X.J ξ fun i => (β j i : E))) : ℚ) : ℂ) = z := by
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      apply mul_left_cancel₀ hpi
      rw [hz]; ring
    have hq' : Algebra.trace ℚ F ((N : F) * Algebra.trace F E (form σ X.J ξ fun i => (β j i : E))) = z := by
      exact_mod_cast hq
    have e1 : ((fun i => ((N : ℕ) : E) * ξ i) ⬝ᵥ X.J *ᵥ fun i => (σ : E →+* E) (β j i)) =
        algebraMap F E (N : F) * form σ X.J ξ (fun i => (β j i : E)) := by
      rw [map_natCast, show (fun i => ((N : ℕ) : E) * ξ i) = ((N : ℕ) : E) • ξ from rfl, smul_dotProduct, smul_eq_mul]
      rfl
    rw [e1, ← Algebra.trace_trace (R := ℚ) (S := F) (T := E), ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact hq'
  intro i
  obtain ⟨o, ho⟩ := hDen _ htr i
  exact ⟨o, by rw [← ho]; push_cast; ring⟩
