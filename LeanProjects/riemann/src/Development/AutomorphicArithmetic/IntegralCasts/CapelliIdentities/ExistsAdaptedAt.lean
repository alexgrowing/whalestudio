import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignatureBlockDiagonal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianPositiveSymplectic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TraceEqSumReCmType

namespace UpperTheory.Reformulated.B.Gwb8

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GroundTheory.Automorphic
  GroundTheory.Heights₂.Heights.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

omit [IsCMField E] in
private theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
private theorem embOf_comp (s : 𝓞 E →+* ℂ) : (embOf s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun a => embOf_coe s a

omit [IsCMField E] in
private theorem embOf_eq_iff (s : 𝓞 E →+* ℂ) (t : E →+* ℂ) :
    embOf s = t ↔ s = t.comp (algebraMap (𝓞 E) E) := by
  constructor
  · rintro rfl
    exact (embOf_comp s).symm
  · rintro rfl
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (embOf_comp _)

private theorem trace_sum (F : UnivFam E Ψ j j' n g Λ) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (embOf (F.σ τ) x).re := by
  refine UpperTheory.trace_eq_sum_re_cm_type (fun τ => embOf (F.σ τ)) ?_ ?_ x
  · intro a b hab
    apply F.cm.1
    rw [← embOf_comp (F.σ a), ← embOf_comp (F.σ b)]
    exact congrArg (fun t : E →+* ℂ => t.comp (algebraMap (𝓞 E) E)) hab
  · intro s
    simp only [embOf_eq_iff, RingHom.comp_assoc]
    exact F.cm.2 _

private theorem vec_bas (C : LatEmb F) (k : Fin (2 * g)) : C.bas k = C.vec (C.lam k) := by
  funext τ i
  exact C.bas_eq k τ i

private theorem per_vec (C : LatEmb F) (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  let v : Λ →+ (Ψ → Fin (j + j') → ℂ) :=
    { toFun := C.vec
      map_zero' := by funext τ i; simp [LatEmb.vec]
      map_add' := fun a b => by funext τ i; simp [LatEmb.vec] }
  have key : ((C.perExt R).toAddMonoidHom.comp v).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    change C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [← vec_bas, LatEmb.perExt, Module.Basis.constr_basis]
  exact LinearMap.congr_fun key x

private theorem per_act (C : LatEmb F) (R : RiemLat E g Λ) (a : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (fun τ => F.σ τ a • y τ) = R.B a (C.perExt R y) := by
  let D : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) :=
    { toFun := fun y τ => F.σ τ a • y τ
      map_add' := fun y y' => by funext τ; simp
      map_smul' := fun r y => by funext τ; simp [smul_comm r] }
  have key : (C.perExt R).comp D = ((R.B a).restrictScalars ℝ).comp (C.perExt R) := by
    refine C.bas.ext fun k => ?_
    change C.perExt R (fun τ => F.σ τ a • C.bas k τ) = R.B a (C.perExt R (C.bas k))
    rw [vec_bas, per_vec, ← R.act, ← per_vec C]
    congr 1
    funext τ i
    simp [LatEmb.vec, C.e_smul, embOf_coe]
  exact LinearMap.congr_fun key y

private theorem sesq_emb (C : LatEmb F) (τ : Ψ) (x y : Λ) :
    embOf (F.σ τ) (C.h.toSesq (C.e y) (C.e x)) = star (C.vec y τ) ⬝ᵥ (C.gr τ *ᵥ C.vec x τ) := by
  rw [sesq_eq_sum C.h.toSesq (Pi.basisFun E (Fin (j + j')))]
  simp only [map_sum, map_mul, embedding_conj, Pi.basisFun_repr, dotProduct, mulVec, Finset.mul_sum,
    LatEmb.gr, LatEmb.vec, Matrix.map_apply, Pi.star_apply, mul_assoc]
  rfl

private theorem per_im (C : LatEmb F) (R : RiemLat E g Λ) (hR : R.form = F.form)
    (y y' : Ψ → Fin (j + j') → ℂ) :
    (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y' := by
  let b₁ : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y y' => (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im)
      (fun a b c => by simp [add_dotProduct])
      (fun r a c => by simp [smul_dotProduct])
      (fun a b c => by simp [mulVec_add, dotProduct_add])
      (fun r a c => by simp [star_smul, mulVec_smul, dotProduct_smul])
  let b₂ : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y y' => C.Fm y y')
      (fun a b c => by
        simp only [LatEmb.Fm, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re,
          Finset.sum_add_distrib])
      (fun r a c => by
        simp only [LatEmb.Fm, Pi.smul_apply, mulVec_smul, dotProduct_smul, mul_smul_comm, Complex.smul_re,
          Finset.smul_sum])
      (fun a b c => by
        simp only [LatEmb.Fm, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re,
          Finset.sum_add_distrib])
      (fun r a c => by
        simp only [LatEmb.Fm, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, mul_smul_comm,
          Complex.smul_re, Finset.smul_sum])
  have key : b₁ = b₂ := by
    refine LinearMap.ext_basis C.bas C.bas fun k l => ?_
    change (C.perExt R (C.bas k) ⬝ᵥ R.Hm *ᵥ star (C.perExt R (C.bas l))).im = C.Fm (C.bas k) (C.bas l)
    rw [vec_bas, vec_bas, per_vec, per_vec, R.im, hR]
    have h1 := congrArg (fun q : ℚ => (q : ℝ)) (C.form_eq (C.lam k) (C.lam l))
    simp only [Rat.cast_intCast] at h1
    rw [h1, trace_sum F]
    simp only [LatEmb.Fm, map_mul, sesq_emb]
  exact LinearMap.congr_fun₂ key y y'

private theorem gr_herm (C : LatEmb F) (τ : Ψ) : (C.gr τ).IsHermitian := by
  have h := isHermitianFor_gram C.h (Pi.basisFun E (Fin (j + j')))
  ext a b
  have h1 := congrArg (embOf (F.σ τ)) (congrFun (congrFun h a) b)
  simp only [transpose_apply, Matrix.map_apply] at h1
  simp only [conjTranspose_apply, LatEmb.gr, Matrix.map_apply]
  rw [← h1]
  exact (embedding_conj (embOf (F.σ τ)) _).symm

private theorem sgr_herm (C : LatEmb F) (τ : Ψ) : (C.sgr τ).IsHermitian := by
  unfold LatEmb.sgr Matrix.IsHermitian
  rw [conjTranspose_smul, (gr_herm C τ).eq]
  simp

private theorem sgr_unit (C : LatEmb F) (τ : Ψ) : IsUnit (C.sgr τ).det := by
  have h := (isUnit_det_gram C.h (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))
  rw [RingHom.map_det] at h
  have he : C.eps τ ≠ 0 := by
    intro h0
    have := C.eps_sq τ
    rw [h0] at this
    norm_num at this
  rw [LatEmb.sgr, det_smul]
  exact (IsUnit.mk0 _ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 he))).mul h

open Classical in
private theorem per_single (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ) (a : 𝓞 E) (y : Fin (j + j') → ℂ) :
    R.B a (C.perExt R (Pi.single τ y)) =
      (F.σ τ a).re • C.perExt R (Pi.single τ y) +
        (F.σ τ a).im • C.perExt R (Pi.single τ (Complex.I • y)) := by
  rw [← per_act, ← map_smul, ← map_smul, ← map_add]
  congr 1
  funext τ'
  by_cases h : τ' = τ
  · subst h
    funext i
    simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im (F.σ τ' a)]
    ring
  · simp [Pi.single_eq_of_ne h]

end UpperTheory.Reformulated.B.Gwb8

open UpperTheory.Reformulated.B.Gwb8 Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict in
theorem UpperTheory.Reformulated.B.Gwb8.exists_adapted_at :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {Ψ : Type}
      [inst_3 : Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [inst_4 : AddCommGroup Λ]
      [inst_5 : _root_.Module (NumberField.RingOfIntegers E) Λ] {F : GlobalTheory.CompanionTheory.Ar.Cusp.UnivFam E Ψ j j' n g Λ}
      (C : GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmb F) (R : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ),
      R.form = F.form →
        R.HasSig F.σ j j' →
          ∀ (τ : Ψ),
            ∃ (A : Matrix (Fin (j + j')) (GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Sg j j') ℂ),
              A.conjTranspose * C.sgr τ * A = GlobalTheory.CompanionTheory.Ar.Cusp.Dict.sgI j j' ∧
                (∀ (v : Fin j → ℂ), C.pPart R τ (A.mulVec (Sum.elim v (0 : Fin j' → ℂ))) = (0 : Fin g → ℂ)) ∧
                  ∀ (v : Fin j' → ℂ), C.pBar R τ (A.mulVec (Sum.elim (0 : Fin j → ℂ) v)) = (0 : Fin g → ℂ) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hR hs τ
  classical
  let p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (C.perExt R).comp (LinearMap.single ℝ (fun _ : Ψ => Fin (j + j') → ℂ) τ)
  have hp : ∀ y, p y = C.perExt R (Pi.single τ y) := fun _ => rfl
  have hB : ∀ a y, R.B a (p y) = ((F.σ τ a).re : ℂ) • p y + ((F.σ τ a).im : ℂ) • p (Complex.I • y) :=
    fun a y => per_single C R τ a y
  have hI : ∀ y : Fin (j + j') → ℂ, p (Complex.I • Complex.I • y) = -p y := fun y => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  obtain ⟨K, K', h1, h2, h3, h4, h5, h6, h7⟩ := UpperTheory.hermitian_positive_symplectic p R.Hm (C.sgr τ) C.c
    (eigSp R.B (F.σ τ)) (eigSp R.B ((starRingEnd ℂ).comp (F.σ τ))) R.pos (sgr_unit C τ) C.c_pos
    (fun y y' => by
      rw [hp, hp, per_im C R hR, LatEmb.Fm, Finset.sum_eq_single τ]
      · simp only [Pi.single_eq_same, C.xi_eq, LatEmb.sgr, smul_mulVec, dotProduct_smul, smul_eq_mul,
          Complex.ofReal_mul, mul_assoc]
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp)
    (hs τ).1 (hs τ).2
    (fun y => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, map_smul, hB, hI]
      intro a
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul]
      have e := Complex.re_add_im (F.σ τ a)
      linear_combination (p y i - Complex.I * p (Complex.I • y) i) * e +
        (((F.σ τ a).im : ℂ) * p (Complex.I • y) i) * Complex.I_mul_I)
    (fun y => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_add, map_smul, hB, hI]
      intro a
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul,
        RingHom.comp_apply]
      have e : ((F.σ τ a).re : ℂ) - ((F.σ τ a).im : ℂ) * Complex.I = starRingEnd ℂ (F.σ τ a) := by
        apply Complex.ext <;> simp
      linear_combination (p y i + Complex.I * p (Complex.I • y) i) * e +
        (((F.σ τ a).im : ℂ) * p (Complex.I • y) i) * Complex.I_mul_I)
  obtain ⟨A, hA, hK, hK'⟩ := UpperTheory.signature_block_diagonal (C.sgr τ) K K' (sgr_herm C τ) h1 h2 h5 h6 h7
  refine ⟨A, hA, fun v => ?_, fun v => ?_⟩
  · have := h3 _ (hK v)
    rw [hp, hp] at this
    rw [LatEmb.pPart]
    convert smul_zero (1 / 2 : ℂ)
  · have := h4 _ (hK' v)
    rw [hp, hp] at this
    rw [LatEmb.pBar]
    convert smul_zero (1 / 2 : ℂ)
