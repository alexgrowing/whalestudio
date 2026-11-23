import Formalism.LocalToGlobal.GlobalTheory.GL4.CfMemTwId

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

theorem emb_nonreal {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (φ : E →+* ℂ) : ∃ a : E, (φ a).im ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : NumberField.ComplexEmbedding.IsReal φ :=
    NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x => by
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (h x))
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk φ))
    (NumberField.InfinitePlace.isReal_mk_iff.mpr hr)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {K : Type} [Field K] [CharZero K] (s : K →+* ℂ)
    {F : Pol K ι n} (hF : F ∈ VV K lam) : MvPolynomial.map s F ∈ VV ℂ lam := by
  obtain ⟨Z, -⟩ := standard_basis_z ι n lam
  rw [← Z.span_F K] at hF
  rw [← Z.span_F ℂ]
  induction hF using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    rw [MvPolynomial.map_map, show s.comp (Int.castRingHom K) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
  | smul a p _ hp =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hp

theorem fockN_smul {σ : Type} (d : ℂ) (f : MvPolynomial σ ℂ) : fockN (d • f) = ‖d‖ ^ 2 * fockN f := by
  unfold fockN
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · rw [MvPolynomial.support_smul_eq hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, mul_pow, mul_assoc]

theorem nfAll_self_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p p = ((fockN p / extremalFockNormProduct lam : ℝ) : ℂ) := by
  exact nfL_self lam p

end SlopeTestRemainingChoices

section Nrm

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem maj_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) (y z : (D.sp.X 0).V) :
    majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) (CV.bc c τ z) = v.embedding (CV.rho τ ((D.sp.X 0).hT y z)) := by
  have := (columnHypotheses D u).tcE
  have hcm : ∀ (φ : D.host.E →+* ℂ) (a : D.host.E), φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1
  set φ : D.host.E →+* ℂ := v.embedding.comp (CV.rho τ) with hφ
  obtain ⟨s1, s2, s3, s4⟩ := isSesq_maj (CV.Q c τ).b (CV.Q c τ).X v
  beta_reduce at s1 s2 s3 s4
  refine sesq_ext (F := fun y z => majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) (CV.bc c τ z))
    (G := fun y z => φ ((D.sp.X 0).hT y z)) (σ := φ) (emb_nonreal φ) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ y z
  · intro x x' y
    show majAt _ _ v (CV.bc c τ (x + x')) _ = _
    rw [map_add, s1]
  · intro x y y'
    show majAt _ _ v _ (CV.bc c τ (y + y')) = _
    rw [map_add, s2]
  · intro a x y
    show majAt _ _ v (CV.bc c τ (a • x)) _ = _
    rw [CV.bc_smul, s3]
    rfl
  · intro a x y
    show majAt _ _ v _ (CV.bc c τ (a • y)) = _
    rw [CV.bc_smul, s4]
    rfl
  · intro x x' y
    show φ ((D.sp.X 0).hT (x + x') y) = φ ((D.sp.X 0).hT x y) + φ ((D.sp.X 0).hT x' y)
    rw [map_add, LinearMap.add_apply, map_add]
  · intro x y y'
    show φ ((D.sp.X 0).hT x (y + y')) = φ ((D.sp.X 0).hT x y) + φ ((D.sp.X 0).hT x y')
    rw [map_add, map_add]
  · intro a x y
    show φ ((D.sp.X 0).hT (a • x) y) = starRingEnd ℂ (φ a) * φ ((D.sp.X 0).hT x y)
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, starRingEnd_apply, hcm]
  · intro a x y
    show φ ((D.sp.X 0).hT x (a • y)) = φ a * φ ((D.sp.X 0).hT x y)
    rw [map_smul, smul_eq_mul, map_mul]
  · intro x
    show majAt _ _ v (CV.bc c τ x) (CV.bc c τ x) = φ ((D.sp.X 0).hT x x)
    have hre := CV.bc_norm c τ v x
    have hreal : (φ ((D.sp.X 0).hT x x)).im = 0 := by
      have e : starRingEnd D.host.E ((D.sp.X 0).hT x x) = (D.sp.X 0).hT x x := (D.sp.X 0).herm.eq x x
      have e2 : starRingEnd ℂ (φ ((D.sp.X 0).hT x x)) = φ ((D.sp.X 0).hT x x) := by
        rw [← hcm, ← starRingEnd_apply, e]
      exact Complex.conj_eq_iff_im.1 e2
    apply Complex.ext
    · exact hre
    · rw [majAt_self, Complex.ofReal_im]
      exact hreal.symm

theorem riesz_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) (y : (D.sp.X 0).V)
    (q : (CV.Q c τ).V) : v.embedding (bcFun CV c τ y q) = majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) q := by
  obtain ⟨s1, s2, s3, s4⟩ := isSesq_maj (CV.Q c τ).b (CV.Q c τ).X v
  beta_reduce at s1 s2 s3 s4
  have hq : q ∈ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) :=
    span_bc_frame CV c τ Submodule.mem_top
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    rw [bcFun_bc, maj_bc]
  | zero =>
    rw [map_zero, map_zero]
    have := s2 (CV.bc c τ y) 0 0
    rw [add_zero] at this
    linear_combination this
  | add q q' _ _ h1 h2 => rw [map_add, map_add, s2, h1, h2]
  | smul a q _ h1 => rw [map_smul, smul_eq_mul, map_mul, s4, h1]

theorem gM_map (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) :
    (gM CV c y τ).map v.embedding =
      Matrix.of (fun a k => star (fcoord (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ (y a)) ((CV.eQ c τ).symm k))) *
        Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹ := by
  classical
  ext a j
  simp only [Matrix.map_apply, gM, Matrix.of_apply]
  rw [riesz_bc, Matrix.mul_apply]
  unfold majAt
  refine Fintype.sum_equiv (CV.eQ c τ) _ _ fun i => ?_
  simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  simp [fcoord, vecAt, Matrix.mulVec, dotProduct, Basis.repr_self, Finsupp.single_apply]

theorem invFr_coe (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ) =
      Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹ := rfl

theorem hsN_gM (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) :
    hsN (((gM CV c y τ).map v.embedding *
        (((invFr CV v c τ)⁻¹ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ) =
      ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re := by
  have hdet : IsUnit (Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹).det := by
    rw [← invFr_coe]
    exact Matrix.isUnits_det_units _
  rw [gM_map, Matrix.coe_units_inv, invFr_coe, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  unfold hsN
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← CV.bc_norm c τ v (y a), majAt_self, Complex.ofReal_re]
  unfold normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Fintype.sum_equiv (CV.eQ c τ).symm _ _ fun k => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply, norm_star]

theorem tcAt_mem_VV (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    tcAt CV v c x ∈ VV ℂ ((D.fm u).lam 0) := by
  unfold tcAt
  refine polyAction_mem_VV _ _ (map_mem_VV _ v.embedding ?_)
  rw [← coE_coe CV (hTV0 D u) x c]
  exact (coE CV (hTV0 D u) x c).2

theorem class_norm (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v
        (cfMap ((D.fm u).lam 0) (gG CV c y hli) (coE CV (hTV0 D u) x c)) ^ 2 ≤
      ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) *
          ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) *
        normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 := by
  set lam := (D.fm u).lam 0 with hlam
  set g := gG CV c y hli with hg
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) :=
    ((coE CV (hTV0 D u) x c : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  set P := tcAt CV v c x with hP
  set d : ℂ := detTwK lam (invFr CV v c)⁻¹ with hd
  set U : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding) *
      (((invFr CV v c τ)⁻¹ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ with hU
  set G := MvPolynomial.map v.embedding (trAct g F) with hGdef
  set Gp := ∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW (lam τ) with hGp
  have h1 : normAt (Pi.basisFun D.what₂.LL (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g (coE CV (hTV0 D u) x c)) ^ 2 ≤
      fockN G / extremalFockNormProduct lam := by
    rw [monH_norm]
    have e1 : ∑ m, monW lam m * ‖v.embedding (cfMap lam g (coE CV (hTV0 D u) x c) m)‖ ^ 2 =
        (∑ m : MonI lam, ‖coeff m.1 G‖ ^ 2 * (mfact m.1 : ℝ)) / extremalFockNormProduct lam := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hGdef, coeff_map, cfMap_apply, monW]
      ring
    have e2 : ∑ m : MonI lam, ‖coeff m.1 G‖ ^ 2 * (mfact m.1 : ℝ) ≤ fockN G := by
      have := fockN_sum_le G ((Finset.univ : Finset (MonI lam)).map ⟨fun m : MonI lam => m.1, fun a b h => Subtype.ext h⟩)
      rwa [Finset.sum_map] at this
    rw [e1]
    exact div_le_div_of_nonneg_right e2 (extR_pos lam).le
  have hVt : ∀ τ, (((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ * U τ =
      (((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ).map v.embedding := by
    intro τ
    simp only [hU]
    rw [← Matrix.transpose_mul, Matrix.coe_units_inv, Matrix.nonsing_inv_mul_cancel_right _ _ (Matrix.isUnits_det_units _),
      Matrix.transpose_map]
  have eP : P = detTwK lam (invFr CV v c) • Formalism.GradedWeylDivisibility.blockAct ℂ
      (fun τ => ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)ᵀ)
      (MvPolynomial.map v.embedding F) := by
    simp only [hP, tcAt, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct]
    rfl
  have ecomp : Formalism.GradedWeylDivisibility.blockAct ℂ U (Formalism.GradedWeylDivisibility.blockAct ℂ
      (fun τ => ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)ᵀ)
      (MvPolynomial.map v.embedding F)) = G := by
    rw [← AlgHom.comp_apply, blockAct_comp]
    simp only [hVt]
    rw [hGdef]
    unfold trAct
    rw [map_blockAct]
  have hd1 : d * detTwK lam (invFr CV v c) = 1 := by rw [hd, ← detTwK_mul, inv_mul_cancel, detTwK_one]
  have h2 : G = d • Formalism.GradedWeylDivisibility.blockAct ℂ U P := by
    rw [eP, map_smul, ecomp, smul_smul, hd1, one_smul]
  have hPV : P ∈ VV ℂ lam := tcAt_mem_VV CV v c x
  have h3 : fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U P) ≤ (∏ τ, hsN (U τ) ^ dW (lam τ)) * fockN P := by
    refine fockSubNorm D.what₂.Tau (D.R.N 0) U (fun τ => dW (lam τ)) P fun m hm τ => ?_
    have hm' := coefficient_space_support ℂ lam hPV m hm
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => hm' τ s
  have h4 : ∀ τ, hsN (U τ) = ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re := fun τ =>
    hsN_gM CV c y τ v
  have h5 : fockN P / extremalFockNormProduct lam ≤ normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 := by
    have e := majorant_lattice_eq_sum CV v x x
    rw [majAt_self] at e
    have e2 : normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 = ∑ c', fockN (tcAt CV v c' x) / extremalFockNormProduct lam := by
      have := congrArg Complex.re e
      rw [Complex.ofReal_re, Complex.re_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [nfAll_self_eq, Complex.ofReal_re]
    rw [e2]
    exact Finset.single_le_sum (f := fun c' => fockN (tcAt CV v c' x) / extremalFockNormProduct lam)
      (fun c' _ => div_nonneg (fockN_nonneg _) (extR_pos _).le) (Finset.mem_univ c)
  have hGn : fockN G ≤ ‖d‖ ^ 2 * (Gp * fockN P) := by
    rw [h2, fockN_smul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have := h3
    simp only [h4] at this
    exact this
  have hprod : 0 ≤ Gp :=
    Finset.prod_nonneg fun τ _ => pow_nonneg (by rw [← h4 τ]; exact hsN_nonneg _) _
  calc normAt (Pi.basisFun D.what₂.LL (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g (coE CV (hTV0 D u) x c)) ^ 2
      ≤ fockN G / extremalFockNormProduct lam := h1
    _ ≤ ‖d‖ ^ 2 * (Gp * fockN P) / extremalFockNormProduct lam := div_le_div_of_nonneg_right hGn (extR_pos lam).le
    _ = (Gp * ‖d‖ ^ 2) * (fockN P / extremalFockNormProduct lam) := by ring
    _ ≤ (Gp * ‖d‖ ^ 2) * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hprod (sq_nonneg _))

end Nrm

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
