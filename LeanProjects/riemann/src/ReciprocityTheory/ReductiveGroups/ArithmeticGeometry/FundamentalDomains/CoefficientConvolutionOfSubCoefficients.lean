import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourMul

namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hline {r : ℕ} (X : Data E r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) : (Fin (Fintype.card X.Ψ) → ℂ) → ℂ :=
  fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)

def SubCoeffSt : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom, ∀ (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ),
      (∀ j, ω j ∈ X.periods la) → LinearIndependent ℝ ω →
      ∀ (k : Fin (Fintype.card X.Ψ) → ℤ) (ν : X.Ψ → ℝ), (∀ j, (k j : ℝ) = 2 * ∑ τ, ν τ * ω j τ) →
        fourCoeff (hline X P ξ x ω) 0 k = X.fj la ξ ν P x

variable {r : ℕ} (X : Data E r)

def bas1 (la : Wt X.Ψ r) : Module.Basis (Fin (Fintype.card X.Ψ)) ℤ (perL X la) :=
  Module.finBasisOfFinrankEq ℤ (perL X la) (perL_rank X la)

def om1 (la : Wt X.Ψ r) : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ := fun j => ((bas1 X la j : perL X la) : X.Ψ → ℝ)

theorem basicPeriod_mem (la : Wt X.Ψ r) (j : Fin (Fintype.card X.Ψ)) : om1 X la j ∈ X.periods la := by
  first
    | exact (bas1 X la j).2
    | exact AddSubgroup.mem_toIntSubmodule.mp (bas1 X la j).2

theorem basicPeriod_linearIndependent (la : Wt X.Ψ r) : LinearIndependent ℝ (om1 X la) := by
  have := (Module.Basis.ofZLatticeBasis ℝ (perL X la) (bas1 X la)).linearIndependent
  have h : ∀ j, (Module.Basis.ofZLatticeBasis ℝ (perL X la) (bas1 X la)) j = om1 X la j := fun j => by
    rw [Module.Basis.ofZLatticeBasis_apply]; rfl
  exact (funext h : _ = om1 X la) ▸ this

theorem scale_mem (la la2 : Wt X.Ψ r) (K K2 : ℕ) (hK : X.chiOrd la * K = X.chiOrd la2 * K2)
    {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) : (K : ℝ) • p ∈ X.periods la2 := by
  have hK' : (X.chiOrd la : ℝ) * K = X.chiOrd la2 * K2 := by exact_mod_cast hK
  simp only [Nat.cast_smul_eq_nsmul]
  unfold Data.periods at hp
  refine AddSubgroup.closure_induction (fun q hq => ?_) ?_ (fun q q' _ _ h1 h2 => ?_)
    (fun q _ h => ?_) hp
  · obtain ⟨a, hca, hia, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    refine ⟨(K2 : E) * a, ?_, ?_, ?_⟩
    · simp only [cc] at hca ⊢
      rw [map_mul, map_natCast, hca]
    · have h2 : IsIntegral ℤ (K2 : E) := by
        simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (K2 : ℤ)))
      exact h2.mul hia
    · funext τ
      simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Nat.cast_mul,
        Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      linear_combination ((X.m : ℝ) * (τ.1 a).re) * hK'
  · rw [smul_zero]
    exact AddSubgroup.zero_mem _
  · rw [smul_add]
    exact AddSubgroup.add_mem _ h1 h2
  · rw [smul_neg]
    exact AddSubgroup.neg_mem _ h

def omc (la la' : Wt X.Ψ r) : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ :=
  fun j => ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) • om1 X la j

theorem omc_li (la la' : Wt X.Ψ r) : LinearIndependent ℝ (omc X la la') := by
  have hC : ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) ≠ 0 := by
    have h1 : 0 < X.chiOrd la' := (X.χ_fin la').choose_spec.1
    have h2 : 0 < X.chiOrd (la + la') := (X.χ_fin (la + la')).choose_spec.1
    have h3 : 0 < X.chiOrd la' * X.chiOrd (la + la') := Nat.mul_pos h1 h2
    exact_mod_cast h3.ne'
  have h := (basicPeriod_linearIndependent X la).units_smul (fun _ => Units.mk0 _ hC)
  convert h using 1
  funext j
  first
    | rfl
    | simp [omc, Units.smul_def]

theorem scaledPeriod_mem_left (la la' : Wt X.Ψ r) (j : Fin (Fintype.card X.Ψ)) : omc X la la' j ∈ X.periods la := by
  show ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) • om1 X la j ∈ X.periods la
  simp only [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ (basicPeriod_mem X la j) _

theorem scaledPeriod_mem_right (la la' : Wt X.Ψ r) (j : Fin (Fintype.card X.Ψ)) : omc X la la' j ∈ X.periods la' := by
  show ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) • om1 X la j ∈ X.periods la'
  exact scale_mem X la la' _ (X.chiOrd la * X.chiOrd (la + la')) (by ring) (basicPeriod_mem X la j)

theorem scaledPeriod_mem_sum (la la' : Wt X.Ψ r) (j : Fin (Fintype.card X.Ψ)) :
    omc X la la' j ∈ X.periods (la + la') := by
  show ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) • om1 X la j ∈ X.periods (la + la')
  exact scale_mem X la (la + la') _ (X.chiOrd la * X.chiOrd la') (by ring) (basicPeriod_mem X la j)

theorem fj_eq_zero_of_not_freq (la : Wt X.Ψ r) (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) (h : ¬ ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) :
    X.fj la ξ ν P x = 0 := by
  rw [Data.fj, if_neg h]

private lemma diag_ne_lemma {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    b τ i i ≠ 0 := by
  obtain ⟨hdet, htri⟩ := hb τ
  have ht : (mat b τ).BlockTriangular id := fun a c h => htri a c h
  rw [Matrix.det_of_upperTriangular ht] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem sec_mul {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la' Q) :
    X.IsSec (la + la') (P * Q) := by
  obtain ⟨hPd, hPb, hPg⟩ := hP
  obtain ⟨hQd, hQb, hQg⟩ := hQ
  refine ⟨hPd.mul hQd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hbc : bchar (la + la') b = bchar la b * bchar la' b := by
      simp only [bchar, Pi.add_apply, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
      exact zpow_add₀ (diag_ne_lemma X hb τ i) _ _
    simp only [Pi.mul_apply, hPb x hx b hb, hQb x hx b hb, hbc]
    ring
  · simp only [Pi.mul_apply, hPg γ hγ x hx, hQg γ hγ x hx, X.χ_add la la' γ hγ]
    ring

section line

variable {X}

theorem exists_e (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) (hωi : LinearIndependent ℝ ω) :
    ∃ e : (Fin (Fintype.card X.Ψ) → ℤ) → (X.Ψ → ℝ), (∀ k j, 2 * ∑ τ, e k τ * ω j τ = k j) ∧
      Function.Injective e ∧ (∀ k k', e (k - k') = e k - e k') ∧
      ∀ ν : X.Ψ → ℝ, (∀ j, ∃ n : ℤ, 2 * ∑ τ, ν τ * ω j τ = n) → ∃ k, e k = ν := by
  classical
  let W : Matrix (Fin (Fintype.card X.Ψ)) X.Ψ ℝ := Matrix.of fun j τ => 2 * ω j τ
  have hA : ∀ ν j, (W.mulVecLin ν) j = 2 * ∑ τ, ν τ * ω j τ := by
    intro ν j
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hspan : Submodule.span ℝ (Set.range ω) = ⊤ := by
    rcases isEmpty_or_nonempty (Fin (Fintype.card X.Ψ)) with hE | hE
    · have h0 : Fintype.card X.Ψ = 0 := Nat.eq_zero_of_not_pos (fun h => hE.false ⟨0, h⟩)
      have hΨ : IsEmpty X.Ψ := Fintype.card_eq_zero_iff.mp h0
      exact Subsingleton.elim _ _
    · exact hωi.span_eq_top_of_card_eq_finrank (by simp)
  have hinj : Function.Injective W.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ν hν
    have h0 : ∀ j, ∑ τ, ν τ * ω j τ = 0 := by
      intro j
      have h1 := congrFun hν j
      rw [hA] at h1
      simpa using h1
    let φ : (X.Ψ → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun w => ∑ τ, ν τ * w τ
        map_add' := by
          intro a b
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          ring }
    have hle : Submodule.span ℝ (Set.range ω) ≤ LinearMap.ker φ :=
      Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact LinearMap.mem_ker.mpr (h0 j))
    have hmem : ν ∈ Submodule.span ℝ (Set.range ω) := by
      rw [hspan]
      exact Submodule.mem_top
    have hsq : ∑ τ, ν τ * ν τ = 0 := LinearMap.mem_ker.mp (hle hmem)
    funext τ
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => mul_self_nonneg (ν τ))).mp hsq τ
      (Finset.mem_univ τ)
    exact mul_self_eq_zero.mp h2
  have hsurj : Function.Surjective W.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  let L := LinearEquiv.ofBijective W.mulVecLin ⟨hinj, hsurj⟩
  have hL : ∀ ν j, L ν j = 2 * ∑ τ, ν τ * ω j τ := fun ν j => hA ν j
  refine ⟨fun k => L.symm (fun j => (k j : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro k j
    show 2 * ∑ τ, L.symm (fun j => (k j : ℝ)) τ * ω j τ = k j
    rw [← hL, L.apply_symm_apply]
  · intro k k' h
    have h' : L.symm (fun j => (k j : ℝ)) = L.symm (fun j => (k' j : ℝ)) := h
    have h1 := L.symm.injective h'
    funext j
    exact_mod_cast congrFun h1 j
  · intro k k'
    show L.symm (fun j => (((k - k') j : ℤ) : ℝ)) =
      L.symm (fun j => (k j : ℝ)) - L.symm (fun j => (k' j : ℝ))
    rw [show (fun j => (((k - k') j : ℤ) : ℝ)) = (fun j => (k j : ℝ)) - (fun j => (k' j : ℝ)) by
      funext j
      simp]
    exact map_sub L.symm _ _
  · intro ν hν
    choose n hn using hν
    refine ⟨n, ?_⟩
    show L.symm (fun j => (n j : ℝ)) = ν
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [hL]
    exact (hn j).symm

def Om (ξ : Fin r → E) (x : Frame X.Ψ r) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    Set (Fin (Fintype.card X.Ψ) → ℝ) :=
  {b | (fun τ => ∑ j, b j * ω j τ) ∈ admissibleImaginary X ξ x}

theorem Om_open (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    IsOpen (Om ξ x ω) := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun b : Fin (Fintype.card X.Ψ) → ℝ =>
      psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ) +
        ((2 * X.c τ * ∑ j, b j * ω j τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re := by
    intro τ i
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    unfold lminor
    refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
    first
      | fun_prop
      | exact continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul
          (continuous_finset_sum _ fun j _ => (continuous_apply j).mul continuous_const))).smul
          continuous_const)
  have hO : Om ξ x ω = ⋂ (τ : X.Ψ), ⋂ (i : Fin (r + 1)), {b | 0 < psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ) +
        ((2 * X.c τ * ∑ j, b j * ω j τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re} := by
    ext b
    simp only [Om, admissibleImaginary, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hO]
  exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (hc τ i)

private lemma hsubl_lemma_21 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (u u' w : Fin n → ℂ) : hermC σ G (u - u') w = hermC σ G u w - hermC σ G u' w := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hsmull_lemma_22 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (k : ℂ) (u w : Fin n → ℂ) : hermC σ G (k • u) w = k * hermC σ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma hsubr_lemma_23 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (v w w' : Fin n → ℂ) : hermC σ G v (w - w') = hermC σ G v w - hermC σ G v w' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

private lemma hsmulr_lemma_24 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (k : ℂ) (v w : Fin n → ℂ) : hermC σ G v (k • w) = conj k * hermC σ G v w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma hconj_lemma_25 (τ : X.Ψ) (u v : Fin r → ℂ) :
    conj (hermC τ.1 X.Gm u v) = hermC τ.1 X.Gm v u := by
  have hG : ∀ a b, conj (τ.1 (X.Gm a b)) = τ.1 (X.Gm b a) := by
    intro a b
    rw [← X.Gm_herm a b]
    first
      | simp [cc, IsCMField.complexEmbedding_complexConj]
      | simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  simp only [hermC, map_sum, map_mul, Complex.conj_conj, hG]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma huu_lemma_26 {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
  have h : τ.1 (herm X.Gm ξ ξ) = hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) := by
    first
      | simp [herm, hermC, Data.emb, cc, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [← h, hξ, map_zero]

private lemma colmul_lemma_27 (A M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (A * M) a = A *ᵥ col M a := by
  funext k
  simp only [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma flowmv_lemma_28 (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (p : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ p =
      p - (I * (X.c τ : ℂ) * s * hermC τ.1 X.Gm p (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.flowMat, Matrix.of_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, Data.emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private lemma gramflow_lemma_29 {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  ext a b
  have hu := huu_lemma_26 hξ τ
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1,
    Matrix.vecMulVec_apply, hv]
  rw [colmul_lemma_27, colmul_lemma_27, flowmv_lemma_28, flowmv_lemma_28]
  simp only [hsubl_lemma_21, hsubr_lemma_23, hsmull_lemma_22, hsmulr_lemma_24, hu]
  rw [← hconj_lemma_25 τ (col M b) (Data.emb τ.1 ξ)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
  have hs : (starRingEnd ℂ) s = s - 2 * I * (s.im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [hs]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma flowdet_lemma_210 {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det ≠ 0 := by
  have hu := huu_lemma_26 hξ τ
  have key : ∀ p, (X.flowMat ξ τ s * X.flowMat ξ τ (-s)) *ᵥ p = p := by
    intro p
    rw [← Matrix.mulVec_mulVec, flowmv_lemma_28, flowmv_lemma_28]
    simp only [hsubl_lemma_21, hsmull_lemma_22, hu, mul_zero, sub_zero]
    funext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hinv : X.flowMat ξ τ s * X.flowMat ξ τ (-s) = 1 := by
    ext a b
    have h1 := congrFun (key (Pi.single b 1)) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h1
  have h2 := congrArg Matrix.det hinv
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact left_ne_zero_of_mul_eq_one h2

theorem flow_mem_of_tube {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) {s : Fin (Fintype.card X.Ψ) → ℂ}
    (hs : s ∈ tube (Fintype.card X.Ψ) (Om ξ x ω)) :
    X.flow ξ (fun τ => ∑ j, s j * (ω j τ : ℂ)) x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (X.flowMat ξ τ (∑ j, s j * (ω j τ : ℂ)) * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (flowdet_lemma_210 hξ τ _) (hx τ).1
  · show 0 < psgn X.p0 i *
      (lminor (gram τ.1 X.Gm (X.flowMat ξ τ (∑ j, s j * (ω j τ : ℂ)) * mat x τ)) i).re
    have h1 : (fun τ => ∑ j, (s j).im * ω j τ) ∈ admissibleImaginary X ξ x := hs
    have h2 := h1 τ i
    have him : (∑ j, s j * (ω j τ : ℂ)).im = ∑ j, (s j).im * ω j τ := by
      simp [Complex.im_sum]
    rw [gramflow_lemma_29 hξ τ, him]
    exact h2

theorem zero_mem_Om {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) : (0 : Fin (Fintype.card X.Ψ) → ℝ) ∈ Om ξ x ω := by
  show (fun τ => ∑ j, (0 : Fin (Fintype.card X.Ψ) → ℝ) j * ω j τ) ∈ admissibleImaginary X ξ x
  simp only [admissibleImaginary, Set.mem_setOf_eq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero,
    Complex.ofReal_zero, zero_smul, add_zero]
  intro τ i
  exact (hx τ).2 i

theorem hline_diff {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube (Fintype.card X.Ψ) (Om ξ x ω)) := by
  have hF : Differentiable ℂ (fun t : Fin (Fintype.card X.Ψ) → ℂ =>
      X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x) := by
    rw [differentiable_pi]
    intro τ
    rw [differentiable_pi]
    intro a
    rw [differentiable_pi]
    intro b
    simp only [Data.flow, Data.flowMat, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hP.comp hF.differentiableOn (fun t ht => flow_mem_of_tube hξ hx ω ht)

theorem hline_per {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ)
    (hωp : ∀ j, ω j ∈ X.periods la) :
    ∀ s ∈ tube (Fintype.card X.Ψ) (Om ξ x ω), ∀ n : Fin (Fintype.card X.Ψ) → ℤ,
      hline X P ξ x ω (s + fun k => (n k : ℂ)) = hline X P ξ x ω s := by
  intro s hs n
  set p : X.Ψ → ℝ := ∑ j, (n j : ℤ) • ω j with hpdef
  have hp : p ∈ X.periods la :=
    AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hωp j) _
  have hσ : (fun τ => ∑ j, (s + fun k => (n k : ℂ)) j * (ω j τ : ℂ)) =
      cR X p + fun τ => ∑ j, s j * (ω j τ : ℂ) := by
    funext τ
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, cR, hpdef, Finset.sum_apply,
      Pi.smul_apply]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  unfold hline
  rw [hσ, ← flow_flow X hξ.2.1]
  exact sec_periodic X la P hP hξ.1 hξ.2.1 hp _ (flow_mem_of_tube hξ.2.1 hx ω hs)

end line

theorem coefficientConvolution_of_subCoefficients (hsub : SubCoeffSt (E := E)) : CoefficientConvolution (E := E) := by
  intro r X la la' P Q hP hQ _ _ ξ hξ x hx ν
  set ω := omc X la la' with hωdef
  have hωi := omc_li X la la'
  obtain ⟨e, he_k, he_inj, he_sub, he_surj⟩ := exists_e ω hωi
  have hPQ := sec_mul X hP hQ
  have cP : ∀ k, X.fj la ξ (e k) P x = fourCoeff (hline X P ξ x ω) 0 k := fun k =>
    (hsub r X la P hP ξ hξ x hx ω (scaledPeriod_mem_left X la la') hωi k (e k) (fun j => (he_k k j).symm)).symm
  have cQ : ∀ k, X.fj la' ξ (e k) Q x = fourCoeff (hline X Q ξ x ω) 0 k := fun k =>
    (hsub r X la' Q hQ ξ hξ x hx ω (scaledPeriod_mem_right X la la') hωi k (e k) (fun j => (he_k k j).symm)).symm
  have cPQ : ∀ k, X.fj (la + la') ξ (e k) (P * Q) x = fourCoeff (hline X (P * Q) ξ x ω) 0 k := fun k =>
    (hsub r X (la + la') (P * Q) hPQ ξ hξ x hx ω (scaledPeriod_mem_sum X la la') hωi k (e k)
      (fun j => (he_k k j).symm)).symm
  have z : ∀ (la0 : Wt X.Ψ r) (P0 : Frame X.Ψ r → ℂ), (∀ j, ω j ∈ X.periods la0) →
      ∀ ν' : X.Ψ → ℝ, ν' ∉ Set.range e → X.fj la0 ξ ν' P0 x = 0 := by
    intro la0 P0 hmem ν' hν'
    apply fj_eq_zero_of_not_freq
    intro hfreq
    apply hν'
    obtain ⟨k, hk⟩ := he_surj ν' (fun j => hfreq _ (hmem j))
    exact ⟨k, hk⟩
  have he_add : ∀ k k', e (k + k') = e k + e k' := fun k k' => by
    have := he_sub (k + k') k'
    rw [add_sub_cancel_right] at this
    rw [this]; abel
  by_cases hν : ν ∈ Set.range e
  · obtain ⟨k0, rfl⟩ := hν
    have hfm := four_mul' (Fintype.card X.Ψ) (Om ξ x ω) (hline X P ξ x ω) (hline X Q ξ x ω)
      (Om_open ξ hx ω) (hline_diff hP.1 hξ.2.1 hx ω) (hline_diff hQ.1 hξ.2.1 hx ω)
      (hline_per hP hξ hx ω (scaledPeriod_mem_left X la la')) (hline_per hQ hξ hx ω (scaledPeriod_mem_right X la la')) 0
      (zero_mem_Om hξ.2.1 hx ω) k0
    have hprod : hline X P ξ x ω * hline X Q ξ x ω = hline X (P * Q) ξ x ω := rfl
    rw [hprod, ← cPQ] at hfm
    rw [← he_inj.hasSum_iff (fun ν' hν' => by rw [z la P (scaledPeriod_mem_left X la la') ν' hν', zero_mul])]
    convert hfm using 1
    funext k'
    simp only [Function.comp_apply]
    rw [← he_sub, cP, cQ]
  · rw [z (la + la') (P * Q) (scaledPeriod_mem_sum X la la') ν hν]
    convert hasSum_zero with ν'
    by_cases h' : ν' ∈ Set.range e
    · obtain ⟨k', rfl⟩ := h'
      have : ν - e k' ∉ Set.range e := by
        rintro ⟨k'', hk''⟩
        apply hν
        refine ⟨k'' + k', ?_⟩
        rw [he_add, hk'']
        abel
      rw [z la' Q (scaledPeriod_mem_right X la la') _ this, mul_zero]
    · rw [z la P (scaledPeriod_mem_left X la la') _ h', zero_mul]

end

end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
