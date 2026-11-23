import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FinKey

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FreeQuotientRank MvPolynomial

namespace FinKey

theorem eval_bind₁' {σ τ R : Type} [CommRing R] (Y : τ → R) (g : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) : eval Y (bind₁ g p) = eval (fun x => eval Y (g x)) p := by
  induction p using MvPolynomial.induction_on <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def frameLin {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (x : ArcLt Dw) : MvPolynomial (ArcLt Dw) K :=
  ∑ l : Fin (Dw.mult x.1), X ⟨x.1, x.2.1, l⟩ * C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)

theorem eval_frameLin {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (Y : ArcLt Dw → K) (x : ArcLt Dw) :
    eval Y (frameLin Bm lam x) = frameSub Bm lam Y x := by
  simp only [frameLin, frameSub, map_sum, map_mul, eval_X, eval_C, Finset.sum_mul, mul_assoc]

theorem frameLin_homog {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (x : ArcLt Dw) : (frameLin Bm lam x).IsHomogeneous 1 := by
  unfold frameLin
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun l _ => ?_
  have h := (isHomogeneous_X K (⟨x.1, x.2.1, l⟩ : ArcLt Dw)).mul
    (isHomogeneous_C (ArcLt Dw) (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹))
  rwa [add_zero] at h

theorem subA_sum' {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (τ : E →+* ℂ) (i l : Fin (Dw.mult τ)) :
    (∑ z : ArcLt Dw, C (subA A ⟨τ, i, l⟩ z) * (X z : MvPolynomial (ArcLt Dw) K)) =
      ∑ k : Fin (Dw.mult τ), C (A τ k l) * X ⟨τ, i, k⟩ := subA_sum A ⟨τ, i, l⟩

theorem bind_subA_frameLin {K : Type} [Field K]
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (hAB : ∀ τ, A τ * Bm τ = 1)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (x : ArcLt Dw) :
    bind₁ (fun y => ∑ z : ArcLt Dw, C (subA A y z) * (X z : MvPolynomial (ArcLt Dw) K)) (frameLin Bm lam x) =
      C ((lam x.1 x.2.2)⁻¹) * X x := by
  obtain ⟨τ, i, j⟩ := x
  have key : ∀ k : Fin (Dw.mult τ), ∑ l, A τ k l * Bm τ l j = if k = j then 1 else 0 := by
    intro k
    have h := congrFun (congrFun (hAB τ) k) j
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [frameLin, map_sum, map_mul, bind₁_X_right, bind₁_C_right, subA_sum, Finset.sum_mul]
  calc _ = ∑ k : Fin (Dw.mult τ), C ((∑ l, A τ k l * Bm τ l j) * (lam τ j)⁻¹) *
          (X ⟨τ, i, k⟩ : MvPolynomial (ArcLt Dw) K) := by
        show ∑ l : Fin (Dw.mult τ), ∑ k : Fin (Dw.mult τ), C (A τ k l) *
          (X ⟨τ, i, k⟩ : MvPolynomial (ArcLt Dw) K) * (C (Bm τ l j) * C (lam τ j)⁻¹) = _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Finset.sum_mul, map_sum, map_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = C (lam τ j)⁻¹ * X ⟨τ, i, j⟩ := by
        rw [Finset.sum_eq_single j]
        · simp [key]
        · intro k _ hkj
          simp [key, hkj]
        · intro h
          exact absurd (Finset.mem_univ j) h

private theorem eval_map_detZ_lemma {K : Type} [CommRing K] (D : Datum H) (x : ArcLt D → K) :
    eval x (map (Int.castRingHom K) (detZ D)) =
      ∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (D.mult τ) => x ⟨τ, i, l⟩).det := by
  rw [detZ, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := RingHom.map_det ((eval x).comp (map (Int.castRingHom K)))
    (Matrix.of fun i l : Fin (D.mult τ) => (X (⟨τ, i, l⟩ : ArcLt D) : MvPolynomial (ArcLt D) ℤ))
  rw [RingHom.comp_apply] at h
  rw [h]
  congr 1
  ext i l
  simp

theorem exists_coeff_norm_one {K : Type} [NormedField K] [IsUltrametricDist K] (Dw : Datum H) :
    ∃ ν, ‖coeff ν (map (Int.castRingHom K) (detZ Dw))‖ = 1 := by
  by_contra hne
  push_neg at hne
  have hlt : ∀ ν, ‖coeff ν (map (Int.castRingHom K) (detZ Dw))‖ < 1 := fun ν =>
    lt_of_le_of_ne (by rw [coeff_map]; exact IsUltrametricDist.norm_intCast_le_one K _) (hne ν)
  have hev : eval (fun x : ArcLt Dw => if x.2.1 = x.2.2 then (1 : K) else 0)
      (map (Int.castRingHom K) (detZ Dw)) = 1 := by
    rw [eval_map_detZ_lemma]
    refine Finset.prod_eq_one fun τ _ => ?_
    refine (congrArg Matrix.det ?_).trans
      (Matrix.det_one : Matrix.det (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) = 1)
    ext i l
    simp [Matrix.one_apply]
  rw [MvPolynomial.eval_eq] at hev
  obtain ⟨ν, -, hν⟩ := IsUltrametricDist.exists_norm_finsetSum_le
    (map (Int.castRingHom K) (detZ Dw)).support
    (fun d => coeff d (map (Int.castRingHom K) (detZ Dw)) *
      ∏ i ∈ d.support, (if i.2.1 = i.2.2 then (1 : K) else 0) ^ d i)
  beta_reduce at hν
  rw [hev, norm_one, norm_mul] at hν
  have hpow : ∀ (y : K), ‖y‖ ≤ 1 → ∀ k : ℕ, ‖y ^ k‖ ≤ 1 := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, norm_mul]
      nlinarith [norm_nonneg (y ^ k), norm_nonneg y]
  have hp : ‖∏ i ∈ ν.support, (if i.2.1 = i.2.2 then (1 : K) else 0) ^ ν i‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hpow _ ?_ _
    split_ifs <;> simp
  linarith [hlt ν, mul_le_of_le_one_right
    (norm_nonneg (coeff ν (map (Int.castRingHom K) (detZ Dw)))) hp]

private theorem coeff_lcoeffPoly_lemma_2 {σ K₁ : Type} [Field K₁] (P : MvPolynomial σ (LaurentSeries K₁))
    (k : ℤ) (ν : σ →₀ ℕ) : coeff ν (lcoeffPoly P k) = (P.coeff ν).coeff k := by
  classical
  rw [lcoeffPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    simp [h]

private theorem coeff_bind_scale_lemma_3 {σ K : Type} [NormedField K] (s : σ → K) (Q : MvPolynomial σ K)
    (ν : σ →₀ ℕ) :
    coeff ν (bind₁ (fun x => C (s x) * X x) Q) = (ν.prod fun x e => s x ^ e) * coeff ν Q := by
  classical
  induction Q using MvPolynomial.induction_on'
  next u a =>
    rw [MvPolynomial.bind₁_monomial]
    have hprod : (∏ i ∈ u.support, (C (s i) * X i) ^ u i : MvPolynomial σ K) =
        monomial u (∏ i ∈ u.support, s i ^ u i) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [hprod, MvPolynomial.C_mul_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [Finsupp.prod, mul_comm]
    · rw [mul_zero]
  next p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

private theorem norm_subA_le_lemma_4 {K : Type} [NormedField K]
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (Cb : ℝ) (hC0 : 0 ≤ Cb)
    (hA : ∀ τ k l, ‖A τ k l‖ ≤ Cb) (y z : ArcLt Dw) : ‖subA A y z‖ ≤ Cb := by
  obtain ⟨σ, i, l⟩ := y
  obtain ⟨σ', i', l'⟩ := z
  simp only [subA]
  by_cases hσ : σ' = σ
  · subst hσ
    by_cases hi : i' = i
    · subst hi
      simpa using hA σ' l' l
    · simp [hi, hC0]
  · simp [hσ, hC0]

private theorem exists_lcoeffPoly_eq_zero_lemma_5 {σ K₁ : Type} [Field K₁]
    (P : MvPolynomial σ (LaurentSeries K₁)) :
    ∃ b : ℕ, ∀ k : ℤ, k < -(b : ℤ) → lcoeffPoly P k = 0 := by
  refine ⟨∑ μ' ∈ P.support, (-(P.coeff μ').order).toNat, fun k hk => ?_⟩
  rw [lcoeffPoly]
  refine Finset.sum_eq_zero fun μ' hμ' => ?_
  have hle : (-(P.coeff μ').order).toNat ≤ ∑ μ' ∈ P.support, (-(P.coeff μ').order).toNat :=
    Finset.single_le_sum (f := fun μ' => (-(P.coeff μ').order).toNat) (fun _ _ => Nat.zero_le _) hμ'
  have h1 := Int.self_le_toNat (-(P.coeff μ').order)
  have hc : (P.coeff μ').coeff k = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_order
    omega
  rw [hc, map_zero]

private theorem isHomogeneous_frame_lemma_6 {K₁ : Type} [Field K₁] {K : Type} [NormedField K] (ι : K₁ →+* K)
    (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (d : ℕ) (hP : P.IsHomogeneous d)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (c : K) (k : ℤ) :
    (C c * bind₁ (frameLin Bm lam) (map ι (lcoeffPoly P k))).IsHomogeneous d := by
  have hQh : (map ι (lcoeffPoly P k)).IsHomogeneous d := by
    intro ν hν
    apply hP
    intro h0
    apply hν
    rw [MvPolynomial.coeff_map, coeff_lcoeffPoly_lemma_2, h0]
    all_goals simp
  have hb : (bind₁ (frameLin Bm lam) (map ι (lcoeffPoly P k))).IsHomogeneous d := by
    have h := hQh.eval₂ C (frameLin Bm lam) (fun r => isHomogeneous_C (ArcLt Dw) r)
      (fun x => frameLin_homog Bm lam x)
    rw [one_mul] at h
    exact h
  have h := (isHomogeneous_C (ArcLt Dw) c).mul hb
  rw [zero_add] at h
  exact h

private theorem eval_frame_lemma_7 {K : Type} [NormedField K]
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (c : K) (Q : MvPolynomial (ArcLt Dw) K)
    (x : ArcLt Dw → K) :
    eval x (C c * bind₁ (frameLin Bm lam) Q) = c * eval (frameSub Bm lam x) Q := by
  have hfs : ∀ y, eval x (frameLin Bm lam y) = frameSub Bm lam x y := fun y => by
    simp only [frameLin, frameSub, map_sum, map_mul, eval_X, eval_C, Finset.sum_mul, mul_assoc]
  rw [map_mul, eval_C]
  congr 1
  induction Q using MvPolynomial.induction_on <;> simp_all

private theorem coeff_subst_lemma_8 {K : Type} [NormedField K]
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (hAB : ∀ τ, A τ * Bm τ = 1)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (c : K) (Q : MvPolynomial (ArcLt Dw) K)
    (μ : ArcLt Dw →₀ ℕ) :
    coeff μ (bind₁ (fun i => ∑ k : ArcLt Dw, C (subA A i k) * (X k : MvPolynomial (ArcLt Dw) K))
        (C c * bind₁ (frameLin Bm lam) Q)) =
      c * ((μ.prod fun x e => (lam x.1 x.2.2)⁻¹ ^ e) * coeff μ Q) := by
  have hfun : (fun y => bind₁ (fun i => ∑ k : ArcLt Dw, C (subA A i k) *
      (X k : MvPolynomial (ArcLt Dw) K)) (frameLin Bm lam y)) = fun x => C (lam x.1 x.2.2)⁻¹ * X x :=
    funext fun x => by
      obtain ⟨τ, i, j⟩ := x
      have key : ∀ k : Fin (Dw.mult τ), ∑ l, A τ k l * Bm τ l j = if k = j then 1 else 0 := by
        intro k
        have h := congrFun (congrFun (hAB τ) k) j
        rwa [Matrix.mul_apply, Matrix.one_apply] at h
      simp only [frameLin, map_sum, map_mul, bind₁_X_right, bind₁_C_right, subA_sum, Finset.sum_mul]
      calc _ = ∑ k : Fin (Dw.mult τ), C ((∑ l, A τ k l * Bm τ l j) * (lam τ j)⁻¹) *
              (X ⟨τ, i, k⟩ : MvPolynomial (ArcLt Dw) K) := by
            show ∑ l : Fin (Dw.mult τ), ∑ k : Fin (Dw.mult τ), C (A τ k l) *
              (X ⟨τ, i, k⟩ : MvPolynomial (ArcLt Dw) K) * (C (Bm τ l j) * C (lam τ j)⁻¹) = _
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [Finset.sum_mul, map_sum, map_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
        _ = C (lam τ j)⁻¹ * X ⟨τ, i, j⟩ := by
            rw [Finset.sum_eq_single j]
            · simp [key]
            · intro k _ hkj
              simp [key, hkj]
            · intro h
              exact absurd (Finset.mem_univ j) h
  rw [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_bind₁, hfun, MvPolynomial.coeff_C_mul,
    coeff_bind_scale_lemma_3]

set_option maxHeartbeats 800000 in

theorem coeff_bound (hFC : FinCoreStatement) (hBC : BasisChangeStatement)
    {K₁ : Type} [Field K₁] {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (ι : K₁ →+* K) (K₀ : Subfield K) (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (S : Set K)
    (hS1 : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1)
    (hS2 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - ρ| < ε)
    (hS3 : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S)
    (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (d : ℕ) (hP : P.IsHomogeneous d) (n : ℕ)
    (γ : K) (hγ : γ ≠ 0) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (hlam : ∀ τ k, lam τ k ≠ 0)
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (hAB : ∀ τ, A τ * Bm τ = 1)
    (Cb : ℝ) (hC : 1 ≤ Cb) (hA : ∀ τ k l, ‖A τ k l‖ ≤ Cb)
    (hbd : ∀ t ∈ S, ∀ Y : ArcLt Dw → K, (∀ x, Y x ∈ K₀ ∧ ‖Y x‖ ≤ 1) →
      ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
      Filter.Tendsto (fun k : ℤ => ‖eval (frameSub Bm lam Y) (map ι (lcoeffPoly P k)) * t ^ k‖)
        Filter.cofinite (nhds 0) ∧
      ‖(γ ^ n)⁻¹ * ∑' k : ℤ, eval (frameSub Bm lam Y) (map ι (lcoeffPoly P k)) * t ^ k‖ ≤ 1)
    (μ : ArcLt Dw →₀ ℕ) (m : ℤ) :
    ‖ι ((P.coeff μ).coeff m)‖ ≤ ‖γ‖ ^ n * (μ.prod fun x e => ‖lam x.1 x.2.2‖ ^ e) * Cb ^ d := by
  classical
  obtain ⟨R, hRdef⟩ : ∃ R : ℤ → MvPolynomial (ArcLt Dw) K,
      ∀ k, R k = C (γ ^ n)⁻¹ * bind₁ (frameLin Bm lam) (map ι (lcoeffPoly P k)) :=
    ⟨_, fun _ => rfl⟩
  have hC0 : (0 : ℝ) ≤ Cb := by linarith
  have hRh : ∀ k, (R k).IsHomogeneous d := fun k => by
    rw [hRdef]
    exact isHomogeneous_frame_lemma_6 ι P d hP Bm lam _ k
  have hevR : ∀ (k : ℤ) (x : ArcLt Dw → K),
      eval x (R k) = (γ ^ n)⁻¹ * eval (frameSub Bm lam x) (map ι (lcoeffPoly P k)) := fun k x => by
    rw [hRdef]
    exact eval_frame_lemma_7 Bm lam _ _ x
  have hδ1 : ∀ ν, ‖coeff ν (map (Int.castRingHom K) (detZ Dw))‖ ≤ 1 := fun ν => by
    rw [MvPolynomial.coeff_map]
    exact IsUltrametricDist.norm_intCast_le_one K _
  have hframe : ∀ t ∈ S, ∀ x : ArcLt Dw → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) →
      ‖eval x (map (Int.castRingHom K) (detZ Dw))‖ = 1 →
      Filter.Tendsto (fun k => ‖eval x (R k) * t ^ k‖) Filter.cofinite (nhds 0) ∧
      ‖∑' k, eval x (R k) * t ^ k‖ ≤ 1 := by
    intro t ht x hx hdet
    rw [eval_map_detZ_lemma] at hdet
    obtain ⟨h1, h2⟩ := hbd t ht x hx hdet
    constructor
    · have h3 := h1.const_mul ‖(γ ^ n)⁻¹‖
      rw [mul_zero] at h3
      refine h3.congr fun k => ?_
      simp only [hevR, norm_mul, mul_assoc]
    · simp only [hevR, mul_assoc]
      rw [tsum_mul_left]
      exact h2
  obtain ⟨b, hbR'⟩ := exists_lcoeffPoly_eq_zero_lemma_5 P
  have hbR : ∀ k : ℤ, k < -(b : ℤ) → R k = 0 := fun k hk => by
    rw [hRdef, hbR' k hk, map_zero, map_zero, mul_zero]
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = μ.prod fun x e => ‖lam x.1 x.2.2‖ ^ e := ⟨_, rfl⟩
  have hG : ‖μ.prod fun x e => (lam x.1 x.2.2)⁻¹ ^ e‖ = L⁻¹ := by
    rw [hLdef]
    simp only [Finsupp.prod, norm_prod, norm_pow, norm_inv, inv_pow, Finset.prod_inv_distrib]
  have hL : 0 < L := by
    rw [hLdef, Finsupp.prod]
    exact Finset.prod_pos fun x _ => pow_pos (norm_pos_iff.mpr (hlam _ _)) _
  have hγn : 0 < ‖γ‖ ^ n := pow_pos (norm_pos_iff.mpr hγ) n
  obtain ⟨hcoef, -⟩ := hFC K K₀ hres S hS1 hS2 hS3 (ArcLt Dw) (map (Int.castRingHom K) (detZ Dw))
    hδ1 (exists_coeff_norm_one Dw) R b hbR hframe m
  have hB := hBC K (ArcLt Dw) (R m) d (hRh m) hcoef (subA A) Cb hC
    (fun y z => norm_subA_le_lemma_4 A Cb hC0 hA y z) μ
  rw [hRdef, coeff_subst_lemma_8 A Bm hAB lam, MvPolynomial.coeff_map, coeff_lcoeffPoly_lemma_2,
    norm_mul, norm_mul, norm_inv, norm_pow, hG] at hB
  rw [← hLdef]
  calc ‖ι ((P.coeff μ).coeff m)‖
      = L * (‖γ‖ ^ n * ((‖γ‖ ^ n)⁻¹ * (L⁻¹ * ‖ι ((P.coeff μ).coeff m)‖))) := by
        rw [mul_inv_cancel_left₀ hγn.ne', mul_inv_cancel_left₀ hL.ne']
    _ ≤ L * (‖γ‖ ^ n * Cb ^ d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hγn.le) hL.le
    _ = ‖γ‖ ^ n * L * Cb ^ d := by ring

end FinKey

end Formalism.L2.Pj.QAt
