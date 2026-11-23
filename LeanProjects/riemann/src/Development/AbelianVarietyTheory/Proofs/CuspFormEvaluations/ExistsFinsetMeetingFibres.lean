import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames

namespace GlobalTheory.FrameNet

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

noncomputable section

theorem norm_det_le {r : ℕ} {m : Matrix (Fin r) (Fin r) ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hm : ∀ i k, ‖m i k‖ ≤ s) : ‖m.det‖ ≤ (r : ℝ) ^ r * s ^ r := by
  have hσ : ∀ σ : Equiv.Perm (Fin r), ‖Equiv.Perm.sign σ • ∏ i, m (σ i) i‖ ≤ s ^ r := by
    intro σ
    have hp : ‖∏ i, m (σ i) i‖ ≤ s ^ r := by
      rw [norm_prod]
      calc ∏ i, ‖m (σ i) i‖ ≤ ∏ _i : Fin r, s :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hm _ _)
        _ = s ^ r := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hp
  have hfac : ((Nat.factorial r : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ • ∏ i, m (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin r), ‖Equiv.Perm.sign σ • ∏ i, m (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), s ^ r := Finset.sum_le_sum fun σ _ => hσ σ
    _ = (Nat.factorial r : ℝ) * s ^ r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (r : ℝ) ^ r * s ^ r := mul_le_mul_of_nonneg_right hfac (pow_nonneg hs _)

theorem norm_mul_inv_sub_one_le {r : ℕ} {m m' : Matrix (Fin r) (Fin r) ℂ} {s ε : ℝ} (hs : 1 ≤ s)
    (hm : ∀ i k, ‖m' i k‖ ≤ s) (hd : m'.det ≠ 0) (hε : ∀ i k, ‖m i k - m' i k‖ ≤ ε) (a b : Fin r) :
    ‖(m * m'⁻¹) a b - (if a = b then 1 else 0)‖ ≤ r * (ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖)) := by
  have hu : IsUnit m'.det := isUnit_iff_ne_zero.mpr hd
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε a a)
  have hadj : ∀ k c, ‖m'.adjugate k c‖ ≤ (r : ℝ) ^ r * s ^ r := by
    intro k c
    rw [Matrix.adjugate_apply]
    apply norm_det_le (by linarith)
    intro i j
    rw [Matrix.updateRow_apply]
    split_ifs with h
    · by_cases hjk : j = k <;> simp [hjk] <;> linarith
    · exact hm i j
  have hinv : ∀ k c, ‖m'⁻¹ k c‖ ≤ (r : ℝ) ^ r * s ^ r / ‖m'.det‖ := by
    intro k c
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, norm_mul, norm_inv,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hadj k c) (inv_nonneg.mpr (norm_nonneg _))
  have hkey : (m * m'⁻¹) a b - (if a = b then 1 else 0) = ∑ k, (m a k - m' a k) * m'⁻¹ k b := by
    have h1 : m * m'⁻¹ - 1 = (m - m') * m'⁻¹ := by rw [sub_mul, Matrix.mul_nonsing_inv _ hu]
    have h2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, Matrix.one_apply] at h2
    rw [h2, Matrix.mul_apply]
    simp only [Matrix.sub_apply]
  rw [hkey]
  calc ‖∑ k, (m a k - m' a k) * m'⁻¹ k b‖ ≤ ∑ k, ‖(m a k - m' a k) * m'⁻¹ k b‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin r, ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hε a k) (hinv k b) (norm_nonneg _) hε0
    _ = r * (ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖)) := by simp

def cell (s δ : ℝ) (z : ℂ) : ℤ × ℤ := (⌊(z.re + s) / δ⌋, ⌊(z.im + s) / δ⌋)

theorem abs_sub_le_of_floor_eq {s δ a b : ℝ} (hδ : 0 < δ) (h : ⌊(a + s) / δ⌋ = ⌊(b + s) / δ⌋) :
    |a - b| ≤ δ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos hδ, div_lt_one hδ] at h1
  exact h1.le

theorem norm_sub_le_of_cell_eq {s δ : ℝ} (hδ : 0 < δ) {z w : ℂ} (h : cell s δ z = cell s δ w) :
    ‖z - w‖ ≤ 2 * δ := by
  simp only [cell, Prod.mk.injEq] at h
  have h1 := abs_sub_le_of_floor_eq hδ h.1
  have h2 := abs_sub_le_of_floor_eq hδ h.2
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ δ + δ := by rw [Complex.sub_re, Complex.sub_im]; exact add_le_add h1 h2
    _ = 2 * δ := by ring

theorem floor_mem_Icc {s δ a : ℝ} (hδ : 0 < δ) (h : |a| ≤ s) :
    ⌊(a + s) / δ⌋ ∈ Finset.Icc (0 : ℤ) ⌊2 * s / δ⌋ := by
  have ha := abs_le.mp h
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hδ.le)
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hδ.le)

theorem cell_mem {s δ : ℝ} (hδ : 0 < δ) {z : ℂ} (h : ‖z‖ ≤ s) :
    cell s δ z ∈ Finset.Icc (0 : ℤ) ⌊2 * s / δ⌋ ×ˢ Finset.Icc (0 : ℤ) ⌊2 * s / δ⌋ := by
  simp only [cell, Finset.mem_product]
  exact ⟨floor_mem_Icc hδ ((Complex.abs_re_le_norm z).trans h),
    floor_mem_Icc hδ ((Complex.abs_im_le_norm z).trans h)⟩

theorem card_Icc_floor_le {t : ℝ} (ht : 0 ≤ t) : ((Finset.Icc (0 : ℤ) ⌊t⌋).card : ℝ) ≤ t + 1 := by
  rw [Int.card_Icc, sub_zero]
  have h0 : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht
  have e : (((⌊t⌋ + 1).toNat : ℕ) : ℝ) = ((⌊t⌋ + 1 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [e]
  push_cast
  linarith [Int.floor_le t]

theorem exists_finset_meeting_fibres {α β : Type*} (O : Set α) (g : α → β) (S : Finset β)
    (hS : ∀ x ∈ O, g x ∈ S) :
    ∃ N : Finset α, (N : Set α) ⊆ O ∧ N.card ≤ S.card ∧ ∀ x ∈ O, ∃ y ∈ N, g x = g y := by
  classical
  let T := S.filter (fun b => ∃ x ∈ O, g x = b)
  have hT : ∀ b ∈ T, ∃ x ∈ O, g x = b := fun b hb => (Finset.mem_filter.mp hb).2
  let pick : T → α := fun b => (hT b.1 b.2).choose
  refine ⟨T.attach.image pick, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact (hT b.1 b.2).choose_spec.1
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_attach]
    exact Finset.card_filter_le _ _
  · intro x hx
    have hb : g x ∈ T := Finset.mem_filter.mpr ⟨hS x hx, x, hx, rfl⟩
    refine ⟨pick ⟨g x, hb⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    exact ((hT (g x) hb).choose_spec.2).symm

theorem exists_net_of_matrices {α ι : Type*} [Fintype ι] {r : ℕ} (O : Set α)
    (m : α → ι → Matrix (Fin r) (Fin r) ℂ) (D : ι → ℝ) (hD0 : ∀ τ, 0 < D τ) (hD : 1 ≤ ∏ τ, D τ)
    {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η) (hη : η ≤ 1)
    (hm : ∀ x ∈ O, ∀ τ i k, ‖m x τ i k‖ ^ 2 ≤ B) (hdet : ∀ x ∈ O, ∀ τ, ‖(m x τ).det‖ = D τ) :
    ∃ N : Finset α, (N : Set α) ⊆ O ∧
      (N.card : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * Fintype.card ι * r ^ 2) ∧
      ∀ x ∈ O, ∃ y ∈ N, ∀ τ a b,
        ‖(m x τ * (m y τ)⁻¹) a b - (if a = b then 1 else 0)‖ ≤ η := by
  classical
  rcases O.eq_empty_or_nonempty with hO | ⟨x0, hx0⟩
  · refine ⟨∅, by simp, ?_, fun x hx => by simp [hO] at hx⟩
    rw [Finset.card_empty, Nat.cast_zero]
    apply pow_nonneg
    exact mul_nonneg (div_nonneg (by positivity) hη0.le)
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) _)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨{x0}, by simpa using hx0, by simp, fun x _ => ⟨x0, by simp, fun τ a => a.elim0⟩⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt B := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hB
  have hs0 : 0 < s := by linarith
  have hsB : s ^ 2 = B := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hent : ∀ x ∈ O, ∀ τ i k, ‖m x τ i k‖ ≤ s := fun x hx τ i k => by
    have h := Real.abs_le_sqrt (hm x hx τ i k)
    rwa [abs_norm, ← hs] at h
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hDM : ∀ τ, D τ ≤ (r : ℝ) ^ r * s ^ r := fun τ => by
    rw [← hdet x0 hx0 τ]; exact norm_det_le hs0.le (hent x0 hx0 τ)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (r : ℝ) ^ (r + 1) * s ^ r := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ι → ℝ, ∀ τ, δ τ = η * D τ / c := ⟨_, fun _ => rfl⟩
  have hδ0 : ∀ τ, 0 < δ τ := fun τ => by rw [hδ]; exact div_pos (mul_pos hη0 (hD0 τ)) hc0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ,
      Q = 4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) / η + (r : ℝ) ^ r * s ^ r := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; exact add_pos (div_pos (by positivity) hη0) (by positivity)
  have hcnt : ∀ τ, ((Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋).card : ℝ) ≤ Q / D τ := by
    intro τ
    have hDτ := hD0 τ
    refine (card_Icc_floor_le (div_nonneg (by linarith) (hδ0 τ).le)).trans ?_
    have e : 2 * s / δ τ = (4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) / η) / D τ := by
      have := hη0.ne'; have := hDτ.ne'; have := hr0.ne'; have := hs0.ne'
      rw [hδ, hc]; field_simp; ring
    rw [e, hQ, add_div]
    linarith [(one_le_div hDτ).mpr (hDM τ)]
  have hQb : Q ≤ 6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r := by
    have e1 : ((r : ℝ) * B) ^ r = (r : ℝ) ^ r * s ^ (2 * r) := by rw [mul_pow, ← hsB, ← pow_mul]
    have p1 : (r : ℝ) ^ (r + 1) ≤ (r : ℝ) ^ r * r ^ 2 := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have p2 : s ^ (r + 1) ≤ s ^ (2 * r) := pow_le_pow_right₀ hs1 (by omega)
    have p3 : s ^ r ≤ s ^ (2 * r) := pow_le_pow_right₀ hs1 (by omega)
    have p4 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hX : 0 ≤ (r : ℝ) ^ r * s ^ (2 * r) := by positivity
    have a1 : 4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) ≤ 4 * ((r : ℝ) ^ r * r ^ 2) * s ^ (2 * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left p1 (by norm_num)) p2 (by positivity) (by positivity)
    have b1 : η * ((r : ℝ) ^ r * s ^ r) ≤ 1 * ((r : ℝ) ^ r * s ^ (2 * r)) :=
      mul_le_mul hη (mul_le_mul_of_nonneg_left p3 (by positivity)) (by positivity) zero_le_one
    have b2 := mul_le_mul_of_nonneg_right p4 hX
    rw [hQ, e1]
    have e2 : 4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) / η + (r : ℝ) ^ r * s ^ r
        = (4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) + η * ((r : ℝ) ^ r * s ^ r)) / η := by
      rw [add_div, mul_div_cancel_left₀ _ hη0.ne']
    have e3 : 6 * (r : ℝ) ^ 2 / η * ((r : ℝ) ^ r * s ^ (2 * r))
        = (6 * ((r : ℝ) ^ r * r ^ 2) * s ^ (2 * r)) / η := by ring
    rw [e2, e3]
    apply div_le_div_of_nonneg_right _ hη0.le
    nlinarith
  let g : α → ι → Fin r → Fin r → ℤ × ℤ := fun x τ i k => cell s (δ τ) (m x τ i k)
  let S : Finset (ι → Fin r → Fin r → ℤ × ℤ) :=
    Fintype.piFinset fun τ => Fintype.piFinset fun _ : Fin r => Fintype.piFinset fun _ : Fin r =>
      Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋ ×ˢ Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋
  have hgS : ∀ x ∈ O, g x ∈ S := by
    intro x hx
    simp only [S, g, Fintype.mem_piFinset]
    intro τ i k
    exact cell_mem (hδ0 τ) (hent x hx τ i k)
  obtain ⟨N, hNO, hNcard, hNcov⟩ := exists_finset_meeting_fibres O g S hgS
  refine ⟨N, hNO, ?_, ?_⟩
  · have hS : (S.card : ℝ) = ∏ τ, ((Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋).card : ℝ) ^ (2 * r ^ 2) := by
      simp only [S, Fintype.card_piFinset, Finset.card_product, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      push_cast
      exact Finset.prod_congr rfl fun τ _ => by ring
    have hPD : 0 ≤ ∏ τ, D τ := Finset.prod_nonneg fun τ _ => (hD0 τ).le
    calc (N.card : ℝ) ≤ S.card := by exact_mod_cast hNcard
      _ = ∏ τ, ((Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋).card : ℝ) ^ (2 * r ^ 2) := hS
      _ ≤ ∏ τ, (Q / D τ) ^ (2 * r ^ 2) :=
          Finset.prod_le_prod (fun τ _ => by positivity)
            (fun τ _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (hcnt τ) _)
      _ = (Q ^ Fintype.card ι / ∏ τ, D τ) ^ (2 * r ^ 2) := by
          rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ (Q ^ Fintype.card ι) ^ (2 * r ^ 2) := by
          apply pow_le_pow_left₀ (div_nonneg (pow_nonneg hQ0.le _) hPD)
          exact div_le_self (pow_nonneg hQ0.le _) hD
      _ = Q ^ (2 * Fintype.card ι * r ^ 2) := by rw [← pow_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ hQ0.le hQb _
  · intro x hx
    obtain ⟨y, hyN, hxy⟩ := hNcov x hx
    have hy := hNO hyN
    refine ⟨y, hyN, fun τ a b => ?_⟩
    have hcell : ∀ i k, ‖m x τ i k - m y τ i k‖ ≤ 2 * δ τ := fun i k =>
      norm_sub_le_of_cell_eq (hδ0 τ) (congrFun (congrFun (congrFun hxy τ) i) k)
    have hdy : (m y τ).det ≠ 0 := by
      intro h0
      have h1 := hdet y hy τ
      rw [h0, norm_zero] at h1
      exact (hD0 τ).ne h1
    have key := norm_mul_inv_sub_one_le hs1 (hent y hy τ) hdy hcell a b
    rw [hdet y hy τ] at key
    refine key.trans (le_of_eq ?_)
    have := hη0.ne'; have := (hD0 τ).ne'; have := hr0.ne'; have := hs0.ne'
    rw [hδ, hc]
    field_simp
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def basisMat (τ : E →+* ℂ) (v : Fin r → Fin r → E) : Matrix (Fin r) (Fin r) ℂ :=
  ((Matrix.of v)ᵀ).map τ

def gramMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i k => herm G (v i) (v k)

theorem gram_basisMat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    gram τ G (basisMat τ v) = (gramMat G v).map τ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, gramMat, basisMat, hermC, herm, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.map_apply,
    Matrix.transpose_apply, map_sum, map_mul, cc, NumberField.IsCMField.complexEmbedding_complexConj]

omit [NumberField E] [IsCMField E] in
theorem norm_det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    ‖(gram τ G M).det‖ = ‖M.det‖ ^ 2 * ‖τ G.det‖ := by
  rw [PIW.FdPA.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have h1 : (G.map τ).det = τ G.det := by rw [RingHom.map_det]; rfl
  have h2 : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by rw [RingHom.map_det]; rfl
  rw [h1, h2, norm_mul, norm_mul, Complex.norm_conj]
  ring

omit [NumberField E] [IsCMField E] in
theorem det_basisMat_ne_zero (τ : E →+* ℂ) {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (basisMat τ v).det ≠ 0 := by
  have hu : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hv
  have hd : (Matrix.of v).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have e : (basisMat τ v).det = τ ((Matrix.of v)ᵀ).det := by
    unfold basisMat; rw [RingHom.map_det]; rfl
  rw [e, Matrix.det_transpose]
  exact (map_ne_zero τ).mpr hd

theorem norm_emb_det_gramMat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    ‖τ (gramMat G v).det‖ = ‖(basisMat τ v).det‖ ^ 2 * ‖τ G.det‖ := by
  have e : τ (gramMat G v).det = (gram τ G (basisMat τ v)).det := by
    rw [gram_basisMat, RingHom.map_det]; rfl
  rw [e]
  exact norm_det_gram τ G _

variable (X : Data E r)

theorem det_gramMat_ne_zero {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (gramMat X.Gm v).det ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  intro h0
  have h1 := norm_emb_det_gramMat τ X.Gm v
  rw [h0, map_zero, norm_zero] at h1
  have h2 : (basisMat τ v).det ≠ 0 := det_basisMat_ne_zero τ hv
  have h3 : τ X.Gm.det ≠ 0 := (map_ne_zero τ).mpr X.Gm_det
  exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h2)) (norm_ne_zero_iff.mpr h3) h1.symm

theorem norm_det_sq_of_ortho {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 X.Gm.det‖ = 1 := by
  rw [← norm_det_gram τ.1 X.Gm (mat x τ), hx τ, Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> simp

theorem det_ne_zero_of_ortho {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) :
    (mat x τ).det ≠ 0 := by
  intro h
  have h1 := norm_det_sq_of_ortho X hx τ
  rw [h, norm_zero] at h1
  simp at h1

theorem norm_det_coord {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → Fin r → E) :
    ‖((mat x τ)⁻¹ * basisMat τ.1 v).det‖ = Real.sqrt ‖τ.1 (gramMat X.Gm v).det‖ := by
  have h1 := norm_det_sq_of_ortho X hx τ
  have hd := det_ne_zero_of_ortho X hx τ
  have hdn : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hd
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, norm_mul, norm_inv,
    norm_emb_det_gramMat]
  have hG : ‖τ.1 X.Gm.det‖ = (‖(mat x τ).det‖⁻¹) ^ 2 := by
    rw [inv_pow]
    field_simp
    linarith [h1]
  rw [hG, ← mul_pow, Real.sqrt_sq (by positivity)]
  ring

theorem maj_eq_sum_coord {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → Fin r → E)
    (k : Fin r) : X.maj x τ (Data.emb τ.1 (v k)) =
      ∑ i, ‖((mat x τ)⁻¹ * basisMat τ.1 v) i k‖ ^ 2 := by
  have hd : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_ortho X hx τ)
  have hw : Data.emb τ.1 (v k) = mat x τ *ᵥ fun i => ((mat x τ)⁻¹ * basisMat τ.1 v) i k := by
    funext j
    have h1 : (mat x τ * ((mat x τ)⁻¹ * basisMat τ.1 v)) j k = basisMat τ.1 v j k := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.mulVec, dotProduct]
    rw [h1]
    rfl
  rw [hw, UnipMove.GraphH.maj_ortho X hx τ]
  rfl

def shortFrames (v : Fin r → Fin r → E) (B : ℝ) : Set (Frame X.Ψ r) :=
  {x | (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ i, ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 (v i)) ≤ B}

theorem mem_shortFrames {v : Fin r → Fin r → E} {B : ℝ} {x : Frame X.Ψ r} :
    x ∈ shortFrames X v B ↔ (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ i, ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 (v i)) ≤ B := by
  exact Iff.rfl

theorem shortFrames_subset_dom (v : Fin r → Fin r → E) (B : ℝ) : shortFrames X v B ⊆ X.dom := by
  intro x hx
  have ho : X.IsOrtho x := hx.1
  rw [PIW.FdPA.mem_dom_iff]
  intro τ
  refine ⟨det_ne_zero_of_ortho X ho τ, fun i => ?_⟩
  have hm : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
    rfl
  rw [hm, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    rw [Finset.prod_ne_zero_iff]
    intro a _
    unfold sgn
    split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

theorem exists_net_card_le (v : Fin r → Fin r → E) (hv : LinearIndependent E v)
    (hint : ∀ i k, IsIntegral ℤ (herm X.Gm (v i) (v k))) {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η)
    (hη : η ≤ 1) :
    ∃ N : Finset (Frame X.Ψ r), (N : Set (Frame X.Ψ r)) ⊆ shortFrames X v B ∧
      (∀ x ∈ shortFrames X v B, ∃ A : Frame X.Ψ r, rmul x A ∈ N ∧
        ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ η) ∧
      (N.card : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * fdeg E * r ^ 2) := by
  classical
  have hcard : Fintype.card X.Ψ = fdeg E := ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi X
  have hdetG : (gramMat X.Gm v).det ≠ 0 := det_gramMat_ne_zero X hv
  have hmem : (gramMat X.Gm v).det ∈ integralClosure ℤ E := by
    rw [Matrix.det_apply]
    refine sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (prod_mem fun i _ => hint (σ i) i) _
  have hint_det : IsIntegral ℤ (gramMat X.Gm v).det := hmem
  obtain ⟨D, hDdef⟩ : ∃ D : X.Ψ → ℝ, ∀ τ, D τ = Real.sqrt ‖τ.1 (gramMat X.Gm v).det‖ :=
    ⟨_, fun _ => rfl⟩
  have hD0 : ∀ τ, 0 < D τ := fun τ => by
    rw [hDdef]; exact Real.sqrt_pos.mpr (norm_pos_iff.mpr ((map_ne_zero _).mpr hdetG))
  have hD : 1 ≤ ∏ τ : X.Ψ, D τ := by
    have h1 := ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.one_le_prod_norm X _ hint_det hdetG
    have h2 : (∏ τ : X.Ψ, D τ) ^ 4 = ∏ τ : X.Ψ, ‖τ.1 (gramMat X.Gm v).det‖ ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hDdef τ, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (norm_nonneg _)]
    rcases lt_or_ge (∏ τ : X.Ψ, D τ) 1 with hlt | hge
    swap
    · exact hge
    have h3 : (∏ τ : X.Ψ, D τ) ^ 4 < 1 :=
      pow_lt_one₀ (Finset.prod_nonneg fun τ _ => (hD0 τ).le) hlt (by norm_num)
    linarith
  have hm : ∀ x ∈ shortFrames X v B, ∀ (τ : X.Ψ) (i k : Fin r),
      ‖((mat x τ)⁻¹ * basisMat τ.1 v) i k‖ ^ 2 ≤ B := by
    intro x hx τ i k
    have ho : X.IsOrtho x := hx.1
    have hnn : ∀ σ : X.Ψ, 0 ≤ X.maj x σ (Data.emb σ.1 (v k)) := fun σ => by
      rw [maj_eq_sum_coord X ho σ v k]; exact Finset.sum_nonneg fun _ _ => by positivity
    calc ‖((mat x τ)⁻¹ * basisMat τ.1 v) i k‖ ^ 2
        ≤ ∑ i', ‖((mat x τ)⁻¹ * basisMat τ.1 v) i' k‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ‖((mat x τ)⁻¹ * basisMat τ.1 v) i' k‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ i)
      _ = X.maj x τ (Data.emb τ.1 (v k)) := (maj_eq_sum_coord X ho τ v k).symm
      _ ≤ ∑ σ : X.Ψ, X.maj x σ (Data.emb σ.1 (v k)) :=
          Finset.single_le_sum (f := fun σ : X.Ψ => X.maj x σ (Data.emb σ.1 (v k)))
            (fun σ _ => hnn σ) (Finset.mem_univ τ)
      _ ≤ B := hx.2 k
  have hdet : ∀ x ∈ shortFrames X v B, ∀ τ : X.Ψ,
      ‖((mat x τ)⁻¹ * basisMat τ.1 v).det‖ = D τ := by
    intro x hx τ
    rw [hDdef]
    exact norm_det_coord X hx.1 τ v
  obtain ⟨N, hNO, hNcard, hNcov⟩ := exists_net_of_matrices (shortFrames X v B)
    (fun x τ => (mat x τ)⁻¹ * basisMat τ.1 v) D hD0 hD hB hη0 hη hm hdet
  refine ⟨N, hNO, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyN, hxy⟩ := hNcov x hx
    have hy := hNO hyN
    let A : Frame X.Ψ r := fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ)
    refine ⟨A, ?_, fun τ a b => ?_⟩
    · have hxy' : rmul x A = y := by
        funext τ
        have hdx : IsUnit (mat x τ).det :=
          isUnit_iff_ne_zero.mpr (det_ne_zero_of_ortho X hx.1 τ)
        show mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdx, Matrix.one_mul]
      rw [hxy']
      exact hyN
    · have hdy : IsUnit (mat y τ).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_ortho X hy.1 τ)
      have hdV : IsUnit (basisMat τ.1 v).det :=
        isUnit_iff_ne_zero.mpr (det_basisMat_ne_zero τ.1 hv)
      have heq : (mat x τ)⁻¹ * basisMat τ.1 v * ((mat y τ)⁻¹ * basisMat τ.1 v)⁻¹ =
          (mat x τ)⁻¹ * mat y τ := by
        rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdy, Matrix.mul_assoc,
          ← Matrix.mul_assoc (basisMat τ.1 v), Matrix.mul_nonsing_inv _ hdV, Matrix.one_mul]
      have h := hxy τ a b
      beta_reduce at h
      rw [heq] at h
      exact h
  · rw [← hcard]
    exact hNcard

theorem log_le_of_card_le {n f r : ℕ} {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η) (hη : η ≤ 1)
    (h : (n : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * f * r ^ 2)) :
    (n : ℝ) ≤ Real.exp (2 * f * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * f * (r : ℝ) ^ 3 * Real.log (r * B)) ∧
      Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * f * (r : ℝ) ^ 3 * Real.log (r * B) := by
  have key : (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * f * r ^ 2) =
      Real.exp (2 * f * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * f * (r : ℝ) ^ 3 * Real.log (r * B)) ∧
      0 ≤ 2 * f * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * f * (r : ℝ) ^ 3 * Real.log (r * B) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have h6 : 1 ≤ 6 * (r : ℝ) ^ 2 / η := by
        rw [le_div_iff₀ hη0]; nlinarith
      have hrB : 1 ≤ (r : ℝ) * B := by nlinarith
      have ha : 0 < 6 * (r : ℝ) ^ 2 / η := by linarith
      have hb : 0 < ((r : ℝ) * B) ^ r := pow_pos (by linarith) _
      constructor
      · rw [← Real.exp_log (pow_pos (mul_pos ha hb) _), Real.log_pow, Real.log_mul ha.ne' hb.ne',
          Real.log_pow]
        congr 1
        push_cast
        ring
      · have l1 := Real.log_nonneg h6
        have l2 := Real.log_nonneg hrB
        positivity
  obtain ⟨he, hR0⟩ := key
  rw [he] at h
  refine ⟨h, ?_⟩
  rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    exact hR0
  · exact (Real.log_le_iff_le_exp h0).mpr h

theorem exists_frame_net (v : Fin r → Fin r → E) (hv : LinearIndependent E v)
    (hint : ∀ i k, IsIntegral ℤ (herm X.Gm (v i) (v k))) {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η)
    (hη : η ≤ 1) :
    ∃ N : Finset (Frame X.Ψ r), (N : Set (Frame X.Ψ r)) ⊆ shortFrames X v B ∧
      (∀ x ∈ shortFrames X v B, ∃ A : Frame X.Ψ r, rmul x A ∈ N ∧
        ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ η) ∧
      (N.card : ℝ) ≤ Real.exp (2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B)) ∧
      Real.log N.card ≤ 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B) := by
  obtain ⟨N, h1, h2, h3⟩ := exists_net_card_le X v hv hint hB hη0 hη
  obtain ⟨h4, h5⟩ := log_le_of_card_le hB hη0 hη h3
  exact ⟨N, h1, h2, h4, h5⟩

end

end GlobalTheory.FrameNet
