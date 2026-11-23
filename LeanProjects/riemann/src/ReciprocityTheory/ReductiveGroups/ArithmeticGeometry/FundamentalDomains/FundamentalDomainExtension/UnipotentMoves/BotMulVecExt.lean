import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowBlock
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace UnipMove.GraphH

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix

noncomputable section

def en {n : ℕ} (v : Fin n → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖

lemma en_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ en v := by
  exact norm_nonneg _

private lemma nsq_nonneg_unipotent_moves {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma en_sq {n : ℕ} (v : Fin n → ℂ) : en v ^ 2 = nsq v := by
  have e : en v = Real.sqrt (nsq v) := by
    unfold en nsq
    first
      | (rw [EuclideanSpace.norm_eq]; rfl)
      | (rw [EuclideanSpace.norm_eq]; simp)
      | simp [EuclideanSpace.norm_eq]
  rw [e, Real.sq_sqrt (nsq_nonneg_unipotent_moves v)]

lemma en_eq_sqrt {n : ℕ} (v : Fin n → ℂ) : en v = Real.sqrt (nsq v) := by
  unfold en nsq
  first
    | (rw [EuclideanSpace.norm_eq]; rfl)
    | (rw [EuclideanSpace.norm_eq]; simp)
    | simp [EuclideanSpace.norm_eq]

lemma en_add_le {n : ℕ} (u v : Fin n → ℂ) : en (u + v) ≤ en u + en v := by
  unfold en
  first
    | (rw [WithLp.toLp_add]; exact norm_add_le _ _)
    | exact norm_add_le _ _
    | simpa using norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)

lemma en_sub_le {n : ℕ} (u v : Fin n → ℂ) : en (u - v) ≤ en u + en v := by
  unfold en
  first
    | (rw [WithLp.toLp_sub]; exact norm_sub_le _ _)
    | exact norm_sub_le _ _
    | simpa using norm_sub_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)

lemma eq_zero_of_en {n : ℕ} (d : Fin n → ℂ) (h : en d = 0) : d = 0 := by
  rw [en_eq_sqrt, Real.sqrt_eq_zero (nsq_nonneg_unipotent_moves d)] at h
  have hs : ∀ j ∈ Finset.univ, ‖d j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖d j‖)).mp h
  funext j
  have := hs j (Finset.mem_univ j)
  simpa using this

lemma en_pos {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < en v := by
  exact lt_of_le_of_ne (en_nonneg v) (fun h => hv (eq_zero_of_en v h.symm))

lemma en_le_of_nsq {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : nsq u ≤ c ^ 2 * nsq v) : en u ≤ c * en v := by
  rw [en_eq_sqrt, en_eq_sqrt]
  calc Real.sqrt (nsq u) ≤ Real.sqrt (c ^ 2 * nsq v) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt (nsq v) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma opN_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, en (A *ᵥ v) ≤ c * en v) : Data.opN A ≤ c := by
  unfold Data.opN
  apply Real.sSup_le _ hc
  rintro t ⟨v, hv, rfl⟩
  have h1 := h v
  rw [en_eq_sqrt, en_eq_sqrt] at h1
  have hpos : 0 < Real.sqrt (nsq v) := by
    have := en_pos hv
    rwa [en_eq_sqrt] at this
  change Real.sqrt (nsq (A *ᵥ v)) / Real.sqrt (nsq v) ≤ c
  rw [div_le_iff₀ hpos]
  exact h1

lemma re_conj_mul (w : ℂ) (s : ℝ) : (conj w * (w * (s : ℂ))).re = s * ‖w‖ ^ 2 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  first
    | (rw [Complex.sq_norm, Complex.normSq_apply]; ring)
    | (rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring)
    | (simp [Complex.sq_abs, Complex.normSq_apply]; ring)

section Blocks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma sum_splitR (f : Fin r → ℝ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) := by
  have h : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  have e : ∑ j, f j = ∑ i : Fin (X.p0 + (r - X.p0)), f (Fin.cast h i) :=
    (Fintype.sum_equiv (finCongr h) (fun i => f (Fin.cast h i)) f (fun _ => rfl)).symm
  rw [e, Fin.sum_univ_add]
  rfl

def top (w : Fin r → ℂ) : Fin X.p0 → ℂ := fun a => w (Fin.castLE X.p0_le a)

def bot (w : Fin r → ℂ) : Fin (r - X.p0) → ℂ := fun m => w (nI X m)

def ext (d : Fin X.p0 → ℂ) : Fin r → ℂ := fun i => if h : (i : ℕ) < X.p0 then d ⟨i, h⟩ else 0

def blkA (K : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun a b => K (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le b)

def blkB (K : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  Matrix.of fun m b => K (nI X m) (Fin.castLE X.p0_le b)

lemma nsq_split (w : Fin r → ℂ) : nsq w = nsq (top X w) + nsq (bot X w) := by
  unfold nsq
  exact sum_splitR X (fun j => ‖w j‖ ^ 2)

lemma en_top_le (w : Fin r → ℂ) : en (top X w) ≤ en w := by
  rw [en_eq_sqrt, en_eq_sqrt]
  apply Real.sqrt_le_sqrt
  have h0 := nsq_nonneg_unipotent_moves (bot X w)
  rw [nsq_split X w]
  linarith

lemma en_bot_le (w : Fin r → ℂ) : en (bot X w) ≤ en w := by
  rw [en_eq_sqrt, en_eq_sqrt]
  apply Real.sqrt_le_sqrt
  have h0 := nsq_nonneg_unipotent_moves (top X w)
  rw [nsq_split X w]
  linarith

lemma sum_mul_ext (f : Fin r → ℂ) (d : Fin X.p0 → ℂ) :
    ∑ j, f j * ext X d j = ∑ b, f (Fin.castLE X.p0_le b) * d b := by
  have h : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  have e : ∑ j, f j * ext X d j =
      ∑ i : Fin (X.p0 + (r - X.p0)), f (Fin.cast h i) * ext X d (Fin.cast h i) :=
    (Fintype.sum_equiv (finCongr h) (fun i => f (Fin.cast h i) * ext X d (Fin.cast h i))
      (fun j => f j * ext X d j) (fun _ => rfl)).symm
  rw [e, Fin.sum_univ_add]
  have h1 : ∀ a : Fin X.p0, ext X d (Fin.cast h (Fin.castAdd (r - X.p0) a)) = d a := by
    intro a
    unfold ext
    split_ifs with ha
    · rfl
    · exact absurd a.isLt ha
  have h2 : ∀ m : Fin (r - X.p0), ext X d (Fin.cast h (Fin.natAdd X.p0 m)) = 0 := by
    intro m
    unfold ext
    split_ifs with hm
    · have e2 : ((Fin.cast h (Fin.natAdd X.p0 m) : Fin r) : ℕ) = X.p0 + (m : ℕ) := rfl
      omega
    · rfl
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

lemma top_mulVec_ext (K : Matrix (Fin r) (Fin r) ℂ) (d : Fin X.p0 → ℂ) :
    top X (K *ᵥ ext X d) = blkA X K *ᵥ d := by
  funext a
  exact sum_mul_ext X (fun j => K (Fin.castLE X.p0_le a) j) d

lemma bot_mulVec_ext (K : Matrix (Fin r) (Fin r) ℂ) (d : Fin X.p0 → ℂ) :
    bot X (K *ᵥ ext X d) = blkB X K *ᵥ d := by
  funext m
  exact sum_mul_ext X (fun j => K (nI X m) j) d

lemma blkA_low (Z : X.Coord) (τ : X.Ψ) : blkA X (X.lowBlock Z τ) = 1 := by
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [blkA, Data.lowBlock, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Fin.coe_castLE]
  split_ifs <;> first | omega | rfl | simp

lemma blkB_low (Z : X.Coord) (τ : X.Ψ) : blkB X (X.lowBlock Z τ) = Matrix.of (Z τ) := by
  ext m b
  have hb := b.isLt
  have hne : X.p0 + (m : ℕ) ≠ (b : ℕ) := by omega
  first
    | simp [blkB, Data.lowBlock, nI, Fin.ext_iff, hne, hb]
    | (simp only [blkB, Data.lowBlock, Matrix.of_apply, Fin.ext_iff, Fin.coe_castLE, nI]
       split_ifs <;> first | (simp_all; done) | omega | (congr 1 <;> ext <;> simp))

end Blocks

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma fin_split (i : Fin r) :
    (∃ a : Fin X.p0, i = Fin.castLE X.p0_le a) ∨ ∃ m : Fin (r - X.p0), i = nI X m := by
  by_cases h : (i : ℕ) < X.p0
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨(i : ℕ) - X.p0, by have := i.isLt; omega⟩, Fin.ext ?_⟩
    show (i : ℕ) = X.p0 + ((i : ℕ) - X.p0)
    omega

lemma col_mul (P Q : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) : col (P * Q) j = P *ᵥ col Q j := by
  first
    | rfl
    | (funext k; simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct])

lemma span_cols_eq {p : ℕ} (u w : Fin p → Fin r → ℂ) (A : Matrix (Fin p) (Fin p) ℂ)
    (hA : IsUnit A.det) (h : ∀ a, u a = ∑ b, A b a • w b) :
    Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range w) := by
  have key : ∀ b, w b = ∑ a, A⁻¹ a b • u a := by
    intro b
    have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have hc : ∀ c, ∑ a, A⁻¹ a b * A c a = (1 : Matrix (Fin p) (Fin p) ℂ) c b := by
      intro c
      rw [← hinv, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp_rw [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc, Matrix.one_apply]
    simp
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [h a]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [key b]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

private lemma sum_four_comm_unipotent_moves {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) :
    ∑ a, ∑ b, ∑ j, ∑ k, F a b j k = ∑ j, ∑ k, ∑ a, ∑ b, F a b j k := by
  calc ∑ a, ∑ b, ∑ j, ∑ k, F a b j k = ∑ a, ∑ j, ∑ b, ∑ k, F a b j k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ k, ∑ b, F a b j k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ k, ∑ b, F a b j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ b, F a b j k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm

private lemma hermC_mulVec_mulVec_eq_sum_gram' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (c d : Fin r → ℂ) :
    hermC τ G (M *ᵥ c) (M *ᵥ d) = ∑ j, ∑ k, c j * gram τ G M j k * conj (d k) := by
  have e1 : ∀ a b, (M *ᵥ c) a * τ (G a b) * conj ((M *ᵥ d) b) =
      ∑ j, ∑ k, M a j * c j * τ (G a b) * (conj (M b k) * conj (d k)) := by
    intro a b
    rw [show (M *ᵥ c) a = ∑ j, M a j * c j from rfl, show (M *ᵥ d) b = ∑ k, M b k * d k from rfl,
      map_sum, Finset.sum_mul, Finset.sum_mul_sum]
    simp only [map_mul]
  have e2 : ∀ j k, c j * gram τ G M j k * conj (d k) =
      ∑ a, ∑ b, c j * (M a j * τ (G a b) * conj (M b k)) * conj (d k) := by
    intro j k
    rw [show gram τ G M j k = ∑ a, ∑ b, M a j * τ (G a b) * conj (M b k) from rfl,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
  unfold hermC
  simp only [e1, e2]
  rw [sum_four_comm_unipotent_moves]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma col_eq_mulVec_single (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    col M j = M *ᵥ Pi.single j 1 := by
  funext k
  first
    | simp [col, Matrix.mulVec, dotProduct, Pi.single_apply]
    | simp [col, Matrix.mulVec_single_one]
    | (rw [Matrix.mulVec_single_one]; rfl)

private lemma hermC_mat_mulVec_eq_sum_sgn_of_isOrtho {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ c) (mat x τ *ᵥ d) =
      ∑ j, c j * ((sgn X.p0 j : ℝ) : ℂ) * conj (d j) := by
  rw [hermC_mulVec_mulVec_eq_sum_gram', ho τ]
  first
    | simp only [Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    | simp [Matrix.diagonal_apply]

lemma maj_ortho {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (c : Fin r → ℂ) :
    X.maj x τ (mat x τ *ᵥ c) = nsq c := by
  have hgp : X.gramPos x τ = 1 := by
    ext a b
    simp [Data.gramPos, ho τ, Matrix.diagonal_apply, Matrix.one_apply, sgn, Fin.ext_iff]
  have hcol : ∀ j, hermC τ.1 X.Gm (mat x τ *ᵥ c) (col (mat x τ) j) =
      c j * ((sgn X.p0 j : ℝ) : ℂ) := by
    intro j
    rw [col_eq_mulVec_single, hermC_mat_mulVec_eq_sum_sgn_of_isOrtho X ho]
    simp [Pi.single_apply]
  have hpos : X.posPart x τ (mat x τ *ᵥ c) = ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 := by
    unfold Data.posPart
    rw [hgp, inv_one]
    simp only [hcol, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hs : ((sgn X.p0 (Fin.castLE X.p0_le a : ℕ) : ℝ) : ℂ) = 1 := by simp [sgn]
    rw [hs, mul_one]
    rw [show c (Fin.castLE X.p0_le a) * conj (c (Fin.castLE X.p0_le a)) =
        conj (c (Fin.castLE X.p0_le a)) * (c (Fin.castLE X.p0_le a) * ((1 : ℝ) : ℂ)) by
          simp [mul_comm], re_conj_mul, one_mul]
  have hh : (hermC τ.1 X.Gm (mat x τ *ᵥ c) (mat x τ *ᵥ c)).re =
      ∑ j : Fin r, sgn X.p0 j * ‖c j‖ ^ 2 := by
    rw [hermC_mat_mulVec_eq_sum_sgn_of_isOrtho X ho, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show c j * ((sgn X.p0 j : ℝ) : ℂ) * conj (c j) =
        conj (c j) * (c j * ((sgn X.p0 j : ℝ) : ℂ)) by ring, re_conj_mul]
  unfold Data.maj
  rw [hpos, hh, sum_splitR X (fun j => sgn X.p0 j * ‖c j‖ ^ 2)]
  unfold nsq
  rw [sum_splitR X (fun j => ‖c j‖ ^ 2)]
  have h1 : ∀ a : Fin X.p0, sgn X.p0 (Fin.castLE X.p0_le a : ℕ) = 1 := fun a => by simp [sgn]
  have h2 : ∀ m : Fin (r - X.p0), sgn X.p0 (nI X m : ℕ) = -1 := fun m => by
    unfold sgn
    rw [if_neg]
    show ¬ (X.p0 + (m : ℕ) < X.p0)
    omega
  simp only [h1, h2, one_mul, neg_one_mul, Finset.sum_neg_distrib]
  ring

private lemma nsq_mulVec_le_sum_norm_sq_mul_nsq {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (W *ᵥ v) ≤ (∑ i, ∑ j, ‖W i j‖ ^ 2) * nsq v := by
  unfold nsq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖(W *ᵥ v) i‖ ≤ ∑ j, ‖W i j‖ * ‖v j‖ := by
    calc ‖(W *ᵥ v) i‖ = ‖∑ j, W i j * v j‖ := rfl
      _ ≤ ∑ j, ‖W i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖W i j‖ * ‖v j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖W i j‖) (fun j => ‖v j‖)
  calc ‖(W *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖W i j‖ * ‖v j‖) ^ 2 := by gcongr
    _ ≤ _ := h2

private lemma en_mulVec_le_opN_mul_en {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    en (W *ᵥ v) ≤ Data.opN W * en v := by
  by_cases hv : v = 0
  · subst hv
    simp [en_eq_sqrt, nsq, Matrix.mulVec_zero]
  · have hpos := en_pos hv
    have hF : 0 ≤ ∑ i, ∑ j, ‖W i j‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hC : ∀ u, en (W *ᵥ u) ≤ Real.sqrt (∑ i, ∑ j, ‖W i j‖ ^ 2) * en u := fun u =>
      en_le_of_nsq _ _ (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt hF]; exact nsq_mulVec_le_sum_norm_sq_mul_nsq W u)
    have hmem : en (W *ᵥ v) / en v ∈ {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        t = Real.sqrt (∑ i, ‖Matrix.mulVec W v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} :=
      ⟨v, hv, by rw [en_eq_sqrt, en_eq_sqrt]; rfl⟩
    have hbdd : BddAbove {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        t = Real.sqrt (∑ i, ‖Matrix.mulVec W v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
      refine ⟨Real.sqrt (∑ i, ∑ j, ‖W i j‖ ^ 2), ?_⟩
      rintro t ⟨u, hu, rfl⟩
      have h1 := hC u
      have hup := en_pos hu
      rw [en_eq_sqrt, en_eq_sqrt] at h1
      rw [en_eq_sqrt] at hup
      change Real.sqrt (nsq (W *ᵥ u)) / Real.sqrt (nsq u) ≤ _
      rw [div_le_iff₀ hup]
      exact h1
    have h2 := le_csSup hbdd hmem
    rw [div_le_iff₀ hpos] at h2
    unfold Data.opN
    exact h2

lemma graph_tau {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) (ho : X.IsOrtho x0) (τ : X.Ψ)
    (nτ : Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord) {η z : ℝ} (hη : 0 ≤ η) (hz : 0 ≤ z)
    (hZ1 : X.zN Z1 ≤ z) (hs : η * (1 + z) < 1)
    (hn : ∀ v, X.maj x0 τ ((nτ - 1) *ᵥ v) ≤ η ^ 2 * X.maj x0 τ v) :
    ∃ W : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ,
      Data.opN W ≤ (z + η * (1 + z)) / (1 - η * (1 + z)) ∧
      ∀ Z : X.Coord, Matrix.of (Z τ) = W →
        Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            col (nτ * (mat x0 τ * X.lowBlock Z1 τ)) (Fin.castLE X.p0_le a)) =
          Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le a)) := by
  have hker : ∀ c : Fin r → ℂ, mat x0 τ *ᵥ c = 0 → c = 0 := by
    intro c hMc
    have h0 : nsq c = nsq (0 : Fin r → ℂ) := by
      rw [← maj_ortho X ho τ c, ← maj_ortho X ho τ 0, hMc, Matrix.mulVec_zero]
    apply eq_zero_of_en c
    rw [en_eq_sqrt, h0]
    simp [nsq]
  have hMu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr fun h0 => by
    obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hc (hker c hMc)
  have hMMi : mat x0 τ * (mat x0 τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMu
  obtain ⟨N', hN'⟩ : ∃ N' : Matrix (Fin r) (Fin r) ℂ, N' = (mat x0 τ)⁻¹ * nτ * mat x0 τ :=
    ⟨_, rfl⟩
  have hMN : mat x0 τ * N' = nτ * mat x0 τ := by
    rw [hN', ← mul_assoc, ← mul_assoc, hMMi, one_mul]
  have hN1 : ∀ c, en ((N' - 1) *ᵥ c) ≤ η * en c := by
    intro c
    apply en_le_of_nsq _ _ hη
    have hMN1 : mat x0 τ * (N' - 1) = (nτ - 1) * mat x0 τ := by
      rw [mul_sub, mul_one, hMN, sub_mul, one_mul]
    rw [← maj_ortho X ho τ ((N' - 1) *ᵥ c), ← maj_ortho X ho τ c, Matrix.mulVec_mulVec, hMN1,
      ← Matrix.mulVec_mulVec]
    exact hn (mat x0 τ *ᵥ c)
  have hZτ : Data.opN (Matrix.of (Z1 τ)) ≤ z := by
    have hb : BddAbove (Set.range fun τ' : X.Ψ => Data.opN (Matrix.of (Z1 τ'))) :=
      (Set.finite_range _).bddAbove
    exact (le_ciSup hb τ).trans hZ1
  have hsplit : ∀ w : Fin r → ℂ, en w ≤ en (top X w) + en (bot X w) := by
    intro w
    rw [en_eq_sqrt w]
    calc Real.sqrt (nsq w) ≤ Real.sqrt ((en (top X w) + en (bot X w)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [nsq_split X w, ← en_sq (top X w), ← en_sq (bot X w)]
          nlinarith [mul_nonneg (en_nonneg (top X w)) (en_nonneg (bot X w))]
      _ = en (top X w) + en (bot X w) := Real.sqrt_sq (add_nonneg (en_nonneg _) (en_nonneg _))
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin r) (Fin r) ℂ, K = N' * X.lowBlock Z1 τ := ⟨_, rfl⟩
  have hyt : ∀ d, top X (X.lowBlock Z1 τ *ᵥ ext X d) = d := fun d => by
    rw [top_mulVec_ext, blkA_low, Matrix.one_mulVec]
  have hyb : ∀ d, bot X (X.lowBlock Z1 τ *ᵥ ext X d) = Matrix.of (Z1 τ) *ᵥ d := fun d => by
    rw [bot_mulVec_ext, blkB_low]
  have hyen : ∀ d, en (X.lowBlock Z1 τ *ᵥ ext X d) ≤ (1 + z) * en d := fun d => by
    have h1 := hsplit (X.lowBlock Z1 τ *ᵥ ext X d)
    rw [hyt, hyb] at h1
    have h2 := en_mulVec_le_opN_mul_en (Matrix.of (Z1 τ)) d
    have h3 := mul_le_mul_of_nonneg_right hZτ (en_nonneg d)
    linarith
  have hKd : ∀ d, K *ᵥ ext X d = X.lowBlock Z1 τ *ᵥ ext X d +
      (N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d) := fun d => by
    rw [hK, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hed : ∀ d, en ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) ≤ η * (1 + z) * en d :=
    fun d => by
      have h1 := hN1 (X.lowBlock Z1 τ *ᵥ ext X d)
      have h2 := mul_le_mul_of_nonneg_left (hyen d) hη
      nlinarith
  have htadd : ∀ u v : Fin r → ℂ, top X (u + v) = top X u + top X v := fun _ _ => rfl
  have hbadd : ∀ u v : Fin r → ℂ, bot X (u + v) = bot X u + bot X v := fun _ _ => rfl
  have hAe : ∀ d, blkA X K *ᵥ d = d + top X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) :=
    fun d => by rw [← top_mulVec_ext, hKd, htadd, hyt]
  have hBe : ∀ d, blkB X K *ᵥ d =
      Matrix.of (Z1 τ) *ᵥ d + bot X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) :=
    fun d => by rw [← bot_mulVec_ext, hKd, hbadd, hyb]
  have hs0 : 0 ≤ η * (1 + z) := mul_nonneg hη (by linarith)
  have hAl : ∀ d, (1 - η * (1 + z)) * en d ≤ en (blkA X K *ᵥ d) := fun d => by
    have h1 := en_top_le X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d))
    have h2 := hed d
    have hd : d = blkA X K *ᵥ d - top X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) := by
      rw [hAe d]
      abel
    have h3 := en_sub_le (blkA X K *ᵥ d) (top X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)))
    rw [← hd] at h3
    nlinarith
  have hBu : ∀ d, en (blkB X K *ᵥ d) ≤ (z + η * (1 + z)) * en d := fun d => by
    rw [hBe d]
    have h1 := en_add_le (Matrix.of (Z1 τ) *ᵥ d)
      (bot X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)))
    have h2 := en_mulVec_le_opN_mul_en (Matrix.of (Z1 τ)) d
    have h3 := mul_le_mul_of_nonneg_right hZτ (en_nonneg d)
    have h4 := en_bot_le X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d))
    have h5 := hed d
    nlinarith
  have h1s : 0 < 1 - η * (1 + z) := by linarith
  have hAu : IsUnit (blkA X K).det := isUnit_iff_ne_zero.mpr fun h0 => by
    obtain ⟨d, hd, hAd⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 := hAl d
    rw [hAd] at h1
    have h2 : en (0 : Fin X.p0 → ℂ) = 0 := by
      rw [en_eq_sqrt]
      simp [nsq]
    rw [h2] at h1
    have h3 := en_pos hd
    nlinarith [mul_pos h1s h3]
  refine ⟨blkB X K * (blkA X K)⁻¹, ?_, fun Z hZW => ?_⟩
  · apply opN_le _ (div_nonneg (by linarith) h1s.le)
    intro v
    have hAd : blkA X K *ᵥ ((blkA X K)⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
    have hWv : (blkB X K * (blkA X K)⁻¹) *ᵥ v = blkB X K *ᵥ ((blkA X K)⁻¹ *ᵥ v) := by
      rw [Matrix.mulVec_mulVec]
    rw [hWv]
    have hB := hBu ((blkA X K)⁻¹ *ᵥ v)
    have hA := hAl ((blkA X K)⁻¹ *ᵥ v)
    rw [hAd] at hA
    rw [div_mul_eq_mul_div, le_div_iff₀ h1s]
    have hzs : 0 ≤ z + η * (1 + z) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hA hzs, mul_le_mul_of_nonneg_left hB h1s.le]
  · have hMK : nτ * (mat x0 τ * X.lowBlock Z1 τ) = mat x0 τ * K := by
      rw [hK, ← mul_assoc (mat x0 τ), hMN, mul_assoc]
    have hcol : ∀ (i : Fin r) (a : Fin X.p0), K i (Fin.castLE X.p0_le a) =
        ∑ b, X.lowBlock Z τ i (Fin.castLE X.p0_le b) * blkA X K b a := by
      intro i a
      rcases fin_split X i with ⟨i', rfl⟩ | ⟨m, rfl⟩
      · have h1 : (blkA X (X.lowBlock Z τ) * blkA X K) i' a = blkA X K i' a := by
          rw [blkA_low, Matrix.one_mul]
        rw [Matrix.mul_apply] at h1
        exact h1.symm
      · have h2 : (blkB X (X.lowBlock Z τ) * blkA X K) m a = blkB X K m a := by
          rw [blkB_low, hZW, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
        rw [Matrix.mul_apply] at h2
        exact h2.symm
    refine span_cols_eq _ _ (blkA X K) hAu (fun a => ?_)
    funext i
    show col (nτ * (mat x0 τ * X.lowBlock Z1 τ)) (Fin.castLE X.p0_le a) i =
      (∑ b, blkA X K b a • col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le b)) i
    have lhs : col (mat x0 τ * K) (Fin.castLE X.p0_le a) i =
        ∑ b, ∑ k, mat x0 τ i k * (X.lowBlock Z τ k (Fin.castLE X.p0_le b) * blkA X K b a) := by
      show (mat x0 τ * K) i (Fin.castLE X.p0_le a) = _
      rw [Matrix.mul_apply]
      simp only [hcol, Finset.mul_sum]
      exact Finset.sum_comm
    have rhs : (∑ b, blkA X K b a • col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le b)) i =
        ∑ b, ∑ k, blkA X K b a * (mat x0 τ i k * X.lowBlock Z τ k (Fin.castLE X.p0_le b)) := by
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      show blkA X K b a * (mat x0 τ * X.lowBlock Z τ) i (Fin.castLE X.p0_le b) = _
      rw [Matrix.mul_apply, Finset.mul_sum]
    rw [hMK, lhs, rhs]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Frames

end

end UnipMove.GraphH

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem sGraph {E : Type} [Field E] [NumberField E] [IsCMField E] : SGraph E := by
  unfold SGraph
  intro r X x0 hx0 ho n Z1 η z hη hz hZ1 hs hn
  have hg := fun τ => GraphH.graph_tau X hx0 ho τ (n τ) Z1 hη hz hZ1 hs (hn τ)
  choose W hW1 hW2 using hg
  refine ⟨(fun τ => W τ : X.Coord), ?_, ?_⟩
  · intro τ
    exact hW2 τ (fun τ => W τ) rfl
  · unfold Data.zN
    apply Real.iSup_le
    · intro τ
      exact hW1 τ
    · have h1 : 0 ≤ η * (1 + z) := mul_nonneg hη (by linarith)
      apply div_nonneg
      · linarith
      · linarith

end UnipMove
