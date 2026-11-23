import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section gram

variable (X : Data E r)

def hv (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Fin r → ℂ :=
  fun a => hermC τ.1 X.Gm (col M a) (Data.emb τ.1 ξ)

def rk1 (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  vecMulVec (hv X ξ τ M) (fun b => conj (hv X ξ τ M b))

lemma col_mul (A M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * M) a = A *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma hermC_add_smul_add_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u e v : Fin r → ℂ)
    (β γ : ℂ) :
    hermC τ G (u + β • e) (v + γ • e) = hermC τ G u v + conj γ * hermC τ G u e +
      β * hermC τ G e v + β * conj γ * hermC τ G e e := by
  simp only [hermC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma hermC_swap_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc', hG]
  ring

lemma hermC_pair (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (e u v : Fin r → ℂ) (he : hermC τ G e e = 0) (α : ℂ) :
    hermC τ G (u + (α * hermC τ G u e) • e) (v + (α * hermC τ G v e) • e) =
      hermC τ G u v + (α + conj α) * hermC τ G u e * conj (hermC τ G v e) := by
  rw [hermC_add_smul_add_smul, hermC_swap_of_conj_symm τ G hG v e, he]
  simp only [map_mul]
  ring

lemma alpha_conj (c : ℝ) (s : ℂ) :
    (-(I * (c : ℂ) * s)) + conj (-(I * (c : ℂ) * s)) = ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private lemma hermC_emb_emb_eq_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc']

lemma gram_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  have he : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_herm, hξ, map_zero]
  ext a b
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1, hv,
    vecMulVec_apply]
  rw [col_mul, col_mul, flowMat_mulVec (X := X), flowMat_mulVec (X := X),
    hermC_pair τ.1 X.Gm X.Gm_herm _ _ _ he, alpha_conj]
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

def admissibleImaginary (ξ : Fin r → E) (x : Frame X.Ψ r) : Set (X.Ψ → ℝ) :=
  {y | ∀ τ : X.Ψ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i *
    (lminor (gram τ.1 X.Gm (mat x τ) + ((2 * X.c τ * y τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re}

lemma flow_mem_dom_iff {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) :
    X.flow ξ s x ∈ X.dom ↔ (fun τ => (s τ).im) ∈ admissibleImaginary X ξ x := by
  simp only [Data.dom, GG, Set.mem_setOf_eq, admissibleImaginary, dmin, mat_flow, gram_flowMat X hξ, det_mul,
    det_flowMat (X := X) hξ, one_mul]
  constructor
  · intro h τ i
    exact (h τ).2 i
  · intro h τ
    exact ⟨(hx τ).1, h τ⟩

end gram

section affine

lemma leadingMinor_add_rankOne (A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) (i : Fin (r + 1))
    (hA : lminor A i ≠ 0) : ∃ κ : ℂ, ∀ t : ℂ, lminor (A + t • vecMulVec u v) i = lminor A i * (1 + t * κ) := by
  unfold lminor at hA ⊢
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  set B := A.submatrix e e with hB
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨(v ∘ e) ⬝ᵥ (B⁻¹ *ᵥ (u ∘ e)), fun t => ?_⟩
  have hz : B *ᵥ (B⁻¹ *ᵥ (u ∘ e)) = u ∘ e := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hB', one_mulVec]
  have key : B * (1 + vecMulVec (B⁻¹ *ᵥ (u ∘ e)) (t • (v ∘ e))) =
      (A + t • vecMulVec u v).submatrix e e := by
    rw [mul_add, mul_one]
    ext a b
    have hza : ∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k = u (e a) := congrFun hz a
    simp only [Matrix.add_apply, Matrix.mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rw [show ∑ k, B a k * ((B⁻¹ *ᵥ (u ∘ e)) k * (t * v (e b))) =
        (∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k) * (t * v (e b)) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring, hza]
    simp only [hB, Matrix.submatrix_apply]
    ring
  rw [← key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    smul_eq_mul]

lemma open_convex_aff {ι κ : Type*} [Fintype ι] [Finite κ] (a b : ι → κ → ℝ) :
    IsOpen {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} ∧
      Convex ℝ {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  constructor
  · have hs : {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} =
        ⋂ τ, ⋂ i, {y : ι → ℝ | 0 < a τ i + y τ * b τ i} := by
      ext y
      simp
    rw [hs]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.add ((continuous_apply τ).mul continuous_const))
  · intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hz ⊢
    intro τ i
    have h1 := hy τ i
    have h2 := hz τ i
    have key : a τ i + (s * y τ + t * z τ) * b τ i =
        s * (a τ i + y τ * b τ i) + t * (a τ i + z τ * b τ i) := by
      linear_combination (-(a τ i)) * hst
    rw [key]
    rcases hs.lt_or_eq with hs' | hs'
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' h1) (mul_nonneg ht h2.le)
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using h2

end affine

section adm

variable (X : Data E r)

lemma admissibleImaginary_eq_halfspaces {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    ∃ a b : X.Ψ → Fin (r + 1) → ℝ, admissibleImaginary X ξ x = {y | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  have hL : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), lminor (gram τ.1 X.Gm (mat x τ)) i ≠ 0 := by
    intro τ i h
    have h1 := (hx τ).2 i
    simp only [dmin, h, Complex.zero_re, mul_zero, lt_irrefl] at h1
  have hk : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), ∃ κ : ℂ, ∀ t : ℂ,
      lminor (gram τ.1 X.Gm (mat x τ) + t • rk1 X ξ τ (mat x τ)) i =
        lminor (gram τ.1 X.Gm (mat x τ)) i * (1 + t * κ) :=
    fun τ i => leadingMinor_add_rankOne _ _ _ i (hL τ i)
  choose κ hκ using hk
  have hre : ∀ (L k : ℂ) (t : ℝ), (L * (1 + (t : ℂ) * k)).re = L.re + t * (L * k).re := by
    intro L k t
    rw [show L * (1 + (t : ℂ) * k) = L + (t : ℂ) * (L * k) by ring, Complex.add_re,
      Complex.re_ofReal_mul]
  refine ⟨fun τ i => psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ)) i).re,
    fun τ i => psgn X.p0 i * (2 * X.c τ) * (lminor (gram τ.1 X.Gm (mat x τ)) i * κ τ i).re, ?_⟩
  ext y
  simp only [admissibleImaginary, Set.mem_setOf_eq, hκ, hre]
  refine forall_congr' fun τ => forall_congr' fun i => ?_
  apply iff_of_eq
  congr 1
  ring

lemma admissibleImaginary_open_convex {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    IsOpen (admissibleImaginary X ξ x) ∧ Convex ℝ (admissibleImaginary X ξ x) := by
  obtain ⟨a, b, h⟩ := admissibleImaginary_eq_halfspaces X (ξ := ξ) x hx
  rw [h]
  exact open_convex_aff a b

end adm

end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
