import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace IntegralBasisReduction

open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum4_lemma {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm

private lemma hermC_mulVec_lemma_2 {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (Y : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    hermC τ G (Y *ᵥ u) (Y *ᵥ v) = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
  calc hermC τ G (Y *ᵥ u) (Y *ᵥ v)
      = ∑ a, ∑ b, ∑ i, ∑ j, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := by
        simp only [hermC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
    _ = ∑ i, ∑ j, ∑ a, ∑ b, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := sum4_lemma _
    _ = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [gram, hermC, col, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

theorem hermC_normal {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0) (s : Fin r → ℂ)
    (hg : gram τ X.Gm Y = diagonal s) (p q : Fin r → ℂ) :
    hermC τ X.Gm p q = ∑ a, s a * (Y⁻¹ *ᵥ p) a * conj ((Y⁻¹ *ᵥ q) a) := by
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have key := hermC_mulVec_lemma_2 τ X.Gm Y (Y⁻¹ *ᵥ p) (Y⁻¹ *ᵥ q)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec, hg] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

def IsNormal (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, (y τ).det ≠ 0 ∧ gram τ.1 X.Gm (y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

theorem ip_Sg {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (p q : Fin r → E) :
    ip X (Ly X y (X.embV p)) (Sg X (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm X.Gm p q)).re := by
  simp only [ip, Sg, Ly, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hdet, hg⟩ := hy τ
  have hτ : τ.1 (herm X.Gm p q) = hermC τ.1 X.Gm (X.embV p τ) (X.embV q τ) := by
    first
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [hτ, hermC_normal X hdet _ hg]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def zbas {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Basis ι ℝ (X.Ψ → Fin r → ℂ) :=
  (Basis.mk (RealPlaceEmbeddings.linIndR X g) (RealPlaceEmbeddings.span_embV X g).ge).map
    (LinearEquiv.ofBijective (Ly X y) ⟨Ly_injective X y fun τ => (hy τ).1,
      Ly_surjective X y fun τ => (hy τ).1⟩)

theorem zbas_apply {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ)
    (i : ι) : zbas X hy g i = Ly X y (X.embV (g i : Fin r → E)) := by
  simp only [zbas, Basis.map_apply, Basis.mk_apply]
  exact LinearEquiv.ofBijective_apply _ _

private lemma ip_sum_lemma_3 (u : X.Ψ → Fin r → ℂ) (a : ι → ℝ) (w : ι → X.Ψ → Fin r → ℂ) :
    ip X u (∑ k, a k • w k) = ∑ k, a k * ip X u (w k) := by
  have h1 : ∀ τ b, u τ b * conj ((∑ k, a k • w k) τ b) =
      ∑ k, ((a k : ℂ) * (u τ b * conj (w k τ b))) := by
    intro τ b
    rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  simp only [ip, h1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  calc ∑ τ, ∑ b, ∑ k, X.c τ * (a k * (u τ b * conj (w k τ b)).re)
      = ∑ τ, ∑ k, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) :=
        Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = ∑ k, ∑ τ, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem Bm_eq {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Bm X g = Am X y g * LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) := by
  ext i j
  rw [Matrix.mul_apply]
  have hS := (zbas X hy g).sum_repr (Sg X (zbas X hy g j))
  simp only [LinearMap.toMatrix_apply]
  rw [show Bm X g i j = ip X (zbas X hy g i) (Sg X (zbas X hy g j)) by
    simp only [Bm, Matrix.of_apply, zbas_apply]
    exact (ip_Sg X hy _ _).symm]
  conv_lhs => rw [← hS]
  rw [ip_sum_lemma_3]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Am, Matrix.of_apply, zbas_apply]
  ring

theorem det_Am_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    (Am X y g).det ≤ |(Bm X g).det| := by
  have hSS : Sg X * Sg X = 1 := by
    refine LinearMap.ext fun u => funext fun τ => funext fun a => ?_
    show ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a) = u τ a
    rw [← mul_assoc, ← Complex.ofReal_mul]
    unfold sgn
    split_ifs <;> simp
  have hM : LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) *
      LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) = 1 := by
    rw [← LinearMap.toMatrix_mul, hSS, LinearMap.toMatrix_one]
  have h2 : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| *
      |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rw [← abs_mul, ← Matrix.det_mul, hM, Matrix.det_one, abs_one]
  have hd : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [abs_nonneg (LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det]
  rw [Bm_eq X hy g, Matrix.det_mul, abs_mul, hd, mul_one]
  exact le_abs_self _

theorem reduce {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ v ∈ X.Λ, v ≠ 0 → m ≤ Qy X y v) :
    ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      (∀ i, Qy X y (f i) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
        |(Bm X (RealPlaceEmbeddings.zb X)).det| / m ^ (finrank ℤ X.Λ - 1)) ∧
      ∀ (v : X.Λ) (i : Fin (finrank ℤ X.Λ)),
        ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ (finrank ℤ X.Λ) * Qy X y v / m := by
  set g := RealPlaceEmbeddings.zb X with hgdef
  have hcoe : ∀ x : Fin (finrank ℤ X.Λ) → ℤ,
      ((∑ i, x i • g i : X.Λ) : Fin r → E) = ∑ i, x i • (g i : Fin r → E) := by
    intro x; simp
  have hint : ∀ x : Fin (finrank ℤ X.Λ) → ℤ, x ≠ 0 →
      m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) := by
    intro x hx
    rw [quad_int]
    refine hmin _ ?_ ?_
    · rw [← hcoe]; exact (∑ i, x i • g i : X.Λ).2
    · intro h0
      rw [← hcoe] at h0
      have h1 : (∑ i, x i • g i : X.Λ) = 0 := Subtype.ext h0
      exact hx (funext (Fintype.linearIndependent_iff.mp g.linearIndependent x h1))
  obtain ⟨eb, h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds (finrank ℤ X.Λ) (Am X y g) m
    |(Bm X g).det| (Am_posDef X y (fun τ => (hy τ).1) g) hm hint (det_Am_le X hy g)
  refine ⟨eb.map g.equivFun.symm, fun i => ?_, fun v i => ?_⟩
  · have h3 := h1 i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.equivFun_symm_apply] using h3
  · have h3 := h2 (g.equivFun v) i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.map_repr, Basis.equivFun_symm_apply, g.sum_repr] using h3

end IntegralBasisReduction

end ReciprocityTheory.ChartRestriction.G.FD
