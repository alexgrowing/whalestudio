import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_minor {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) :
    ∃ a b : Fin r, u 0 a * u 1 b - u 0 b * u 1 a ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu0 : u 0 ≠ 0 := hu.ne_zero 0
  obtain ⟨a, ha⟩ : ∃ a, u 0 a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (funext h)
  have key := Fintype.linearIndependent_iff.1 hu ![u 1 a, -(u 0 a)] (by
    funext b
    have hb := hcon a b
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply]
    linear_combination -hb)
  exact ha (by simpa using key 1)

lemma emb_li {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) (τ : E →+* ℂ) (c : Fin 2 → ℂ)
    (hc : ∑ i, c i • Data.emb τ (u i) = 0) : c = 0 := by
  obtain ⟨a, b, hab⟩ := exists_minor hu
  have hd : τ (u 0 a * u 1 b - u 0 b * u 1 a) ≠ 0 := by
    rw [map_ne_zero_iff _ τ.injective]
    exact hab
  simp only [map_sub, map_mul] at hd
  have ea := congrFun hc a
  have eb := congrFun hc b
  simp only [Finset.sum_apply, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Data.emb,
    Pi.zero_apply] at ea eb
  have h0 : c 0 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 1 b) * ea - τ (u 1 a) * eb
  have h1 : c 1 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 0 a) * eb - τ (u 0 b) * ea
  have h0' := (mul_eq_zero.1 h0).resolve_right hd
  have h1' := (mul_eq_zero.1 h1).resolve_right hd
  funext i
  fin_cases i
  · simpa using h0'
  · simpa using h1'

variable (X : Data E r)

lemma uvec_ne {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) {a : X.Ψ → Fin 2 → ℂ} {τ : X.Ψ}
    (ha : a τ ≠ 0) : X.uvec u a τ ≠ 0 := fun h0 => ha (emb_li hu τ.1 (a τ) h0)

lemma hermC_uvec {u : Fin 2 → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (a b : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) = 0 := by
  have key : hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) =
      ∑ i, ∑ k, a τ i * conj (b τ k) * τ.1 (herm X.Gm (u i) (u k)) := by
    simp only [hermC, herm, Data.uvec, Data.emb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      map_sum, map_mul, emb_cc, Fin.sum_univ_two, map_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key]
  simp [hu]

lemma isIsoV_uvec {u : Fin 2 → Fin r → E} (hu : IsIsoPair X.Gm u) {a : X.Ψ → Fin 2 → ℂ}
    (ha : ∀ τ, a τ ≠ 0) : X.IsIsoV (X.uvec u a) := fun τ => ⟨hermC_uvec X hu.1 a a τ, uvec_ne X hu.2 (ha τ)⟩

lemma herm_rank1 (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    IsHermFam (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) := by
  intro τ i k
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma pairR_rank1 (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) = ∑ τ, s τ * (X.chiAt χ a τ).re := by
  unfold Data.pairR Data.chiAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma posSemidef_of {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) (τ0 : X.Ψ)
    (h : ∀ x : Fin 2 → ℂ, x ≠ 0 → 0 ≤ (∑ i, ∑ k, χ τ0 i k * conj (x i) * x k).re) :
    (Matrix.of (χ τ0)).PosSemidef := by
  have hH : (Matrix.of (χ τ0)).IsHermitian := by
    ext i k
    simp [Matrix.conjTranspose_apply, hχ τ0 k i]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x => ?_⟩
  have hre : (star x ⬝ᵥ (Matrix.of (χ τ0)).mulVec x) =
      ∑ i, ∑ k, χ τ0 i k * conj (x i) * x k := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [hre, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx]
    · exact h x hx
  · rw [← hre]
    exact him.symm

lemma chiAt_embH (β : Matrix (Fin 2) (Fin 2) E) (c : Fin 2 → E) (τ : X.Ψ) :
    X.chiAt (X.embH β) (fun σ i => σ.1 (c i)) τ = τ.1 (∑ i, ∑ k, β i k * c i * cc (c k)) := by
  simp only [Data.chiAt, Data.embH, map_sum, map_mul, emb_cc]

lemma herm_of_LZ {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, rfl⟩ := hb
  intro τ i k
  simp only [Data.embH]
  rw [← hβ i k, emb_cc]

lemma herm_comb {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, IsHermFam (ω j))
    (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]

end

end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
