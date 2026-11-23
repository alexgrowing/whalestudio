import Mathlib
import Formalism.SatakeDualWeyl.Statement
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.SkewDense

theorem exists_dual_coef (E : Type) [Field E] [NumberField E] [DecidableEq (E →+* ℂ)] :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → E) (a : (E →+* ℂ) → κ → ℂ),
      ∀ g₀ g : E →+* ℂ, ∑ k, a g₀ k * g (b k) = if g = g₀ then 1 else 0 := by
  classical
  let B := NumberField.canonicalEmbedding.latticeBasis E
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun k => NumberField.integralBasis E k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : E →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1
  exact ⟨_, inferInstance, b, a, ha⟩

theorem eq_zero_of_rat_comb {P G : Type} [Fintype G] (r : G → P → ℂ) (Q : MvPolynomial P ℂ)
    (hrat : ∀ t : G → ℚ, MvPolynomial.eval (fun p => ∑ g, (t g : ℂ) * r g p) Q = 0)
    (hspan : ∀ y : P → ℂ, ∃ z : G → ℂ, y = fun p => ∑ g, z g * r g p) : Q = 0 := by
  classical
  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p
    simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, map_zero]
  refine MvPolynomial.funext fun y => ?_
  obtain ⟨z, rfl⟩ := hspan y
  rw [← heval, hQ', map_zero, map_zero]

def gen {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (u v : Fin n) (x : E) : Matrix (Fin n) (Fin n) E :=
  Matrix.single u v x - Matrix.single v u (σ x)

theorem cT_gen {E : Type} [CommRing E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (u v : Fin n) (x : E) :
    Formalism.UG.cT σ (gen σ u v x) = -gen σ u v x := by
  ext i j
  simp only [Formalism.UG.cT, gen, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.single_apply, map_sub, apply_ite σ, map_zero, hσ, neg_sub, and_comm]

theorem sum_gen {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {κ : Type} [Fintype κ] (b : κ → E)
    (g : E →+* ℂ) (z : Fin n × Fin n × κ → ℂ) (i j : Fin n) :
    ∑ G : Fin n × Fin n × κ, z G * g (gen σ G.1 G.2.1 (b G.2.2) i j) =
      ∑ k, z (i, j, k) * g (b k) - ∑ k, z (j, i, k) * g (σ (b k)) := by
  have e : ∀ (f : Fin n → Fin n → κ → ℂ) (p q : Fin n),
      (∑ G : Fin n × Fin n × κ, if G.1 = p ∧ G.2.1 = q then f G.1 G.2.1 G.2.2 else 0) = ∑ k, f p q k := by
    intro f p q
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single p (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← e (fun u v k => z (u, v, k) * g (b k)) i j, ← e (fun u v k => z (u, v, k) * g (σ (b k))) j i,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [gen, Matrix.sub_apply, Matrix.single_apply, map_sub, apply_ite g, map_zero, mul_sub, mul_ite, mul_zero,
    and_comm]

theorem eq_zero_of_vanish_skew (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E) (_h2 : Module.finrank F E = 2)
    {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ))
    (hψ : Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)))
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0)
    (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) : Q = 0 := by
  classical
  set c : E →+* E := (σ : E →+* E) with hc
  have hcc : ∀ x, c (c x) = x := hσ
  obtain ⟨κ, _, b, a, ha⟩ := exists_dual_coef E
  have hU : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have hinj : ∀ τ τ₀, ψ τ = ψ τ₀ ↔ τ = τ₀ := fun τ τ₀ =>
    ⟨fun h => hψ (by simp only [h]), fun h => by rw [h]⟩
  have hne : ∀ τ τ₀, (ψ τ).comp c ≠ ψ τ₀ := by
    intro τ τ₀ h
    have h1 : τ = τ₀ := by
      apply hψ
      ext x
      have := DFunLike.congr_fun h (algebraMap F E x)
      simpa [hc] using this
    subst h1
    apply hσ1
    ext x
    exact (ψ τ).injective (DFunLike.congr_fun h x)
  let A : Fin n × Fin n × κ → Matrix (Fin n) (Fin n) E := fun G => gen c G.1 G.2.1 (b G.2.2)
  refine eq_zero_of_rat_comb (fun G p => ψ p.1 ((J⁻¹ * A G) p.2.1 p.2.2)) Q (fun t => ?_) (fun y => ?_)
  · have hA : Formalism.UG.cT c (∑ G, (t G : E) • A G) = -∑ G, (t G : E) • A G := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.neg_apply,
        Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun G _ => ?_
      have := congrFun (congrFun (cT_gen c hcc G.1 G.2.1 (b G.2.2)) i) j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at this
      simp only [A, this, mul_neg]
    have hJS : J * (J⁻¹ * ∑ G, (t G : E) • A G) = ∑ G, (t G : E) • A G :=
      Matrix.mul_nonsing_inv_cancel_left _ _ hU
    have h := hQ (J⁻¹ * ∑ G, (t G : E) • A G) (by
      have h1 : Formalism.UG.cT c (J⁻¹ * ∑ G, (t G : E) • A G) * J = -∑ G, (t G : E) • A G := by
        have h2 := Formalism.UG.cT_mul c J (J⁻¹ * ∑ G, (t G : E) • A G)
        rw [hJ, hJS, hA] at h2
        exact h2.symm
      rw [h1, hJS, neg_add_cancel])
    rw [← h]
    congr 2
    funext p
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul,
      map_ratCast]
  · let w : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => J.map (ψ τ) * Matrix.of fun i j => y (τ, i, j)
    let z : Fin n × Fin n × κ → ℂ := fun G => ∑ τ₀, w τ₀ G.1 G.2.1 * a (ψ τ₀) G.2.2
    have key : ∀ (g : E →+* ℂ) u v, ∑ k, z (u, v, k) * g (b k) =
        ∑ τ₀, w τ₀ u v * if g = ψ τ₀ then 1 else 0 := by
      intro g u v
      simp only [z, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ₀ _ => ?_
      rw [← ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hw : ∀ τ i j, ∑ G, z G * ψ τ (A G i j) = w τ i j := by
      intro τ i j
      have k2 := key ((ψ τ).comp c) j i
      simp only [RingHom.comp_apply, hne, if_false, mul_zero, Finset.sum_const_zero] at k2
      rw [sum_gen, key, k2]
      simp [hinj]
    refine ⟨z, ?_⟩
    funext ⟨τ, i, j⟩
    have e1 : (J⁻¹).map (ψ τ) * w τ = Matrix.of fun i j => y (τ, i, j) := by
      simp only [w]
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hU,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.of_apply, Matrix.mul_apply] at e2
    rw [← e2]
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply, ← hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun l _ => ?_
    ring

end GlobalTheory.SkewDense
