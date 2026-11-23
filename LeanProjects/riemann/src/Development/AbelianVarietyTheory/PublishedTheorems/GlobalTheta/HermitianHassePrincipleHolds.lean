import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass

namespace GlobalTheory.HermGlobal

section Defs

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

noncomputable abbrev baseConj (σ : E ≃ₐ[F] E) (A : Type*) [CommRing A] [Algebra F A] :
    A ⊗[F] E →ₐ[A] A ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id A A) σ.toAlgHom

def CongrOver (σ : E ≃ₐ[F] E) (A : Type*) [CommRing A] [Algebra F A] {r : ℕ}
    (G G' : Matrix (Fin r) (Fin r) E) : Prop :=
  ∃ P : Matrix (Fin r) (Fin r) (A ⊗[F] E), IsUnit P.det ∧
    G'.map (fun x => (1 : A) ⊗ₜ[F] x) =
      Pᵀ * G.map (fun x => (1 : A) ⊗ₜ[F] x) * P.map (baseConj σ A)

variable {σ : E ≃ₐ[F] E} {A : Type*} [CommRing A] [Algebra F A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}

theorem CongrOver.of_congr
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) :
    CongrOver σ A G G' := by
  obtain ⟨P, hP, rfl⟩ := h
  let ι : E →+* A ⊗[F] E := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨P.map ι, ?_, ?_⟩
  · rw [show (P.map ι).det = ι P.det from (RingHom.map_det ι P).symm]
    exact hP.isUnit.map ι
  · change (Pᵀ * G * P.map σ).map ι = (P.map ι)ᵀ * G.map ι * _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rfl

theorem CongrOver.det_norm (hd' : G'.det ≠ 0) (h : CongrOver σ A G G') :
    ∃ z : A ⊗[F] E, (1 : A) ⊗ₜ[F] (G.det / G'.det) = z * baseConj σ A z := by
  obtain ⟨P, ⟨p, hp⟩, h⟩ := h
  let ι : E →+* A ⊗[F] E := Algebra.TensorProduct.includeRight.toRingHom
  have h1 : ι G'.det = p * ι G.det * baseConj σ A p := by
    rw [RingHom.map_det, RingHom.map_det, hp, AlgHom.map_det, ← Matrix.det_transpose P,
      ← Matrix.det_mul, ← Matrix.det_mul]
    exact congrArg Matrix.det h
  have h2 : ι (G.det / G'.det) * ι G'.det = ι G.det := by rw [← map_mul, div_mul_cancel₀ _ hd']
  have h3 : baseConj σ A p * baseConj σ A (p⁻¹ : (A ⊗[F] E)ˣ) = 1 := by
    rw [← map_mul, p.mul_inv, map_one]
  refine ⟨(p⁻¹ : (A ⊗[F] E)ˣ), ?_⟩
  change ι (G.det / G'.det) = _
  refine ((hd'.isUnit.map ι).mul_left_inj).1 ?_
  rw [h2, h1]
  linear_combination (-ι G.det) * p.mul_inv - (p * (p⁻¹ : (A ⊗[F] E)ˣ) * ι G.det) * h3

theorem CongrOver.complex (h : CongrOver σ A G G') (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = conj (τ x))
    (ψ : A →+* ℂ) (hψ : ∀ a, conj (ψ a) = ψ a)
    (hψτ : ∀ s : F, ψ (algebraMap F A s) = τ (algebraMap F E s)) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  obtain ⟨P, hP, h⟩ := h
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let ψ' : A →ₐ[F] ℂ := { ψ with commutes' := hψτ }
  let τ' : E →ₐ[F] ℂ := { τ with commutes' := fun _ => rfl }
  let Φ : A ⊗[F] E →+* ℂ := (Algebra.TensorProduct.productMap ψ' τ').toRingHom
  have hΦ : ∀ (a : A) (x : E), Φ (a ⊗ₜ[F] x) = ψ a * τ x := fun a x =>
    Algebra.TensorProduct.productMap_apply_tmul ψ' τ' a x
  have hc : ∀ z, Φ (baseConj σ A z) = conj (Φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, hΦ, hΦ, map_mul, hψ, ← hτ]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have e : ∀ M : Matrix (Fin r) (Fin r) E, (M.map fun x => (1 : A) ⊗ₜ[F] x).map Φ = M.map τ := by
    intro M
    ext a b
    simp [hΦ]
  refine ⟨P.map Φ, ?_, ?_⟩
  · rw [show (P.map Φ).det = Φ P.det from (RingHom.map_det Φ P).symm]
    exact (hP.map Φ).ne_zero
  · rw [← e, h, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, e]
    congr 1
    ext a b
    exact hc _

end Defs

section Quadratic

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem involutive_and_fixed [Algebra.IsQuadraticExtension F E] {σ : E ≃ₐ[F] E} (hσ : σ ≠ 1) :
    (∀ t, σ (σ t) = t) ∧ (∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) ∧
      ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ := by
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm ?_ ?_
    · rw [← Algebra.IsQuadraticExtension.finrank_eq_two F E]
      simpa using AlgEquiv.card_le (F := F) (K := E)
    · have : Nontrivial (E ≃ₐ[F] E) := ⟨σ, 1, hσ⟩
      exact Finite.one_lt_card
  have : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E
    (hcard.trans (Algebra.IsQuadraticExtension.finrank_eq_two F E).symm)
  obtain ⟨τ, -, hτ⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  have hall : ∀ ρ : E ≃ₐ[F] E, ρ = 1 ∨ ρ = σ := fun ρ => by
    by_cases h : ρ = 1
    · exact Or.inl h
    · exact Or.inr ((hτ ρ h).trans (hτ σ hσ).symm)
  have hc : ∀ t, σ (σ t) = t := fun t => by
    rcases hall (σ * σ) with h | h
    · exact DFunLike.congr_fun h t
    · exact absurd (by simpa using h) hσ
  obtain ⟨u, hu⟩ : ∃ u : E, σ u ≠ u := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  refine ⟨hc, fun t => ⟨fun h => ?_, ?_⟩, u - σ u, sub_ne_zero.2 hu.symm, ?_⟩
  · refine (IsGalois.mem_range_algebraMap_iff_fixed t).2 fun ρ => ?_
    rcases hall ρ with rfl | rfl
    · rfl
    · exact h
  · rintro ⟨s, rfl⟩
    exact σ.commutes s
  · rw [map_sub, hc, neg_sub]

variable {σ : E ≃ₐ[F] E}

theorem exists_coord [CharZero E] (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    (x : E) : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  obtain ⟨a, ha⟩ := (hF ((x + σ x) / 2)).1 (by rw [map_div₀, map_add, hc, map_ofNat, add_comm])
  obtain ⟨b, hb⟩ := (hF ((x - σ x) / (2 * θ))).1 (by
    rw [map_div₀, map_sub, hc, map_mul, map_ofNat, hθ]
    field_simp
    ring)
  refine ⟨a, b, ?_⟩
  rw [ha, hb]
  field_simp
  ring

theorem CongrOver.exists_sq_sub [CharZero E] (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    {d : F} (hd : algebraMap F E d = θ * θ) {A : Type*} [Field A] [Algebra F A] {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hd' : G'.det ≠ 0) (h : CongrOver σ A G G') {a : F}
    (ha : algebraMap F E a = G.det / G'.det) :
    ∃ p q : A, algebraMap F A a = p ^ 2 - algebraMap F A d * q ^ 2 := by
  obtain ⟨z, hz⟩ := h.det_norm hd'
  have hs : ∀ s : F, (1 : A) ⊗ₜ[F] algebraMap F E s = algebraMap A (A ⊗[F] E) (algebraMap F A s) := by
    intro s
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.algebraMap_apply' s).symm
  obtain ⟨p, q, rfl⟩ : ∃ p q : A, z = algebraMap A _ p + algebraMap A _ q * (1 : A) ⊗ₜ[F] θ := by
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul u x =>
      obtain ⟨s, t, rfl⟩ := exists_coord hc hF h0 hθ x
      refine ⟨u * algebraMap F A s, u * algebraMap F A t, ?_⟩
      rw [map_mul, map_mul, ← hs, ← hs]
      simp [TensorProduct.tmul_add]
    | add x y hx hy =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨p', q', rfl⟩ := hy
      exact ⟨p + p', q + q', by simp only [map_add]; ring⟩
  refine ⟨p, q, (algebraMap A (A ⊗[F] E)).injective ?_⟩
  have h1 : baseConj σ A ((1 : A) ⊗ₜ[F] θ) = -((1 : A) ⊗ₜ[F] θ) := by
    rw [Algebra.TensorProduct.map_tmul, ← TensorProduct.tmul_neg, ← hθ]
    rfl
  have h2 : algebraMap A (A ⊗[F] E) (algebraMap F A d) = (1 : A) ⊗ₜ[F] θ * (1 : A) ⊗ₜ[F] θ := by
    rw [← hs, hd, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← hs, ha, hz, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, h1, map_sub, map_mul,
    map_pow, map_pow, h2]
  ring

end Quadratic

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E}

theorem exists_embedding_conj (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    {d : F} (hd : algebraMap F E d = θ * θ) (ρ : F →+* ℝ) (hρ : ρ d < 0) :
    ∃ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) ∧ ∀ s : F, τ (algebraMap F E s) = (ρ s : ℂ) := by
  let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
  have hτ : ∀ s : F, τ (algebraMap F E s) = (ρ s : ℂ) := fun s =>
    ComplexEmbedding.lift_algebraMap_apply E _ s
  have h1 : τ θ * τ θ = (ρ d : ℂ) := by rw [← map_mul, ← hd, hτ]
  have h2 := congrArg Complex.re h1
  have h3 := congrArg Complex.im h1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h2 h3
  have h4 : (τ θ).re = 0 := by
    by_contra hne
    have : (τ θ).im = 0 := by
      have : (τ θ).re * (τ θ).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at h2
    nlinarith [mul_self_nonneg (τ θ).re]
  have h5 : conj (τ θ) = -τ θ := by
    apply Complex.ext <;> simp [h4]
  refine ⟨τ, fun x => ?_, hτ⟩
  obtain ⟨a, b, rfl⟩ := exists_coord hc hF h0 hθ x
  simp only [map_add, map_mul, AlgEquiv.commutes, hθ, map_neg, hτ, Complex.conj_ofReal, h5]

theorem exists_represent (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    {r : ℕ} (hr : 2 ≤ r) {g : Fin r → E}
    (hg : ∀ i, σ (g i) = g i) (hg0 : ∀ i, g i ≠ 0) {b : E} (hb : σ b = b) (hb0 : b ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) → ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ b).re)) :
    ∃ z : Fin r → E, z ⬝ᵥ Matrix.diagonal g *ᵥ ((σ : E →+* E) ∘ z) = b := by
  obtain ⟨d, hd⟩ := (hF (θ * θ)).1 (by rw [map_mul, hθ]; ring)
  choose γ hγ' using fun i => (hF (g i)).1 (hg i)
  obtain ⟨κ, hκ'⟩ := (hF b).1 hb
  have hγ : ∀ i, γ i ≠ 0 := fun i h => hg0 i (by rw [← hγ', h, map_zero])
  have hκ : κ ≠ 0 := fun h => hb0 (by rw [← hκ', h, map_zero])
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hd, h, map_zero])
  let a : Option (Fin r ⊕ Fin r) → F := fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)
  have ha : ∀ o, a o ≠ 0 := by
    rintro (_ | i | i)
    · exact neg_ne_zero.mpr hκ
    · exact hγ i
    · exact mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)
  obtain ⟨x, hx, hx0⟩ := isotropic_of_indefinite GlobalTheory.QNorm.hasseNormSt F a (by simp; omega) ha (by
    intro ρ
    rcases lt_or_gt_of_ne ((map_ne_zero ρ).2 hd0) with hρ | hρ
    · obtain ⟨τ, hτ, hτρ⟩ := exists_embedding_conj hc hF h0 hθ hd ρ hρ
      obtain ⟨i, hi⟩ := hs τ hτ
      rw [← hγ', ← hκ', hτρ, hτρ, Complex.ofReal_re, Complex.ofReal_re] at hi
      have n1 : ρ (γ i) ≠ 0 := (map_ne_zero ρ).mpr (hγ i)
      rcases lt_or_gt_of_ne ((map_ne_zero ρ).mpr hκ) with h | h
      · refine ⟨some (Sum.inl i), none, ?_, ?_⟩
        · exact lt_of_le_of_ne (not_lt.mp fun h' => absurd (hi.mp h') h.not_gt) n1
        · simpa [a] using h
      · refine ⟨none, some (Sum.inl i), ?_, hi.mpr h⟩
        simpa [a] using h
    · let i : Fin r := ⟨0, by omega⟩
      have e : ρ (a (some (Sum.inr i))) = -(ρ d * ρ (γ i)) := by simp [a]
      rcases lt_or_gt_of_ne ((map_ne_zero ρ).mpr (hγ i)) with h | h
      · exact ⟨some (Sum.inl i), some (Sum.inr i), h, by rw [e]; nlinarith⟩
      · exact ⟨some (Sum.inr i), some (Sum.inl i), by rw [e]; nlinarith, h⟩)
  obtain ⟨w, hw, hw0⟩ := exists_zero_coord_ne_zero ha hx hx0 none
  rw [Fintype.sum_option, Fintype.sum_sum_type] at hw0
  have hw1 := congrArg (algebraMap F E) hw0
  have hw2 : algebraMap F E (w none) ≠ 0 := (map_ne_zero _).2 hw
  simp only [a, Option.elim, Sum.elim_inl, Sum.elim_inr, map_add, map_mul, map_neg, map_pow, map_sum,
    hγ', hκ', hd, map_zero] at hw1
  refine ⟨fun i => (algebraMap F E (w (some (Sum.inl i))) +
    algebraMap F E (w (some (Sum.inr i))) * θ) / algebraMap F E (w none), ?_⟩
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, map_div₀, map_add, map_mul,
    RingHom.coe_coe, AlgEquiv.commutes, hθ]
  have : ∀ i, (algebraMap F E (w (some (Sum.inl i))) + algebraMap F E (w (some (Sum.inr i))) * θ) /
      algebraMap F E (w none) * (g i * ((algebraMap F E (w (some (Sum.inl i))) +
        algebraMap F E (w (some (Sum.inr i))) * -θ) / algebraMap F E (w none))) =
      (g i * algebraMap F E (w (some (Sum.inl i))) ^ 2 +
        -(θ * θ) * g i * algebraMap F E (w (some (Sum.inr i))) ^ 2) /
          algebraMap F E (w none) ^ 2 := by
    intro i
    field_simp
    ring
  simp only [this, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [div_eq_iff (pow_ne_zero 2 hw2)]
  linear_combination hw1

omit [NumberField F] [NumberField E] in

theorem posIndex_of_congr {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = conj (τ x)) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (h : Congr (σ : E →+* E) G G') :
    GlobalTheory.Inertia.posIndex (G'.map τ) = GlobalTheory.Inertia.posIndex (G.map τ) := by
  obtain ⟨P, hP, rfl⟩ := h
  have h : (P.map (σ : E →+* E)).map τ = (P.map τ).map conj := by
    ext a b
    exact hτ _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, h, GlobalTheory.Inertia.posIndex_congr]
  rw [show (P.map τ).det = τ P.det from (RingHom.map_det τ P).symm]
  exact (map_ne_zero τ).2 hP

theorem congr_diagonal (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ)
    (r : ℕ) : ∀ g g' : Fin r → E,
    (∀ i, σ (g i) = g i) → (∀ i, σ (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∀ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) → posCount τ g = posCount τ g') →
    (∃ x : E, ∏ i, g i = x * σ x * ∏ i, g' i) →
    Congr (σ : E →+* E) (Matrix.diagonal g) (Matrix.diagonal g') := by
  induction r with
  | zero =>
    intro g g' _ _ _ _ _ _
    exact ⟨1, by simp, Subsingleton.elim _ _⟩
  | succ r ih =>
    intro g g' hg hg' h0 h0' hs ⟨x, hx⟩
    obtain ⟨z, hz⟩ : ∃ z : Fin (r + 1) → E,
        z ⬝ᵥ Matrix.diagonal g *ᵥ ((σ : E →+* E) ∘ z) = g' 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact h0 0 (by simpa using hx)
        have hx1 : σ x ≠ 0 := (map_ne_zero σ).2 hx0
        refine ⟨fun _ => x⁻¹, ?_⟩
        simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, map_inv₀,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hx, RingHom.coe_coe]
        field_simp
      · exact exists_represent hc hF hθ0 hθ (by omega) hg h0 (hg' 0) (h0' 0)
          fun τ hτ => exists_sign_iff τ (hs τ hτ) 0
    have hG : ∀ a b, (σ : E →+* E) (Matrix.diagonal g a b) = Matrix.diagonal g b a := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simpa using hg a
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
    obtain ⟨P, k, hP, hPk, hk, hk0, -, hk1⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal_col_eq (c := (σ : E →+* E)) two_ne_zero hc hG (x := z)
        (hz ▸ h0' 0) 0
    have hp : ∏ i, g i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0 i
    have hk0 := hk0 (by rwa [Matrix.det_diagonal])
    have hcg : Congr (σ : E →+* E) (Matrix.diagonal g) (Matrix.diagonal k) := ⟨P, hP, hPk.symm⟩
    have hk2 : k 0 = g' 0 := hk1.trans hz
    refine hcg.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _)
      (fun i => hk0 _) (fun i => h0' _) (fun τ hτ => ?_) ?_))
    · have h1 := posIndex_of_congr hτ hcg
      rw [posIndex_diagonal_map, posIndex_diagonal_map, hs τ hτ, posCount_succ, posCount_succ τ g',
        hk2] at h1
      exact Nat.add_left_cancel h1
    · obtain ⟨y, -, hy⟩ := hcg.det
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ,
        hk2] at hy
      refine ⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩
      rw [hy, map_mul, RingHom.coe_coe]
      ring

variable [Algebra.IsQuadraticExtension F E] {r : ℕ} {G G' : Matrix (Fin r) (Fin r) E}

theorem congr_of_invariants (hσ : σ ≠ 1) (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) →
      GlobalTheory.Inertia.posIndex (G.map τ) = GlobalTheory.Inertia.posIndex (G'.map τ))
    (hn : ∃ x : E, G.det / G'.det = x * σ x) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ := by
  obtain ⟨hc, hF, θ, h0, hθ⟩ := involutive_and_fixed hσ
  obtain ⟨x, hx⟩ := hn
  obtain ⟨P, g, hP, hPg, hg, hg0⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hc (G := G) hG
  obtain ⟨P', g', hP', hPg', hg', hg0'⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hc (G := G') hG'
  have h1 : Congr (σ : E →+* E) G (Matrix.diagonal g) := ⟨P, hP, hPg.symm⟩
  have h1' : Congr (σ : E →+* E) G' (Matrix.diagonal g') := ⟨P', hP', hPg'.symm⟩
  refine (h1.trans (congr_diagonal hc hF h0 hθ r g g' hg hg' (hg0 hd) (hg0' hd')
    (fun τ hτ => ?_) ?_)).trans h1'.symm
  · rw [← posIndex_diagonal_map, ← posIndex_diagonal_map, posIndex_of_congr hτ h1,
      posIndex_of_congr hτ h1', hs τ hτ]
  · obtain ⟨y, -, hy⟩ := h1.det
    obtain ⟨y', -, hy'⟩ := h1'.symm.det
    rw [div_eq_iff hd'] at hx
    rw [Matrix.det_diagonal] at hy hy'
    refine ⟨y * x * y', ?_⟩
    rw [hy, hx, hy']
    simp only [map_mul, RingHom.coe_coe]
    ring

omit [NumberField F] in

theorem exists_real_extension (ρ : F →+* ℝ) :
    ∃ (v : InfinitePlace F) (φ : v.Completion →+* ℝ), ∀ s : F, φ (algebraMap F _ s) = ρ s := by
  have hρ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp ρ) :=
    ComplexEmbedding.isReal_iff.2 (by ext x; simp)
  have hv : (InfinitePlace.mk (Complex.ofRealHom.comp ρ)).IsReal := ⟨_, hρ, rfl⟩
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hv, fun s => ?_⟩
  apply Complex.ofReal_injective
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe
    (InfinitePlace.mk (Complex.ofRealHom.comp ρ)) ((WithAbs.equiv _).symm s)
  rw [RingEquiv.apply_symm_apply, InfinitePlace.embedding_mk_eq_of_isReal hρ] at this
  exact this

theorem congr_of_local_complex (hσ : σ ≠ 1) (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G')
    (hi : ∀ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) → ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ := by
  obtain ⟨hc, hF, θ, h0, hθ⟩ := involutive_and_fixed hσ
  refine congr_of_invariants hσ hG hG' hd hd' (fun τ hτ => ?_) ?_
  · obtain ⟨Q, hQ, h⟩ := hi τ hτ
    rw [h, GlobalTheory.Inertia.posIndex_congr _ hQ]
  · have hdet : ∀ M : Matrix (Fin r) (Fin r) E, (∀ a b, σ (M a b) = M b a) → σ M.det = M.det := by
      intro M hM
      rw [← Matrix.det_transpose M]
      refine (RingHom.map_det (σ : E →+* E) Mᵀ).trans ?_
      rw [Matrix.det_transpose M]
      congr 1
      ext a b
      exact hM b a
    obtain ⟨a, ha⟩ := (hF (G.det / G'.det)).1 (by rw [map_div₀, hdet G hG, hdet G' hG'])
    obtain ⟨d, hdθ⟩ := (hF (θ * θ)).1 (by rw [map_mul, hθ]; ring)
    have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h, map_zero])
    have ha0 : a ≠ 0 := fun h => div_ne_zero hd hd' (by rw [← ha, h, map_zero])
    obtain ⟨x, y, hxy⟩ := GlobalTheory.QNorm.hasseNormSt F d a hd0 ha0
      (fun ρ => by
        rcases lt_or_gt_of_ne ((map_ne_zero ρ).2 hd0) with hρ | hρ
        · obtain ⟨τ, hτ, hτρ⟩ := exists_embedding_conj hc hF h0 hθ hdθ ρ hρ
          have h2 := GlobalTheory.Published.Landherr.re_det_div_pos hd τ (hi τ hτ)
          rw [← ha, hτρ, Complex.ofReal_re] at h2
          exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt h2.le]; ring⟩
        · exact GlobalTheory.Published.HasseNormSt.of_isSquare hρ.ne' (Real.isSquare_iff.2 hρ.le) _)
      (fun v => (hf v).exists_sq_sub hc hF h0 hθ hdθ hd' ha)
    refine ⟨algebraMap F E x + algebraMap F E y * θ, ?_⟩
    rw [← ha, hxy]
    simp only [map_add, map_sub, map_mul, map_pow, AlgEquiv.commutes, hθ, hdθ]
    ring

theorem congr_of_local (hσ : σ ≠ 1) (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G')
    (hi : ∀ v : InfinitePlace F, CongrOver σ v.Completion G G') :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ := by
  refine congr_of_local_complex hσ hG hG' hd hd' hf fun τ hτ => ?_
  have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
    ComplexEmbedding.isReal_iff.2 (by
      ext s
      change conj (τ (algebraMap F E s)) = τ (algebraMap F E s)
      rw [← hτ, AlgEquiv.commutes])
  obtain ⟨v, φ, hφ⟩ := exists_real_extension hre.embedding
  exact (hi v).complex τ hτ (Complex.ofRealHom.comp φ) (fun a => by simp)
    (fun s => by
      change ((φ (algebraMap F _ s) : ℝ) : ℂ) = _
      rw [hφ]
      exact hre.coe_embedding_apply s)

end Global

end GlobalTheory.HermGlobal

namespace GlobalTheory.Published

open GlobalTheory.HermGlobal

def HermitianHassePrinciple : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] (σ : E ≃ₐ[F] E), σ ≠ 1 →
    ∀ (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E),
      (∀ a b, σ (G a b) = G b a) → (∀ a b, σ (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G') →
      (∀ v : InfinitePlace F, CongrOver σ v.Completion G G') →
      ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ

theorem hermitianHassePrinciple_holds : HermitianHassePrinciple :=
  fun _ _ _ _ _ _ _ _ _ hσ _ _ _ hG hG' hd hd' hf hi => congr_of_local hσ hG hG' hd hd' hf hi

theorem HermitianHassePrinciple.iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] {σ : E ≃ₐ[F] E} (hσ : σ ≠ 1) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      (∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G') ∧
        ∀ v : InfinitePlace F, CongrOver σ v.Completion G G' :=
  ⟨fun h => ⟨fun _ => .of_congr h, fun _ => .of_congr h⟩,
    fun h => congr_of_local hσ hG hG' hd hd' h.1 h.2⟩

end GlobalTheory.Published
