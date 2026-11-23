import Mathlib
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def rels (φ : MultilinearMap B (fun _ : Fin q => L) B) : Set (MvPolynomial L B) :=
  Set.range (fun p : L × L => X (p.1 + p.2) - X p.1 - X p.2) ∪
  Set.range (fun p : B × L => X (p.1 • p.2) - C p.1 * X p.2) ∪
  Set.range (fun ℓ : Fin q → L => ∏ i, X (ℓ i) - C (φ ℓ))

def ideal (φ : MultilinearMap B (fun _ : Fin q => L) B) : Ideal (MvPolynomial L B) :=
  Ideal.span (rels φ)

abbrev Alg (φ : MultilinearMap B (fun _ : Fin q => L) B) : Type :=
  MvPolynomial L B ⧸ ideal φ

variable (φ : MultilinearMap B (fun _ : Fin q => L) B)

theorem algebraMap_eq_mk (c : B) : algebraMap B (Alg φ) c = Ideal.Quotient.mk _ (C c) := rfl

theorem add_mem (a b : L) : X (a + b) - X a - X b ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩))

theorem smul_mem (c : B) (a : L) : X (c • a) - C c * X a ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inr ⟨(c, a), rfl⟩))

theorem prod_mem (ℓ : Fin q → L) : ∏ i, X (ℓ i) - C (φ ℓ) ∈ ideal φ :=
  Ideal.subset_span (Or.inr ⟨ℓ, rfl⟩)

def gen : L →ₗ[B] Alg φ where
  toFun ℓ := Ideal.Quotient.mk _ (X ℓ)
  map_add' a b := by
    rw [← sub_eq_zero, sub_add_eq_sub_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact add_mem φ a b
  map_smul' c a := by
    rw [← sub_eq_zero, RingHom.id_apply, Algebra.smul_def, algebraMap_eq_mk,
      ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact smul_mem φ c a

theorem gen_apply (ℓ : L) : gen φ ℓ = Ideal.Quotient.mk _ (X ℓ) := rfl

theorem prod_gen (ℓ : Fin q → L) : ∏ i, gen φ (ℓ i) = algebraMap B (Alg φ) (φ ℓ) := by
  rw [← sub_eq_zero]
  simp only [gen_apply, ← map_prod, algebraMap_eq_mk]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact prod_mem φ ℓ

def scalePoly (t : B) : MvPolynomial L B →ₐ[B] MvPolynomial L B := aeval fun ℓ => C t * X ℓ

theorem scalePoly_X (t : B) (ℓ : L) : scalePoly t (X ℓ) = C t * X ℓ := by simp [scalePoly]

theorem scalePoly_C (t c : B) : scalePoly (L := L) t (C c) = C c := by
  simp [scalePoly, aeval_C, MvPolynomial.algebraMap_eq]

theorem le_comap_scale (t : B) (ht : t ^ q = 1) : ideal φ ≤ (ideal φ).comap (scalePoly t) := by
  rw [ideal, Ideal.span_le]
  rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (a + b) - X a - X b) = C t * (X (a + b) - X a - X b) := by
      simp only [map_sub, scalePoly_X]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem φ a b)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (c • a) - C c * X a) = C t * (X (c • a) - C c * X a) := by
      simp only [map_sub, map_mul, scalePoly_X, scalePoly_C]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (smul_mem φ c a)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (∏ i, X (ℓ i) - C (φ ℓ)) = ∏ i, X (ℓ i) - C (φ ℓ) := by
      simp only [map_sub, map_prod, scalePoly_X, scalePoly_C, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← map_pow, ht, map_one, one_mul]
    rw [this]; exact prod_mem φ ℓ

def scale (t : B) (ht : t ^ q = 1) : Alg φ →ₐ[B] Alg φ :=
  Ideal.quotientMapₐ (ideal φ) (scalePoly t) (le_comap_scale φ t ht)

theorem scale_mk (t : B) (ht : t ^ q = 1) (p : MvPolynomial L B) :
    scale φ t ht (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (scalePoly t p) := rfl

theorem scale_gen (t : B) (ht : t ^ q = 1) (ℓ : L) : scale φ t ht (gen φ ℓ) = t • gen φ ℓ := by
  rw [gen_apply, scale_mk, scalePoly_X, map_mul, Algebra.smul_def, algebraMap_eq_mk]

theorem scale_ext {f g : Alg φ →ₐ[B] Alg φ} (h : ∀ ℓ, f (gen φ ℓ) = g (gen φ ℓ)) : f = g :=
  Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => h ℓ)

theorem scale_comp (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) :
    (scale φ s hs).comp (scale φ t ht) = scale φ (s * t) (by rw [mul_pow, hs, ht, one_mul]) :=
  scale_ext φ fun ℓ => by
    rw [AlgHom.comp_apply, scale_gen, map_smul, scale_gen, scale_gen, smul_smul, mul_comm]

theorem scale_eq_id (t : B) (ht : t ^ q = 1) (h1 : t = 1) : scale φ t ht = AlgHom.id B (Alg φ) :=
  scale_ext φ fun ℓ => by rw [scale_gen, h1, one_smul, AlgHom.id_apply]

theorem scale_congr (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) (h : s = t) :
    scale φ s hs = scale φ t ht := by subst h; rfl

def tw (ζ : B) (g : ZMod q) : B := ζ ^ g.val

theorem tw_add [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g h : ZMod q) :
    tw ζ (g + h) = tw ζ g * tw ζ h := by
  rw [tw, tw, tw, ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (g.val + h.val) q, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem tw_pow {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) : tw ζ g ^ q = 1 := by
  rw [tw, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem tw_zero (ζ : B) : tw ζ (0 : ZMod q) = 1 := by simp [tw]

theorem tw_mul_tw_neg [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) :
    tw ζ g * tw ζ (-g) = 1 := by rw [← tw_add hζ, add_neg_cancel, tw_zero]

def act [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* (Alg φ ≃ₐ[B] Alg φ) where
  toFun g := AlgEquiv.ofAlgHom (scale φ (tw ζ g.toAdd) (tw_pow hζ _))
    (scale φ (tw ζ (-g.toAdd)) (tw_pow hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (tw_mul_tw_neg hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (by rw [mul_comm]; exact tw_mul_tw_neg hζ _))
  map_one' := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (0 : ZMod q)) (tw_pow hζ 0) x = x
    rw [scale_eq_id φ _ _ (tw_zero ζ)]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (g.toAdd + h.toAdd)) (tw_pow hζ _) x =
      scale φ (tw ζ g.toAdd) (tw_pow hζ _) (scale φ (tw ζ h.toAdd) (tw_pow hζ _) x)
    rw [← AlgHom.comp_apply, scale_comp]
    exact DFunLike.congr_fun (scale_congr φ _ _ _ _ (tw_add hζ _ _)) x

theorem act_gen [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) (g : ZMod q) (ℓ : L) :
    act φ ζ hζ (Multiplicative.ofAdd g) (gen φ ℓ) = ζ ^ g.val • gen φ ℓ :=
  scale_gen φ _ (tw_pow hζ _) ℓ

end GlobalTheory.KummerAlg
