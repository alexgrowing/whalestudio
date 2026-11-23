import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.HermTrace

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem fld_induction (P : PPol σ n) (p : Fld P → Prop) (h0 : ∀ e, p (algebraMap E (Fld P) e))
    (hadd : ∀ a b, p a → p b → p (a + b)) (hmul : ∀ a, p a → p (a * alpha P)) (l : Fld P) : p l := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := P.1) l
  induction q using Polynomial.induction_on with
  | C a => exact h0 a
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  | monomial k a ha => rw [pow_succ, ← mul_assoc, map_mul]; exact hmul _ ha

theorem star_star (hσ : ∀ e, σ (σ e) = e) (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  induction l using fld_induction with
  | h0 e => rw [star'_algebraMap, star'_algebraMap, hσ]
  | hadd a b ha hb => rw [map_add, map_add, ha, hb]
  | hmul a ha => rw [map_mul, map_mul, ha, star'_alpha, map_inv₀, star'_alpha, inv_inv]

theorem trace_star (hσ : ∀ e, σ (σ e) = e) (P : PPol σ n) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star_star hσ P)) (RingHom.ext (star_star hσ P))
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ (RingHom.ext fun e => (star'_algebraMap P e).symm) l
  have h' : Algebra.trace E (Fld P) l = σ (Algebra.trace E (Fld P) (star' P l)) := h
  rw [h', hσ]

section Form

variable {A : Type} [CommRing A] (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (a b : Fin n → A) : Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (M : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT s M * J * M = J) (a b : Fin n → A) :
    Formalism.UG.hform s J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform s J a b := by
  have e : s ∘ (M *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s M := by
    funext i
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem hform_add_left (a a' b : Fin n → A) :
    Formalism.UG.hform s J (a + a') b = Formalism.UG.hform s J a b + Formalism.UG.hform s J a' b := by
  simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (a b b' : Fin n → A) :
    Formalism.UG.hform s J a (b + b') = Formalism.UG.hform s J a b + Formalism.UG.hform s J a b' := by
  simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (c : A) (a b : Fin n → A) :
    Formalism.UG.hform s J (c • a) b = s c * Formalism.UG.hform s J a b := by
  simp [Formalism.UG.hform, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (c : A) (a b : Fin n → A) :
    Formalism.UG.hform s J a (c • b) = c * Formalism.UG.hform s J a b := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_symm (hs : ∀ e, s (s e) = e) (hJ : ∀ i j, s (J j i) = J i j) (a b : Fin n → A) :
    Formalism.UG.hform s J b a = s (Formalism.UG.hform s J a b) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hs, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_single (i j : Fin n) : Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [Formalism.UG.hform, Pi.single_apply, apply_ite s]

end Form

theorem exists_trace_form : ∀ (F E : Type) [Field F] [Field E] [CharZero E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (A : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) A * J * A = J → ∀ φ : Fld P ≃ₗ[E] (Fin n → E), (∀ y, A *ᵥ φ y = φ (alpha P * y)) → ∃ x : Fld P, x ≠ 0 ∧ star' P x = x ∧ ∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := by
  intro F E _ _ _ _ σ hσ n P J hJ A hA φ hφ
  set s : E →+* E := (σ : E →+* E) with hs
  have h1 : ∀ y y', Formalism.UG.hform s J (φ (alpha P * y')) (φ (alpha P * y)) = Formalism.UG.hform s J (φ y') (φ y) :=
    fun y y' => by rw [← hφ, ← hφ, hform_unitary s J A hA]
  have h2 : ∀ l y y', Formalism.UG.hform s J (φ (l * y')) (φ y) = Formalism.UG.hform s J (φ y') (φ (star' P l * y)) := by
    intro l
    induction l using fld_induction with
    | h0 e =>
      intro y y'
      rw [star'_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hform_smul_left,
        hform_smul_right]
      rfl
    | hadd a b ha hb =>
      intro y y'
      rw [add_mul, map_add, hform_add_left, ha, hb, map_add, add_mul, map_add, hform_add_right]
    | hmul a ha =>
      intro y y'
      rw [mul_assoc, ha, map_mul (star' P), star'_alpha, ← h1 (star' P a * (alpha P)⁻¹ * y) y']
      congr 2
      field_simp [alpha_ne_zero P]
  let f : Module.Dual E (Fld P) :=
    { toFun := fun y => Formalism.UG.hform s J (φ 1) (φ y)
      map_add' := fun a b => by rw [map_add, hform_add_right]
      map_smul' := fun c a => by rw [map_smul, hform_smul_right]; rfl }
  have hnd := traceForm_nondegenerate E (Fld P)
  let x : Fld P := ((Algebra.traceForm E (Fld P)).toDual hnd).symm f
  have hx : ∀ y, Algebra.trace E (Fld P) (x * y) = Formalism.UG.hform s J (φ 1) (φ y) := fun y => by
    have := LinearMap.BilinForm.toDual_def hnd (m := x) (n := y)
    rw [Algebra.traceForm_apply] at this
    rw [← this, LinearEquiv.apply_symm_apply]
    rfl
  have h3 : ∀ y y', Formalism.UG.hform s J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := fun y y' => by
    rw [mul_assoc, hx, mul_comm y, ← h2, mul_one]
  refine ⟨x, fun h0 => ?_, ?_, h3⟩
  · have hn : 0 < n := P.2.2.2.1 ▸ P.2.2.1.natDegree_pos
    have hz : J = 0 := by
      ext i j
      rw [← hform_single s J i j, ← φ.apply_symm_apply (Pi.single i 1), ← φ.apply_symm_apply (Pi.single j 1), h3, h0]
      simp
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact hJ.2 (by rw [hz, Matrix.det_zero])
  · rw [← sub_eq_zero]
    refine hnd.1 _ fun z => ?_
    have a := hform_symm s J hσ hJ.1 (φ z) (φ 1)
    rw [h3, h3, map_one, mul_one, mul_one] at a
    have b := trace_star hσ P (x * star' P z)
    rw [map_mul, star_star hσ] at b
    rw [Algebra.traceForm_apply, sub_mul, map_sub, b, a, sub_eq_zero]
    rfl

end GlobalTheory.TrEll.HermTrace
