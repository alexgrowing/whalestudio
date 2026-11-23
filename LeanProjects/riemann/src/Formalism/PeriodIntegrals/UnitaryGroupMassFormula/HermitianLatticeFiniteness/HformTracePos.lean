import Formalism.PeriodIntegrals.HermLatFin

open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin.UnitaryGroupMassFormula

variable {E : Type} [Field E] [NumberField E]

theorem sigma_invol (σ : E →+* E)
    (hσ : ∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ, hσ, Complex.conj_conj]

@[instance_reducible]
def starOf (σ : E →+* E) (h2 : ∀ a, σ (σ a) = a) : StarRing E where
  star := σ
  star_involutive := h2
  star_mul a b := by
    show σ (a * b) = σ b * σ a
    rw [map_mul, mul_comm]
  star_add a b := map_add σ a b

theorem herm_hermitian {n : ℕ} (σ : E →+* E)
    (hσ : ∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a))
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ τ : E →+* ℂ, (J.map τ).PosDef) (i j : Fin n) :
    σ (J i j) = J j i := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ]
  have h := congrFun (congrFun (hJ τ).isHermitian j) i
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply] at h
  rw [starRingEnd_apply]
  exact h

section Form

variable [StarRing E] {n : ℕ}

def hform (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun x y => ∑ i, ∑ j, star (x i) * J i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
    (fun x y y' => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

theorem hform_apply (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform J x y = ∑ i, ∑ j, star (x i) * J i j * y j := rfl

theorem hform_eq_herm (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : hform J x y = herm σ J x y := by
  simp only [hform_apply, herm, hst]

theorem hform_isSymm (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, star (J i j) = J j i) :
    (hform J).IsSymm := by
  refine LinearMap.IsSymm.mk fun x y => ?_
  simp only [hform_apply, starRingEnd_apply, star_sum, star_mul', star_star, hJ, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Form

section Pos

variable [StarRing E] {n : ℕ}

theorem hform_trace_pos (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (hσ : ∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a))
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ τ : E →+* ℂ, (J.map τ).PosDef)
    (x : Fin n → E) (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (hform J x x) := by
  haveI : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have key : ∀ τ : E →ₐ[ℚ] ℂ, 0 < τ (hform J x x) := by
    intro τ
    have hτσ : ∀ a : E, τ (σ a) = star (τ a) := fun a => by
      rw [← starRingEnd_apply]
      exact hσ τ.toRingHom a
    have e : τ (hform J x x) =
        star (fun i => τ (x i)) ⬝ᵥ (J.map τ) *ᵥ (fun i => τ (x i)) := by
      rw [hform_apply]
      simp only [map_sum]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul, hst, hτσ]
      ring
    rw [e]
    refine (hJ τ.toRingHom).dotProduct_mulVec_pos ?_
    intro h0
    apply hx
    funext i
    have h1 := congrFun h0 i
    exact (map_eq_zero_iff _ τ.toRingHom.injective).1 h1
  have hsum : 0 < ∑ τ : E →ₐ[ℚ] ℂ, τ (hform J x x) :=
    Finset.sum_pos (fun τ _ => key τ) Finset.univ_nonempty
  rw [← trace_eq_sum_embeddings ℂ, eq_ratCast, ← Complex.ofReal_ratCast, Complex.zero_lt_real,
    Rat.cast_pos] at hsum
  exact hsum

theorem isUJ_of_isom (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (J : Matrix (Fin n) (Fin n) E) (g : (Fin n → E) →ₗ[E] (Fin n → E))
    (hg : ∀ x y, hform J (g x) (g y) = hform J x y) :
    IsUJ σ J (LinearMap.toMatrix' g) := by
  ext a b
  have h := hg (Pi.single a 1) (Pi.single b 1)
  rw [hform_apply, hform_apply] at h
  simp only [← LinearMap.toMatrix'_apply, hst] at h
  have hr : ∑ i, ∑ j, σ ((Pi.single a 1 : Fin n → E) i) * J i j * (Pi.single b 1 : Fin n → E) j = J a b := by
    simp [Pi.single_apply, apply_ite σ]
  rw [hr] at h
  rw [← h]
  simp only [IsUJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end Pos

end PI.HermLatFin.UnitaryGroupMassFormula
