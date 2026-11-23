import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] {N : ℕ}

namespace HeisenbergBilinear

section Forms

variable {R : Type} [CommRing R] [Algebra F R] (a : Fin N → F)

theorem qd_add (u x : Fin N → R) : qd R a (u + x) = qd R a u + qd R a x + Bd R a u x := by
  simp only [qd, Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_ofNat]
  ring

theorem Bd_add_left (u u' x : Fin N → R) : Bd R a (u + u') x = Bd R a u x + Bd R a u' x := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_add_right (u x x' : Fin N → R) : Bd R a u (x + x') = Bd R a u x + Bd R a u x' := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_smul_left (t : R) (u x : Fin N → R) : Bd R a (t • u) x = t * Bd R a u x := by
  simp only [Bd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_smul_right (t : R) (u x : Fin N → R) : Bd R a u (t • x) = t * Bd R a u x := by
  simp only [Bd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_neg_left (u x : Fin N → R) : Bd R a (-u) x = -Bd R a u x := by
  simp only [Bd, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_comm (u x : Fin N → R) : Bd R a u x = Bd R a x u := by
  simp only [Bd]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_self (x : Fin N → R) : Bd R a x x = 2 * qd R a x := by
  simp only [Bd, qd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_ofNat]
  ring

end Forms

variable [NumberField F]

theorem half_mul_two_AF : algebraMap F (AF F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem qd_rat (a : Fin N → F) (ξ : Fin N → F) : qd (AF F) a (rat ξ) = algebraMap F (AF F) (qd F a ξ) := by
  simp only [qd, rat, map_sum, map_mul, map_pow]
  rfl

end HeisenbergBilinear

open HeisenbergBilinear in
theorem weil_intertwine : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ,
      (∀ b x y, rho ψ a x y (Ub ψ a b Φ) = Ub ψ a b (rho ψ a x (y + b • x) Φ)) ∧
      (∀ (t t' : AF F) x y, t * t' = 1 → rho ψ a x y (Da t Φ) = Da t (rho ψ a (t • x) (t' • y) Φ)) ∧
      (∀ x y, rho ψ a x y (Fo ψ ν a Φ) = Fo ψ ν a (rho ψ a (-y) x Φ)) ∧
      (∀ b : F, th (Ub ψ a (algebraMap F (AF F) b) Φ) = th Φ) ∧
      ∀ t : F, t ≠ 0 → th (Da (algebraMap F (AF F) t) Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ
  obtain ⟨-, ⟨-, -, hchar, -⟩, -, ⟨hHaar, -⟩, -⟩ := hC
  have hh : algebraMap F (AF F) (1 / 2) * 2 = 1 := half_mul_two_AF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro b x y
    funext u
    simp only [rho, Ub]
    have key : ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) *
          ψ (b * qd (AF F) a (u + x)) =
        ψ (b * qd (AF F) a u) *
          ψ (Bd (AF F) a u (y + b • x) + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x (y + b • x)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [qd_add, Bd_add_right, Bd_smul_right, Bd_self]
      linear_combination (-(b * qd (AF F) a x)) * hh
    linear_combination (Φ (u + x)) * key
  ·
    intro t t' x y htt
    funext u
    simp only [rho, Da]
    have key : Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y =
        Bd (AF F) a (t • u) (t' • y) + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (t • x) (t' • y) := by
      simp only [Bd_smul_left, Bd_smul_right]
      linear_combination (-(Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y)) * htt
    rw [key, smul_add]
  ·
    intro x y
    funext u
    have : ν.IsAddHaarMeasure := hHaar
    have : (muV N ν).IsAddRightInvariant := by unfold muV; infer_instance
    simp only [rho, Fo]
    refine Eq.trans ?_ (integral_add_right_eq_self (μ := muV N ν)
      (fun s => ψ (Bd (AF F) a s x + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (-y) x) * Φ (s + -y) *
        ψ (Bd (AF F) a s u)) y)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only
    rw [add_neg_cancel_right]
    have key : ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) *
          ψ (Bd (AF F) a s (u + x)) =
        ψ (Bd (AF F) a (s + y) x + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (-y) x) *
          ψ (Bd (AF F) a (s + y) u) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have e1 := Bd_comm a u y
      have e2 := Bd_comm a x y
      simp only [Bd_add_left, Bd_add_right, Bd_neg_left]
      linear_combination e1 + algebraMap F (AF F) (1 / 2) * e2 + Bd (AF F) a y x * hh
    linear_combination (Φ s) * key
  ·
    intro b
    simp only [th, Ub]
    refine tsum_congr fun ξ => ?_
    rw [qd_rat, ← map_mul, hchar, one_mul]
  ·
    intro t ht
    simp only [th, Da]
    have e : ∀ ξ : Fin N → F, algebraMap F (AF F) t • rat ξ = rat (t • ξ) := by
      intro ξ
      funext l
      simp only [rat, Pi.smul_apply, smul_eq_mul, map_mul]
    simp only [e]
    exact Equiv.tsum_eq
      { toFun := fun ξ : Fin N → F => t • ξ
        invFun := fun ξ => t⁻¹ • ξ
        left_inv := fun ξ => by simp only [smul_smul, inv_mul_cancel₀ ht, one_smul]
        right_inv := fun ξ => by simp only [smul_smul, mul_inv_cancel₀ ht, one_smul] }
      (fun ξ => Φ (rat ξ))

end GlobalTheory.SWQ
