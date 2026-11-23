import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

namespace GlobalTheory.PeriodBlock

variable {E : Type} [Field E] [NumberField E]

theorem exists_ne_on_integers {σ σ' : E →+* ℂ} (hne : σ ≠ σ') : ∃ a : 𝓞 E, σ (a : E) ≠ σ' (a : E) := by
  by_contra hcon
  push_neg at hcon
  apply hne
  ext x
  obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hn := hcon n
  have hd := hcon d
  simp only [map_div₀]
  change σ ((n : 𝓞 E) : E) / σ ((d : 𝓞 E) : E) = σ' ((n : 𝓞 E) : E) / σ' ((d : 𝓞 E) : E)
  rw [hn, hd]

theorem entry_eq_zero {g : ℕ} {ty : Fin g → (E →+* ℂ)} (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hc : ∀ (a : 𝓞 E) (z : Fin g → ℂ), h (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * h z i)
    {i k : Fin g} (hik : ty i ≠ ty k) : h (Pi.single k 1) i = 0 := by
  obtain ⟨a, ha⟩ := exists_ne_on_integers hik
  have e : (fun j => ty j (a : E) * (Pi.single k (1 : ℂ) : Fin g → ℂ) j) = ty k (a : E) • (Pi.single k (1 : ℂ) : Fin g → ℂ) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have h1 := congrFun (hc a (Pi.single k 1)) i
  rw [e, map_smul] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : (ty k (a : E) - ty i (a : E)) * h (Pi.single k 1) i = 0 := by rw [sub_mul, h1]; ring
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm ha))

variable [IsCMField E] {H : Host E} {Dd : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem commutes {P P' : Dd.La →+ (Fin g → ℂ)} (hP : IsPeriod Dd ty P) (hP' : IsPeriod Dd ty P')
    (gam : Dd.La ≃ₗ[𝓞 E] Dd.La) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (e : ∀ x, P' (gam x) = h (P x))
    (a : 𝓞 E) (z : Fin g → ℂ) : h (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * h z i := by
  let D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := fun z i => ty i (a : E) * z i
      map_add' := fun x y => by funext i; simp [mul_add]
      map_smul' := fun c x => by funext i; simp [mul_left_comm] }
  have key : (h.comp D).restrictScalars ℝ = (D.comp h).restrictScalars ℝ := by
    refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
    have h1 : D (P x) = P (a • x) := funext fun i => (hP.1 a x i).symm
    have h2 : D (h (P x)) = h (P (a • x)) := by
      rw [← e, ← e, map_smul]
      exact funext fun i => (hP'.1 a (gam x) i).symm
    show h (D (P x)) = D (h (P x))
    rw [h1, h2]
  exact LinearMap.congr_fun key z

theorem apply_eq_sum {p : ℕ} {τ : E →+* ℂ} {ρ : Fin p → Fin g} (hρ : Function.Injective ρ)
    (hτ : ∀ i, ty i = τ ↔ i ∈ Set.range ρ) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hb : ∀ i k, ty i ≠ ty k → h (Pi.single k 1) i = 0) (v : Fin g → ℂ) (a : Fin p) :
    h v (ρ a) = ∑ b, h (Pi.single (ρ b) 1) (ρ a) * v (ρ b) := by
  have ev : h v = ∑ k, v k • h (Pi.single k 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp [map_sum, Finset.sum_apply]
  have hk : ∀ k, k ∉ Set.range ρ → v k * h (Pi.single k 1) (ρ a) = 0 := fun k hk => by
    have h₁ : ty (ρ a) = τ := (hτ _).2 ⟨a, rfl⟩
    have h₂ : ty k ≠ τ := fun h₃ => hk ((hτ k).1 h₃)
    rw [hb (ρ a) k (by rw [h₁]; exact h₂.symm), mul_zero]
  rw [ev, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (Fintype.sum_of_injective ρ hρ _ _ hk fun b => mul_comm _ _).symm

end GlobalTheory.PeriodBlock

open GlobalTheory.PeriodBlock in
theorem GlobalTheory.PeriodBlock.exists_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dd : Datum H) (g p : ℕ) (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (ρ : Fin p → Fin g), Function.Injective ρ → (∀ i, ty i = τ ↔ i ∈ Set.range ρ) → ∀ (P P' : Dd.La →+ (Fin g → ℂ)), IsPeriod Dd ty P → IsPeriod Dd ty P' → ∀ (gam : Dd.La ≃ₗ[𝓞 E] Dd.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a, P' (gam a) = h (P a)) → ∃ Hm : Matrix (Fin p) (Fin p) ℂ, IsUnit Hm ∧ ∀ (v : Fin g → ℂ) (a : Fin p), h v (ρ a) = ∑ b, Hm a b * v (ρ b) := by
  intro E _ _ _ H Dd g p ty τ ρ hρ hτ P P' hP hP' gam h e
  have b₁ : ∀ i k, ty i ≠ ty k → h.toLinearMap (Pi.single k 1) i = 0 := fun i k hik =>
    entry_eq_zero _ (commutes hP hP' gam h.toLinearMap e) hik
  have x₁ := apply_eq_sum hρ hτ h.toLinearMap b₁
  refine ⟨Matrix.of fun a b => h.toLinearMap (Pi.single (ρ b) 1) (ρ a), ?_, fun v a => x₁ v a⟩
  have hm : (Matrix.of fun a b => h.toLinearMap (Pi.single (ρ b) 1) (ρ a)) *
      (Matrix.of fun a b => h.symm.toLinearMap (Pi.single (ρ b) 1) (ρ a)) = (1 : Matrix (Fin p) (Fin p) ℂ) := by
    ext a c
    have := x₁ (h.symm (Pi.single (ρ c) 1)) a
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, LinearEquiv.coe_coe]
    rw [← this]
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac, Pi.single_eq_of_ne (hρ.ne hac)]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hm)
