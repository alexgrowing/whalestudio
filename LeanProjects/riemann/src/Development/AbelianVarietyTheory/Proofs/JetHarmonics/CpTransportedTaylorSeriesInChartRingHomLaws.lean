import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TaylorRead

theorem tay_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    tay (fun z => F z + G z) = tay F + tay G := by
  ext n
  have := iteratedDeriv_add (n := n) (x := (0 : ℂ)) hF.contDiffAt hG.contDiffAt
  simp only [tay, coeff_mk, map_add]
  rw [← add_div, ← this]
  rfl

theorem tay_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    tay (fun z => F z * G z) = tay F * tay G := by
  ext n
  have := iteratedDeriv_mul (n := n) (x := (0 : ℂ)) hF.contDiffAt hG.contDiffAt
  simp only [tay, coeff_mk, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => iteratedDeriv i F 0 / (i.factorial : ℂ) * (iteratedDeriv j G 0 / (j.factorial : ℂ)))]
  change iteratedDeriv n (F * G) 0 / _ = _
  rw [this, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h := Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← h]
  push_cast
  field_simp

theorem tay_congr {F G : ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) : tay F = tay G := by
  ext n
  simp only [tay, coeff_mk]
  rw [h.iteratedDeriv_eq n]

theorem eventuallyEq_of_tay_eq {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (h : tay F = tay G) : F =ᶠ[𝓝 0] G := by
  have hd : ∀ n, iteratedDeriv n F 0 = iteratedDeriv n G 0 := by
    intro n
    have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have := congrArg (coeff n) h
    simp only [tay, coeff_mk] at this
    exact (div_left_inj' h1).mp this
  have hs : AnalyticAt ℂ (F - G) 0 := hF.sub hG
  have htop : analyticOrderAt (F - G) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hs]
    intro i _
    rw [iteratedDeriv_sub hF.contDiffAt hG.contDiffAt, hd, sub_self]
  filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
  exact sub_eq_zero.mp hz

theorem tay_const (c : ℂ) : tay (fun _ => c) = C c := by
  ext n
  simp only [tay, coeff_mk, iteratedDeriv_const, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem derivative_tay (F : ℂ → ℂ) : derivative ℂ (tay F) = tay (deriv F) := by
  ext n
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [coeff_derivative, tay, coeff_mk, iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

theorem tay_id : tay (fun z => z) = X := by
  ext n
  rcases n with _ | n
  · simp [tay]
  · have : deriv (fun z : ℂ => z) = fun _ => 1 := by ext; simp
    simp only [tay, coeff_mk, iteratedDeriv_succ', this, iteratedDeriv_const, coeff_X]
    rcases n with _ | n <;> simp

theorem iteratedDeriv_comp_mul (F : ℂ → ℂ) (α : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => F (α * z)) = fun x => α ^ n * iteratedDeriv n F (α * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext x
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ,
      smul_eq_mul]
    ring

theorem tay_comp_mul (F : ℂ → ℂ) (α : ℂ) : tay (fun z => F (α * z)) = rescale α (tay F) := by
  ext n
  simp only [tay, coeff_mk, coeff_rescale, iteratedDeriv_comp_mul, mul_zero]
  ring

theorem constantCoeff_subst_of {R : Type*} [CommRing R] {ℓ : R⟦X⟧} (hℓ : constantCoeff ℓ = 0)
    (f : R⟦X⟧) : constantCoeff (f.subst ℓ : R⟦X⟧) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (HasSubst.of_constantCoeff_zero' hℓ),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hℓ, hd]

theorem subst_injective_of {R : Type*} [Field R] {ℓ : R⟦X⟧} (hℓ : constantCoeff ℓ = 0)
    (h1 : coeff 1 ℓ ≠ 0) {f g : R⟦X⟧} (h : (f.subst ℓ : R⟦X⟧) = g.subst ℓ) : f = g := by
  have hu : IsUnit (coeff 1 ℓ) := h1.isUnit
  have key : ∀ f : R⟦X⟧, PowerSeries.subst (R := R) (S := R) (substInvOfIsUnit ℓ hu) (PowerSeries.subst (R := R) (S := R) ℓ f) = f := by
    intro f
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hℓ) (HasSubst.substInvOfIsUnit ℓ hu),
      subst_substInvOfIsUnit_right ℓ hℓ hu, X_subst]
  rw [← key f, h, key g]

theorem hat_laws : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧), constantCoeff ℓ = 0 → (∀ F G : ℂ → ℂ, AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 → hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G ∧ hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G ∧ ((∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) → hat ι ℓ F = hat ι ℓ G) ∧ (coeff 1 ℓ ≠ 0 → hat ι ℓ F = hat ι ℓ G → F =ᶠ[𝓝 0] G)) ∧ (∀ c : ℂ, hat ι ℓ (fun _ => c) = C (ι c)) ∧ hat ι ℓ (fun z => z) = ℓ ∧ (∀ F : ℂ → ℂ, constantCoeff (hat ι ℓ F) = ι (F 0)) ∧ (∀ F : ℂ → ℂ, AnalyticAt ℂ F 0 → derivative ℂ_[q] (hat ι ℓ F) = derivative ℂ_[q] ℓ * hat ι ℓ (deriv F)) ∧ (∀ (F : ℂ → ℂ) (α : ℂ), AnalyticAt ℂ F 0 → hat ι ℓ (fun z => F (α * z)) = hat ι (C (ι α) * ℓ) F) ∧ ∀ (F : ℂ → ℂ) (h : ℂ_[q]⟦X⟧), constantCoeff h = 0 → (hat ι ℓ F).subst h = hat ι (ℓ.subst h) F := by
  intro q _ ι ℓ hℓ
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  refine ⟨fun F G hF hG => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hat]
    rw [tay_add hF hG, map_add, subst_add hs]
  · simp only [hat]
    rw [tay_mul hF hG, map_mul, subst_mul hs]
  · intro h
    have : F =ᶠ[𝓝 0] G := (hF.frequently_eq_iff_eventually_eq hG).mp h.frequently
    simp only [hat]
    rw [tay_congr this]
  · intro h1 h
    apply eventuallyEq_of_tay_eq hF hG
    exact PowerSeries.map_injective (ι : ℂ →+* ℂ_[q]) ι.injective (subst_injective_of hℓ h1 h)
  · intro c
    simp only [hat]
    rw [tay_const, map_C, subst_C]
    rfl
  · simp only [hat]
    rw [tay_id, map_X, subst_X hs]
  · intro F
    simp only [hat]
    rw [constantCoeff_subst_of hℓ, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    simp [tay]
  · intro F _
    simp only [hat]
    rw [derivative_subst hs, mul_comm, ← derivative_tay]
    congr 2
    ext n
    simp [coeff_derivative]
  · intro F α _
    simp only [hat]
    have e : PowerSeries.map (ι : ℂ →+* ℂ_[q]) (rescale α (tay F))
        = rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay F)) := by
      ext n
      simp [coeff_rescale]
    rw [tay_comp_mul, e, rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' _) hs,
      subst_smul hs, subst_X hs, smul_eq_C_mul]
  · intro F h hh
    simp only [hat]
    rw [subst_comp_subst_apply hs (HasSubst.of_constantCoeff_zero' hh)]

end GlobalTheory.MomOne.TaylorRead
