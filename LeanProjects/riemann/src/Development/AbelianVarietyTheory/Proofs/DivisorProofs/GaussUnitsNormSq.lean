import Mathlib

open ComplexConjugate Finset

namespace GlobalTheory

namespace GaussUnits

variable {R : Type} [CommRing R] [Fintype R]

theorem sum_ideal_of_exists (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (b : R) (hb : ∃ x ∈ I, b * x ≠ 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := hb
  have hne : ¬ ∀ r, ψ (b * x₀ * r) = 1 := fun h => hx₀ (hψ _ h)
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  have hyI : x₀ * r ∈ I := I.mul_mem_right r hx₀I
  have hby : ψ (b * (x₀ * r)) ≠ 1 := by rwa [← mul_assoc]
  have hshift := Fintype.sum_equiv (Equiv.addRight (x₀ * r))
    (fun x => if x + x₀ * r ∈ I then ψ (b * (x + x₀ * r)) else 0)
    (fun x => if x ∈ I then ψ (b * x) else 0) (fun _ => rfl)
  have hS : ∑ x, (if x ∈ I then ψ (b * x) else 0)
      = ψ (b * (x₀ * r)) * ∑ x, (if x ∈ I then ψ (b * x) else 0) := by
    conv_lhs => rw [← hshift]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ I
    · have h' : x + x₀ * r ∈ I := I.add_mem hx hyI
      rw [if_pos h', if_pos hx, mul_add, AddChar.map_add_eq_mul, mul_comm]
    · have h' : x + x₀ * r ∉ I := fun h => hx (by simpa using I.sub_mem h hyI)
      rw [if_neg h', if_neg hx, mul_zero]
  have h1 : (1 - ψ (b * (x₀ * r))) * ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hby
  · exact h

theorem sum_ideal_of_forall (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ) (b : R)
    (hb : ∀ x ∈ I, b * x = 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = ((univ.filter (· ∈ I)).card : ℂ) := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_filter] at hx
  rw [hb x hx.2, AddChar.map_zero_eq_one, Nat.cast_one]

theorem sum_units_eq (m : Ideal R) [DecidablePred (· ∈ m)] [Fintype Rˣ]
    (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (f : R → ℂ) :
    ∑ u : Rˣ, f u = ∑ x, f x - ∑ x, (if x ∈ m then f x else 0) := by
  have h : ∑ u : Rˣ, f u = ∑ x ∈ univ.filter (fun x => ¬ x ∈ m), f x := by
    refine Finset.sum_bij (fun u _ => (u : R)) ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter]
      exact ⟨mem_univ _, (hm u).mp u.isUnit⟩
    · intro a _ b _ h
      exact Units.ext h
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨((hm x).mpr hx.2).unit, mem_univ _, rfl⟩
    · intro u _
      rfl
  rw [h, eq_sub_iff_add_eq, ← Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]

end GaussUnits

open GaussUnits in

theorem gauss_units_norm_sq : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [Fintype Rˣ]
    (m : Ideal R), (∀ x : R, IsUnit x ↔ x ∉ m) → ∀ (ψ : AddChar R ℂ),
    (∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) → ∀ (χ : Rˣ → ℂ), (∀ u v, χ (u * v) = χ u * χ v) →
    (∀ u, ‖χ u‖ = 1) → ∀ (t₀ : Rˣ), (∀ x ∈ m, ((t₀ : R) - 1) * x = 0) → χ t₀ ≠ 1 →
    ‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 = Fintype.card R := by
  intro R _ _ _ _ m hm ψ hψ χ hχ hχn t₀ ht₀ hχt₀
  classical
  have hχ0 : ∀ u, χ u ≠ 0 := fun u h => by simpa [h] using hχn u
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    rw [mul_one] at h
    have h2 : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (hχ0 1)
    · exact sub_eq_zero.mp h3
  have hconj : conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u) = ∑ z : Rˣ, χ z * ψ (-(z : R)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [map_mul, Complex.inv_eq_conj (hχn z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  have hexp : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = ∑ t : Rˣ, (χ t)⁻¹ * ∑ z : Rˣ, ψ (((t : R) - 1) * z) := by
    rw [hconj, Finset.sum_mul_sum, Finset.sum_comm]
    have hz : ∀ z : Rˣ, ∑ y : Rˣ, (χ y)⁻¹ * ψ y * (χ z * ψ (-(z : R)))
        = ∑ t : Rˣ, (χ t)⁻¹ * ψ (((t : R) - 1) * z) := by
      intro z
      refine Fintype.sum_equiv (Equiv.mulRight z⁻¹) _ _ (fun y => ?_)
      have hzinv : χ z⁻¹ = (χ z)⁻¹ := by
        have h := hχ z z⁻¹
        rw [mul_inv_cancel, hχ1] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      have harg : (((y * z⁻¹ : Rˣ) : R) - 1) * (z : R) = (y : R) + -(z : R) := by
        rw [sub_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          mul_one, one_mul, sub_eq_add_neg]
      simp only [Equiv.coe_mulRight]
      rw [harg, AddChar.map_add_eq_mul, hχ, hzinv, mul_inv, inv_inv]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ t : Rˣ, ∑ z : Rˣ, ψ (((t : R) - 1) * z) =
      (if t = 1 then (Fintype.card R : ℂ) else 0) -
      (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then ((univ.filter (· ∈ m)).card : ℂ) else 0) := by
    intro t
    rw [sum_units_eq m hm (fun x => ψ (((t : R) - 1) * x))]
    congr 1
    · have htop : ∑ x, ψ (((t : R) - 1) * x)
          = ∑ x, (if x ∈ (⊤ : Ideal R) then ψ (((t : R) - 1) * x) else 0) := by simp
      rw [htop]
      split_ifs with h
      · subst h
        rw [sum_ideal_of_forall ⊤ ψ _ (by simp)]
        simp
      · apply sum_ideal_of_exists ⊤ ψ hψ
        refine ⟨1, Submodule.mem_top, ?_⟩
        rw [mul_one, sub_ne_zero]
        exact fun h' => h (Units.val_eq_one.mp h')
    · split_ifs with h
      · exact sum_ideal_of_forall m ψ _ h
      · push_neg at h
        exact sum_ideal_of_exists m ψ hψ _ h
  have hcond : ∀ t : Rˣ, (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) ↔
      (∀ x ∈ m, ((t : R) - 1) * x = 0) := by
    intro t
    constructor
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul] at h1
      have h3 : (t₀ : R) * (((t : R) - 1) * x) = 0 := by linear_combination h1 - h2
      exact t₀.isUnit.mul_right_eq_zero.mp h3
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul]
      linear_combination (t₀ : R) * h1 + h2
  have hS : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
    have e := Fintype.sum_equiv (Equiv.mulLeft t₀)
      (fun t => if (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) then (χ (t₀ * t))⁻¹ else 0)
      (fun t => if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) (fun _ => rfl)
    have hS' : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)
        = (χ t₀)⁻¹ * ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) := by
      conv_lhs => rw [← e]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [hcond t, hχ, mul_inv, mul_ite, mul_zero]
    have hne : (χ t₀)⁻¹ ≠ 1 := fun h => hχt₀ (inv_eq_one.mp h)
    have h1 : (1 - (χ t₀)⁻¹) *
        ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
      rw [sub_mul, one_mul, ← hS', sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hmain : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = (Fintype.card R : ℂ) := by
    rw [hexp]
    simp_rw [hinner, mul_sub, mul_ite, mul_zero]
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then
        (χ t)⁻¹ * ((univ.filter (· ∈ m)).card : ℂ) else 0)
        = (∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)) *
          ((univ.filter (· ∈ m)).card : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> simp
    rw [h2, hS, zero_mul, sub_zero]
    simp [hχ1]
  have hn : ((‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 : ℝ) : ℂ) = (Fintype.card R : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hmain]
  exact_mod_cast hn

end GlobalTheory
