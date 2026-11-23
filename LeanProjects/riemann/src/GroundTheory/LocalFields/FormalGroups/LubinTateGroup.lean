import Mathlib
import GroundTheory.LocalFields.FormalGroups.LubinTate

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section Composition

variable {A : Type*} [CommRing A] {σ τ : Type*}

private theorem coeff_eq_of_two_le_order {φ ψ : MvPowerSeries σ A}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

def IsLubinTateLift (f g : PowerSeries A) (ℓ φ : MvPowerSeries σ A) : Prop :=
  constantCoeff φ = 0 ∧ (2 : ℕ∞) ≤ order (φ - ℓ) ∧
    PowerSeries.subst φ f = subst (substEach g) φ

theorem isLubinTateLift_X [Finite σ] {g : PowerSeries A} (hg0 : PowerSeries.constantCoeff g = 0)
    (i : σ) : IsLubinTateLift g g (X i) (X i : MvPowerSeries σ A) :=
  ⟨by simp, by simp, by rw [subst_X (hasSubst_substEach hg0)]; rfl⟩

theorem two_le_order_subst_sub_subst_of [Finite τ] {Φ ℓ : MvPowerSeries τ A}
    (hΦ : (2 : ℕ∞) ≤ order (Φ - ℓ)) (hℓ : constantCoeff ℓ = 0) {u v : τ → MvPowerSeries σ A}
    (hu0 : ∀ j, constantCoeff (u j) = 0) (hv0 : ∀ j, constantCoeff (v j) = 0)
    (huv : ∀ j, (2 : ℕ∞) ≤ order (u j - v j)) :
    (2 : ℕ∞) ≤ order (subst u Φ - subst v ℓ) := by
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have h1 := le_order_subst_sub_subst hus hu0 hΦ
  have h2 := add_le_order_subst_sub_subst hus hvs hu0 hv0 huv (f := ℓ) (m := 1)
    (one_le_order_iff_constCoeff_eq_zero.2 hℓ)
  have h2' : (2 : ℕ∞) ≤ order (subst u ℓ - subst v ℓ) :=
    (ENat.add_le_add_iff_right ENat.one_ne_top).1 h2
  have e : subst u Φ - subst v ℓ = (subst u Φ - subst u ℓ) + (subst u ℓ - subst v ℓ) := by ring
  rw [e]
  exact le_trans (le_min h1 h2') min_order_le_add

theorem IsLubinTateLift.comp [Finite σ] [Finite τ] {f g h : PowerSeries A}
    (hg0 : PowerSeries.constantCoeff g = 0) (hh0 : PowerSeries.constantCoeff h = 0)
    {ℓ Φ : MvPowerSeries τ A} (hΦ : IsLubinTateLift f g ℓ Φ) {v u : τ → MvPowerSeries σ A}
    (hu : ∀ j, IsLubinTateLift g h (v j) (u j)) :
    IsLubinTateLift f h (subst v ℓ) (subst u Φ) := by
  obtain ⟨hΦ0, hΦ2, hΦe⟩ := hΦ
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun j => (hu j).1
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hℓ0 : constantCoeff ℓ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_eq_of_two_le_order hΦ2 (by simp),
      coeff_zero_eq_constantCoeff_apply, hΦ0]
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_eq_of_two_le_order (hu j).2.1 (by simp),
      coeff_zero_eq_constantCoeff_apply, hu0 j]
  refine ⟨constantCoeff_subst_eq_zero hus hu0 hΦ0,
    two_le_order_subst_sub_subst_of hΦ2 hℓ0 hu0 hv0 (fun j => (hu j).2.1), ?_⟩
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  rw [← subst_powerSeries_subst hΦs hus, hΦe, subst_comp_subst_apply (hasSubst_substEach hg0) hus,
    subst_comp_subst_apply hus (hasSubst_substEach hh0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hus, subst_X hus]
  exact (hu j).2.2

theorem subst_substEach_unit (g : PowerSeries A) (φ : MvPowerSeries Unit A) :
    subst (substEach g) φ = PowerSeries.subst g φ := by
  have : (substEach g : Unit → MvPowerSeries Unit A) = fun _ => g := by
    funext u
    exact PowerSeries.X_subst g
  rw [this, PowerSeries.subst_def]

end Composition

section FormalModule

variable {A : Type*} [CommRing A]

structure FormalModule (F : FormalGroup A) [F.IsComm] where

  smul : A →+* Hom F F

  linearCoeff_smul : ∀ a, linearCoeff F (smul a) = a

end FormalModule

section LubinTate

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A} {f g h : PowerSeries A}

theorem subst_linearForm {σ τ : Type*} [Fintype τ] {v : τ → MvPowerSeries σ A} (hv : HasSubst v)
    (a : τ → A) : subst v (sum₂ a) = ∑ j, C (a j) * v j := by
  rw [sum₂, ← coe_substAlgHom hv, map_sum]
  simp only [map_mul, coe_substAlgHom, subst_C, subst_X hv]

theorem linearForm_unit (a : A) :
    sum₂ (fun _ : Unit => a) = PowerSeries.C a * PowerSeries.X := by
  simp only [sum₂, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem linearForm_fin_two (a b : A) :
    sum₂ (![a, b] : Fin 2 → A) = C a * X 0 + C b * X 1 := by
  simp [sum₂, Fin.sum_univ_two]

theorem subst_linearForm_one_one {σ : Type*} {u v : MvPowerSeries σ A}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    subst ![u, v] (sum₂ (![1, 1] : Fin 2 → A)) = u + v := by
  rw [subst_linearForm (hasSubst_pair hu hv)]
  simp [Fin.sum_univ_two]

theorem single_zero_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  intro h
  have := congrArg (fun d => d 0) h
  simp at this

theorem substEach_fin_two (g : PowerSeries A) :
    (substEach g : Fin 2 → MvPowerSeries (Fin 2) A) =
      ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A) g,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A) g] := by
  funext i
  fin_cases i <;> rfl

variable (hπ : Irreducible π)
include hπ

theorem isLubinTateLift_lubinTateLift {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (a : σ → A) :
    IsLubinTateLift f g (sum₂ a) (lubinTateLift hπ hf hg a) :=
  ⟨constantCoeff_lubinTateLift hπ hf hg a, two_le_order_lubinTateLift_sub hπ hf hg a,
    subst_lubinTateLift hπ hf hg a⟩

theorem eq_lubinTateLift_of {σ : Type*} [Fintype σ] (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) {a : σ → A} {ℓ φ : MvPowerSeries σ A}
    (h : IsLubinTateLift f g ℓ φ) (hℓ : ℓ = sum₂ a) : φ = lubinTateLift hπ hf hg a := by
  subst hℓ
  exact eq_lubinTateLift hπ hf hg a h.2.1 h.2.2

theorem lubinTateLift_assoc (hf : IsLubinTateSeries π f) :
    subst ![subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)), X 2]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)) =
      subst ![(X 0 : MvPowerSeries (Fin 3) A), subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A))]
        (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)) := by
  set F := lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
  have hf0 := hf.constantCoeff_eq_zero
  have hF := isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
  set Y : Fin 3 → MvPowerSeries (Fin 3) A := X with hYdef
  have hY : ∀ i : Fin 3, IsLubinTateLift f f (Y i) (Y i) := isLubinTateLift_X hf0
  have h01 := hF.comp hf0 hf0 (v := ![Y 0, Y 1]) (u := ![Y 0, Y 1])
    (fun k => by fin_cases k <;> simpa using hY _)
  have h12 := hF.comp hf0 hf0 (v := ![Y 1, Y 2]) (u := ![Y 1, Y 2])
    (fun k => by fin_cases k <;> simpa using hY _)
  have hP := hF.comp hf0 hf0 (v := ![subst ![Y 0, Y 1] (sum₂ (![1, 1] : Fin 2 → A)), Y 2])
    (u := ![subst ![Y 0, Y 1] F, Y 2]) (fun j => by
      fin_cases j
      · simpa using h01
      · simpa using hY 2)
  have hQ := hF.comp hf0 hf0 (v := ![Y 0, subst ![Y 1, Y 2] (sum₂ (![1, 1] : Fin 2 → A))])
    (u := ![Y 0, subst ![Y 1, Y 2] F]) (fun j => by
      fin_cases j
      · simpa using hY 0
      · simpa using h12)
  have e01 : subst ![Y 0, Y 1] (sum₂ (![1, 1] : Fin 2 → A)) = Y 0 + Y 1 :=
    subst_linearForm_one_one (by simp [Y]) (by simp [Y])
  have e12 : subst ![Y 1, Y 2] (sum₂ (![1, 1] : Fin 2 → A)) = Y 1 + Y 2 :=
    subst_linearForm_one_one (by simp [Y]) (by simp [Y])
  have hP' := eq_lubinTateLift_of hπ hf hf hP (a := ![1, 1, 1]) (by
    rw [e01, subst_linearForm_one_one (by simp [Y]) (by simp [Y])]
    simp [sum₂, Fin.sum_univ_three, Y])
  have hQ' := eq_lubinTateLift_of hπ hf hf hQ (a := ![1, 1, 1]) (by
    rw [e12, subst_linearForm_one_one (by simp [Y]) (by simp [Y])]
    simp [sum₂, Fin.sum_univ_three, Y, add_assoc])
  exact hP'.trans hQ'.symm

theorem lubinTateLift_comm (hf : IsLubinTateSeries π f) :
    lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A) =
      subst ![(X 1 : MvPowerSeries (Fin 2) A), X 0] (lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)) := by
  have hf0 := hf.constantCoeff_eq_zero
  have hR := (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)).comp hf0 hf0
    (v := ![(X 1 : MvPowerSeries (Fin 2) A), X 0]) (u := ![(X 1 : MvPowerSeries (Fin 2) A), X 0]) (fun j => by fin_cases j <;> exact isLubinTateLift_X hf0 _)
  refine (eq_lubinTateLift_of hπ hf hf hR ?_).symm
  rw [subst_linearForm_one_one (by simp) (by simp)]
  simp [sum₂, Fin.sum_univ_two, add_comm]

noncomputable def lubinTateFormalGroup (hf : IsLubinTateSeries π f) : FormalGroup A where
  toPowerSeries := lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
  zero_constantCoeff := constantCoeff_lubinTateLift hπ hf hf _
  lin_coeff_X := by
    rw [coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hf _) (by simp),
      linearForm_fin_two]
    simp [coeff_X, single_zero_ne_single_one, single_zero_ne_single_one.symm]
  lin_coeff_Y := by
    rw [coeff_eq_of_two_le_order_sub (two_le_order_lubinTateLift_sub hπ hf hf _) (by simp),
      linearForm_fin_two]
    simp [coeff_X, single_zero_ne_single_one, single_zero_ne_single_one.symm]
  assoc := lubinTateLift_assoc hπ hf

theorem lubinTateFormalGroup_toPowerSeries (hf : IsLubinTateSeries π f) :
    (lubinTateFormalGroup hπ hf).toPowerSeries = lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A) :=
  rfl

instance (hf : IsLubinTateSeries π f) : (lubinTateFormalGroup hπ hf).IsComm :=
  ⟨lubinTateLift_comm hπ hf⟩

noncomputable def lubinTateEndo (hf : IsLubinTateSeries π f) :
    Hom (lubinTateFormalGroup hπ hf) (lubinTateFormalGroup hπ hf) where
  toPowerSeries := f
  constantCoeff_eq_zero := hf.constantCoeff_eq_zero
  map_add := by
    have := subst_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)
    rw [substEach_fin_two] at this
    exact this

theorem eq_lubinTateFormalGroup (hf : IsLubinTateSeries π f) (F : FormalGroup A) (φ : Hom F F)
    (hφ : φ.toPowerSeries = f) : F = lubinTateFormalGroup hπ hf := by
  apply FormalGroup.ext
  refine eq_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A) ?_ ?_
  · have h2 := two_le_order_higher F
    have e : higher F = F.toPowerSeries - X 0 - X 1 := rfl
    rwa [e, sub_sub, ← one_mul (X 0 : MvPowerSeries (Fin 2) A), ← one_mul (X 1 : MvPowerSeries (Fin 2) A),
      ← map_one (C : A →+* MvPowerSeries (Fin 2) A), ← linearForm_fin_two] at h2
  · have := φ.map_add
    rw [hφ] at this
    rw [substEach_fin_two]
    exact this

theorem existsUnique_formalGroup (hf : IsLubinTateSeries π f) :
    ∃! F : FormalGroup A, ∃ φ : Hom F F, φ.toPowerSeries = f :=
  ⟨lubinTateFormalGroup hπ hf, ⟨lubinTateEndo hπ hf, rfl⟩,
    fun F ⟨φ, hφ⟩ => eq_lubinTateFormalGroup hπ hf F φ hφ⟩

end LubinTate

section LubinTateHom

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A} (hπ : Irreducible π) {f g h : PowerSeries A}
include hπ

theorem isLubinTateLift_subst_X (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (a : A) {σ : Type*} [Finite σ] (j : σ) :
    IsLubinTateLift f g (C a * X j)
      (PowerSeries.subst (X j : MvPowerSeries σ A) (lubinTateLift hπ hf hg fun _ : Unit => a)) := by
  have hg0 := hg.constantCoeff_eq_zero
  have := (isLubinTateLift_lubinTateLift hπ hf hg fun _ : Unit => a).comp hg0 hg0
    (v := fun _ => X j) (u := fun _ => X j) (fun _ => isLubinTateLift_X hg0 j)
  rw [subst_linearForm (hasSubst_of_constantCoeff_zero fun _ => by simp)] at this
  simpa [PowerSeries.subst_def] using this

theorem lubinTateHom_map_add (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (a : A) :
    PowerSeries.subst (lubinTateFormalGroup hπ hg).toPowerSeries
        (lubinTateLift hπ hf hg fun _ : Unit => a) =
      subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a),
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a)]
        (lubinTateFormalGroup hπ hf).toPowerSeries := by
  have hf0 := hf.constantCoeff_eq_zero
  have hg0 := hg.constantCoeff_eq_zero
  have hL := (isLubinTateLift_lubinTateLift hπ hf hg fun _ : Unit => a).comp hg0 hg0
    (v := fun _ => sum₂ (![1, 1] : Fin 2 → A))
    (u := fun _ => (lubinTateFormalGroup hπ hg).toPowerSeries)
    (fun _ => isLubinTateLift_lubinTateLift hπ hg hg _)
  have hR := (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)).comp hf0 hg0
    (v := ![C a * X 0, C a * X 1])
    (u := ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a),
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A)
          (lubinTateLift hπ hf hg fun _ : Unit => a)])
    (fun j => by fin_cases j <;> simpa using isLubinTateLift_subst_X hπ hf hg a _)
  rw [PowerSeries.subst_def]
  refine (eq_lubinTateLift_of hπ hf hg hL (a := ![a, a]) ?_).trans
    (eq_lubinTateLift_of hπ hf hg hR ?_).symm
  · rw [subst_linearForm (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_linearForm _),
      linearForm_fin_two, linearForm_fin_two]
    simp only [Finset.univ_unique, Finset.sum_singleton, map_one, one_mul]
    ring
  · rw [subst_linearForm_one_one (by simp) (by simp), linearForm_fin_two]

noncomputable def lubinTateHom (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (a : A) :
    Hom (lubinTateFormalGroup hπ hg) (lubinTateFormalGroup hπ hf) where
  toPowerSeries := lubinTateLift hπ hf hg fun _ : Unit => a
  constantCoeff_eq_zero := constantCoeff_lubinTateLift hπ hf hg _
  map_add := lubinTateHom_map_add hπ hf hg a

variable (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (hh : IsLubinTateSeries π h)

theorem lubinTateHom_toPowerSeries (a : A) :
    (lubinTateHom hπ hf hg a).toPowerSeries = lubinTateLift hπ hf hg fun _ : Unit => a :=
  rfl

theorem isLubinTateLift_lubinTateHom (a : A) :
    IsLubinTateLift f g (PowerSeries.C a * PowerSeries.X) (lubinTateHom hπ hf hg a).toPowerSeries :=
  linearForm_unit a ▸ isLubinTateLift_lubinTateLift hπ hf hg _

theorem subst_lubinTateHom (a : A) :
    PowerSeries.subst (lubinTateHom hπ hf hg a).toPowerSeries f =
      PowerSeries.subst g (lubinTateHom hπ hf hg a).toPowerSeries := by
  have := subst_lubinTateLift hπ hf hg (fun _ : Unit => a)
  rw [subst_substEach_unit] at this
  exact this

theorem coeff_one_lubinTateHom (a : A) :
    PowerSeries.coeff 1 (lubinTateHom hπ hf hg a).toPowerSeries = a := by
  have := coeff_eq_of_two_le_order_sub (isLubinTateLift_lubinTateHom hπ hf hg a).2.1
    (e := Finsupp.single () 1) (by simp)
  change coeff (Finsupp.single () 1) _ = a
  rw [this]
  change PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X) = a
  simp

theorem eq_lubinTateHom_toPowerSeries (a : A) {φ : PowerSeries A}
    (h0 : PowerSeries.constantCoeff φ = 0) (h1 : PowerSeries.coeff 1 φ = a)
    (h : PowerSeries.subst φ f = PowerSeries.subst g φ) :
    φ = (lubinTateHom hπ hf hg a).toPowerSeries := by
  refine eq_lubinTateLift hπ hf hg _ ?_ ?_
  · rw [linearForm_unit]
    exact two_le_order_sub_C_mul_X h0 h1
  · rw [subst_substEach_unit]
    exact h

theorem lubinTateHom_add (a b : A) :
    lubinTateHom hπ hf hg (a + b) = lubinTateHom hπ hf hg a + lubinTateHom hπ hf hg b := by
  have hf0 := hf.constantCoeff_eq_zero
  have hg0 := hg.constantCoeff_eq_zero
  apply Hom.ext
  rw [Hom.toPowerSeries_add, lubinTateFormalGroup_toPowerSeries]
  have hS := (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)).comp hf0 hg0
    (v := ![sum₂ fun _ : Unit => a, sum₂ fun _ : Unit => b])
    (u := ![(lubinTateHom hπ hf hg a).toPowerSeries, (lubinTateHom hπ hf hg b).toPowerSeries])
    (fun j => by
      fin_cases j <;> simpa [lubinTateHom_toPowerSeries] using isLubinTateLift_lubinTateLift hπ hf hg _)
  refine (eq_lubinTateLift_of hπ hf hg hS ?_).symm
  rw [subst_linearForm_one_one (constantCoeff_linearForm _) (constantCoeff_linearForm _)]
  simp only [sum₂, Finset.univ_unique, Finset.sum_singleton, map_add]
  ring

theorem lubinTateHom_mul (a b : A) :
    lubinTateHom hπ hf hh (a * b) = (lubinTateHom hπ hf hg a).comp (lubinTateHom hπ hg hh b) := by
  have hg0 := hg.constantCoeff_eq_zero
  have hh0 := hh.constantCoeff_eq_zero
  apply Hom.ext
  rw [Hom.toPowerSeries_comp, PowerSeries.subst_def]
  have hS := (isLubinTateLift_lubinTateLift hπ hf hg fun _ : Unit => a).comp hg0 hh0
    (v := fun _ => sum₂ fun _ : Unit => b)
    (u := fun _ => (lubinTateHom hπ hg hh b).toPowerSeries)
    (fun _ => isLubinTateLift_lubinTateLift hπ hg hh _)
  refine (eq_lubinTateLift_of hπ hf hh hS ?_).symm
  rw [subst_linearForm (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_linearForm _)]
  simp only [sum₂, Finset.univ_unique, Finset.sum_singleton, map_mul]
  ring

theorem lubinTateHom_self_uniformizer :
    (lubinTateHom hπ hf hf π).toPowerSeries = f :=
  (eq_lubinTateHom_toPowerSeries hπ hf hf π hf.constantCoeff_eq_zero hf.coeff_one rfl).symm

theorem lubinTateHom_self_one : lubinTateHom hπ hf hf 1 = Hom.id _ := by
  apply Hom.ext
  rw [Hom.toPowerSeries_id]
  refine (eq_lubinTateHom_toPowerSeries hπ hf hf 1 (by simp) (by simp) ?_).symm
  rw [PowerSeries.X_subst, PowerSeries.subst_X
    (PowerSeries.HasSubst.of_constantCoeff_zero' hf.constantCoeff_eq_zero)]

theorem lubinTateHom_zero : lubinTateHom hπ hf hg 0 = 0 := by
  apply Hom.ext
  rw [Hom.toPowerSeries_zero]
  refine (eq_lubinTateHom_toPowerSeries hπ hf hg 0 (by simp) (by simp) ?_).symm
  rw [PowerSeries.subst_zero_of_constantCoeff_zero hf.constantCoeff_eq_zero,
    ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg.constantCoeff_eq_zero), map_zero]

noncomputable def lubinTateEndRingHom :
    A →+* Hom (lubinTateFormalGroup hπ hf) (lubinTateFormalGroup hπ hf) where
  toFun a := lubinTateHom hπ hf hf a
  map_one' := lubinTateHom_self_one hπ hf
  map_mul' a b := lubinTateHom_mul hπ hf hf hf a b
  map_zero' := lubinTateHom_zero hπ hf hf
  map_add' a b := lubinTateHom_add hπ hf hf a b

theorem lubinTateEndRingHom_apply (a : A) : lubinTateEndRingHom hπ hf a = lubinTateHom hπ hf hf a :=
  rfl

noncomputable def lubinTateFormalModule : FormalModule (lubinTateFormalGroup hπ hf) where
  smul := lubinTateEndRingHom hπ hf
  linearCoeff_smul a := coeff_one_lubinTateHom hπ hf hf a

noncomputable def lubinTateIso (u : Aˣ) :
    Iso (lubinTateFormalGroup hπ hg) (lubinTateFormalGroup hπ hf) :=
  Iso.ofIsUnit (lubinTateHom hπ hf hg u) (by rw [coeff_one_lubinTateHom]; exact u.isUnit)

theorem lubinTateIso_hom (u : Aˣ) : (lubinTateIso hπ hf hg u).hom = lubinTateHom hπ hf hg u :=
  rfl

end LubinTateHom

end GroundTheory.LocalField.FormalGroup
