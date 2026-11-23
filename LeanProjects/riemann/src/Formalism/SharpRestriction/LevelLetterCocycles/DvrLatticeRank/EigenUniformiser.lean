import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero

namespace DualFramesAlt.EigenUniformiser

open PowerSeries

structure Data (O : Type*) [CommRing O] (Δ : Type*) [Group Δ] [Fintype Δ] where
  ρ : Δ →* (PowerSeries O ≃ₐ[O] PowerSeries O)
  ω : Δ →* Oˣ
  hω : Function.Injective ω
  v : Δ → PowerSeries O
  hv : ∀ δ, ρ δ X = X * v δ
  hv0 : ∀ δ, constantCoeff (v δ) = (ω δ : O)

variable {O : Type*} [CommRing O] [IsDomain O] {Δ : Type*} [Group Δ] [Fintype Δ] [IsCyclic Δ]

noncomputable def piPrime (D : Data O Δ) : PowerSeries O := ∏ δ, D.ρ δ X

noncomputable def pi1 (D : Data O Δ) (hs : IsUnit (Fintype.card Δ : O)) : PowerSeries O :=
  ((hs.unit⁻¹ : Oˣ) : O) • ∑ δ, (((D.ω δ)⁻¹ : Oˣ) : O) • D.ρ δ X

section Lemmas

variable (D : Data O Δ)

theorem constantCoeff_rho_X (δ : Δ) : constantCoeff (D.ρ δ X) = 0 := by
  rw [D.hv, map_mul, constantCoeff_X, zero_mul]

theorem rho_rho_X (δ ε : Δ) : D.ρ δ (D.ρ ε X) = D.ρ (δ * ε) X := by
  rw [map_mul, AlgEquiv.mul_apply]

theorem rho_subst (δ : Δ) {p : PowerSeries O} (hp : constantCoeff p = 0) (g : PowerSeries O) :
    D.ρ δ (PowerSeries.subst p g) = PowerSeries.subst (D.ρ δ p) g :=
  algHom_subst (D.ρ δ).toAlgHom (constantCoeff_rho_X D δ) hp g

theorem omega_pow_card (δ : Δ) : ((D.ω δ : Oˣ) : O) ^ Fintype.card Δ = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

theorem card_ne_zero : Fintype.card Δ ≠ 0 := Fintype.card_ne_zero

theorem piPrime_invariant (δ : Δ) : D.ρ δ (piPrime D) = piPrime D := by
  unfold piPrime
  rw [map_prod]
  simp_rw [rho_rho_X]
  exact Equiv.prod_comp (Equiv.mulLeft δ) (fun ε => D.ρ ε X)

variable (hs : IsUnit (Fintype.card Δ : O))

theorem coeff_eigen_uniformiser (n : ℕ) : coeff n (pi1 D hs) =
    ((hs.unit⁻¹ : Oˣ) : O) * ∑ δ, (((D.ω δ)⁻¹ : Oˣ) : O) * coeff n (D.ρ δ X) := by
  simp [pi1, map_sum, smul_eq_mul]

theorem coeff_zero_eigen_uniformiser : coeff 0 (pi1 D hs) = 0 := by
  rw [coeff_eigen_uniformiser]
  simp [D.hv]

theorem coeff_one_eigen_uniformiser : coeff 1 (pi1 D hs) = 1 := by
  rw [coeff_eigen_uniformiser]
  have h1 : ∀ δ, coeff 1 (D.ρ δ X) = (D.ω δ : O) := by
    intro δ
    rw [D.hv, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      D.hv0]
  simp_rw [h1, Units.inv_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact hs.val_inv_mul

theorem constantCoeff_eigen_uniformiser : constantCoeff (pi1 D hs) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_eigen_uniformiser]

theorem isUnit_coeff_one_eigen_uniformiser : IsUnit (coeff 1 (pi1 D hs)) := by
  rw [coeff_one_eigen_uniformiser]; exact isUnit_one

theorem rho_eigen_uniformiser (δ : Δ) : D.ρ δ (pi1 D hs) = (D.ω δ : O) • pi1 D hs := by
  unfold pi1
  rw [map_smul, map_sum]
  simp_rw [map_smul, rho_rho_X]
  have key : ∑ ε, (((D.ω ε)⁻¹ : Oˣ) : O) • D.ρ (δ * ε) X =
      (D.ω δ : O) • ∑ η, (((D.ω η)⁻¹ : Oˣ) : O) • D.ρ η X := by
    conv_rhs => rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft δ)]
    refine Finset.sum_congr rfl fun ε _ => ?_
    simp only [Equiv.coe_mulLeft]
    rw [smul_smul]
    congr 1
    have hu : (D.ω ε)⁻¹ = D.ω δ * (D.ω (δ * ε))⁻¹ := by
      rw [map_mul, mul_inv, mul_inv_cancel_left]
    rw [hu, Units.val_mul]
  rw [key]
  exact smul_comm _ _ _

theorem uniformiser_pow_card_subst (g : PowerSeries O) :
    PowerSeries.subst (pi1 D hs) (PowerSeries.subst (X ^ Fintype.card Δ : PowerSeries O) g) =
      PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) g := by
  have hp := HasSubst.of_constantCoeff_zero' (constantCoeff_eigen_uniformiser D hs)
  rw [subst_comp_subst_apply (HasSubst.X_pow (card_ne_zero (Δ := Δ))) hp, subst_pow hp,
    subst_X hp]

theorem rho_subst_uniformiser (δ : Δ) (g : PowerSeries O) :
    D.ρ δ (PowerSeries.subst (pi1 D hs) g) =
      PowerSeries.subst (pi1 D hs) (rescale (D.ω δ : O) g) := by
  have hp := HasSubst.of_constantCoeff_zero' (constantCoeff_eigen_uniformiser D hs)
  rw [rho_subst D δ (constantCoeff_eigen_uniformiser D hs), rho_eigen_uniformiser, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' _) hp, subst_smul hp, subst_X hp]

theorem invariant_subst_iff_card_dvd (g : PowerSeries O) :
    (∀ δ, D.ρ δ (PowerSeries.subst (pi1 D hs) g) = PowerSeries.subst (pi1 D hs) g) ↔
      ∀ k, coeff k g ≠ 0 → Fintype.card Δ ∣ k := by
  constructor
  · intro H k hk
    obtain ⟨δ₀, hδ₀⟩ := IsCyclic.exists_generator (α := Δ)
    have h := H δ₀
    rw [rho_subst_uniformiser] at h
    have h2 := congrArg (coeff k)
      (subst_injective (constantCoeff_eigen_uniformiser D hs) (isUnit_coeff_one_eigen_uniformiser D hs) h)
    rw [coeff_rescale] at h2
    have h3 : (((D.ω δ₀ : Oˣ) : O) ^ k - 1) * coeff k g = 0 := by
      rw [sub_mul, h2, one_mul, sub_self]
    have h4 : ((D.ω δ₀ : Oˣ) : O) ^ k = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hk)
    have h5 : δ₀ ^ k = 1 := by
      apply D.hω
      rw [map_pow, map_one]
      ext
      rw [Units.val_pow_eq_pow_val, h4, Units.val_one]
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [orderOf_eq_card_of_forall_mem_zpowers hδ₀] at h6
    simpa [Nat.card_eq_fintype_card] using h6
  · intro H δ
    rw [rho_subst_uniformiser]
    congr 1
    ext k
    rw [coeff_rescale]
    by_cases hk : coeff k g = 0
    · rw [hk, mul_zero]
    · obtain ⟨t, rfl⟩ := H k hk
      rw [pow_mul, omega_pow_card, one_pow, one_mul]

end Lemmas

theorem piPrime_eq (D : Data O Δ) :
    ∃ v' : PowerSeries O, IsUnit v' ∧ piPrime D = X ^ Fintype.card Δ * v' ∧
      constantCoeff v' = ∏ δ, (D.ω δ : O) := by
  refine ⟨∏ δ, D.v δ, ?_, ?_, ?_⟩
  · rw [isUnit_iff_constantCoeff, map_prod]
    simp_rw [D.hv0]
    rw [← Units.coe_prod]
    exact Units.isUnit _
  · unfold piPrime
    simp_rw [D.hv]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  · rw [map_prod]
    simp_rw [D.hv0]

theorem eigen_uniformiser_props (D : Data O Δ) (hs : IsUnit (Fintype.card Δ : O)) :
    pi1 D hs - X ∈ (Ideal.span {X ^ 2} : Ideal (PowerSeries O)) ∧
    (∀ δ, D.ρ δ (pi1 D hs) = (D.ω δ : O) • pi1 D hs) ∧
    (∀ f : PowerSeries O, ∃ g : PowerSeries O, f = PowerSeries.subst (pi1 D hs) g) := by
  refine ⟨?_, rho_eigen_uniformiser D hs, subst_surjective (constantCoeff_eigen_uniformiser D hs) (isUnit_coeff_one_eigen_uniformiser D hs)⟩
  rw [Ideal.mem_span_singleton, X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · rw [map_sub, coeff_zero_eigen_uniformiser, coeff_zero_X, sub_zero]
  · rw [map_sub, coeff_one_eigen_uniformiser, coeff_one_X, sub_self]

theorem invariants (D : Data O Δ) (hs : IsUnit (Fintype.card Δ : O)) :
    (∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
        ∃ g : PowerSeries O, f = PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) g) ∧
    (∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
        ∃ g : PowerSeries O, f = PowerSeries.subst (piPrime D) g) ∧
    (∀ f : PowerSeries O, ∃! a : Fin (Fintype.card Δ) → PowerSeries O,
        f = ∑ j : Fin (Fintype.card Δ), pi1 D hs ^ (j : ℕ) * PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) (a j)) ∧
    (∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) → constantCoeff f = 0 →
        ∃ g : PowerSeries O, (∀ δ, D.ρ δ g = g) ∧ f = piPrime D * g) := by
  have hs0 : Fintype.card Δ ≠ 0 := card_ne_zero
  have hp0 := constantCoeff_eigen_uniformiser D hs
  have hp1 := isUnit_coeff_one_eigen_uniformiser D hs
  have hps0 : constantCoeff (pi1 D hs ^ Fintype.card Δ) = 0 := by
    rw [map_pow, hp0, zero_pow hs0]
  have hps := HasSubst.of_constantCoeff_zero' hps0
  have part1 : ∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
      ∃ g : PowerSeries O, f = PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) g := by
    intro f
    obtain ⟨g, rfl⟩ := subst_surjective hp0 hp1 f
    rw [invariant_subst_iff_card_dvd D hs g]
    constructor
    · intro H
      exact ⟨_, by rw [← uniformiser_pow_card_subst D hs, ← subst_X_pow_of_dvd hs0 g H]⟩
    · rintro ⟨h, hh⟩ k hk
      rw [← uniformiser_pow_card_subst D hs] at hh
      rw [subst_injective hp0 hp1 hh] at hk
      exact dvd_of_coeff_subst_X_pow_ne_zero hs0 h k hk
  have hpp0 : constantCoeff (piPrime D) = 0 := by
    obtain ⟨v', -, hv', -⟩ := piPrime_eq D
    rw [hv', map_mul, map_pow, constantCoeff_X, zero_pow hs0, zero_mul]
  obtain ⟨P0, hP0⟩ := (part1 (piPrime D)).mp (piPrime_invariant D)
  have hP0c : constantCoeff P0 = 0 := by
    have e := congrArg constantCoeff hP0
    rw [subst_eq_C_add hps0, map_add, map_mul, hps0, zero_mul, add_zero, constantCoeff_C,
      hpp0] at e
    exact e.symm
  have hP0u : IsUnit (coeff 1 P0) := by
    obtain ⟨v', -, hv', hv'0⟩ := piPrime_eq D
    obtain ⟨w, hw⟩ : X ∣ pi1 D hs := X_dvd_iff.mpr hp0
    have hw0 : constantCoeff w = 1 := by
      have e := coeff_one_eigen_uniformiser D hs
      rwa [hw, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
        coeff_zero_eq_constantCoeff_apply] at e
    have e := hP0
    rw [subst_eq_C_add hps0, hP0c, map_zero, zero_add, subst_eq_C_add hps0, hv', hw] at e
    have e2 := congrArg (coeff (Fintype.card Δ)) e
    rw [mul_pow, mul_assoc (X ^ Fintype.card Δ)] at e2
    simp only [coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_add, map_pow, hv'0, hw0, constantCoeff_X,
      zero_pow hs0, one_pow, one_mul, zero_mul, add_zero, constantCoeff_C] at e2
    have e3 : constantCoeff (mk fun n => coeff (n + 1) P0) = coeff 1 P0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    rw [← e3, ← e2, ← Units.coe_prod]
    exact Units.isUnit _
  have hP0s : HasSubst P0 := HasSubst.of_constantCoeff_zero' hP0c
  have part2 : ∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) ↔
      ∃ g : PowerSeries O, f = PowerSeries.subst (piPrime D) g := by
    intro f
    rw [part1 f]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨PowerSeries.subst (substInvOfIsUnit P0 hP0u) g, ?_⟩
      rw [hP0, ← subst_comp_subst_apply hP0s hps, subst_subst_substInv hP0c hP0u]
    · rintro ⟨g, rfl⟩
      exact ⟨PowerSeries.subst P0 g, by rw [hP0, subst_comp_subst_apply hP0s hps]⟩
  have part3 : ∀ f : PowerSeries O, ∃! a : Fin (Fintype.card Δ) → PowerSeries O,
      f = ∑ j : Fin (Fintype.card Δ),
        pi1 D hs ^ (j : ℕ) * PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) (a j) := by
    intro f
    have hp := HasSubst.of_constantCoeff_zero' hp0
    have hE : ∀ a : Fin (Fintype.card Δ) → PowerSeries O,
        ∑ j : Fin (Fintype.card Δ),
          pi1 D hs ^ (j : ℕ) * PowerSeries.subst (pi1 D hs ^ Fintype.card Δ) (a j) =
        PowerSeries.subst (pi1 D hs) (∑ j : Fin (Fintype.card Δ),
          X ^ (j : ℕ) * PowerSeries.subst (X ^ Fintype.card Δ : PowerSeries O) (a j)) := by
      intro a
      rw [← coe_substAlgHom hp, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, coe_substAlgHom, subst_X hp, uniformiser_pow_card_subst]
    obtain ⟨g, rfl⟩ := subst_surjective hp0 hp1 f
    obtain ⟨a, ha, hu⟩ := existsUnique_sum_X_pow_mul_subst hs0 g
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · dsimp only
      rw [hE, ← ha]
    · dsimp only at hb ⊢
      rw [hE] at hb
      exact subst_injective hp0 hp1 hb
  have part4 : ∀ f : PowerSeries O, (∀ δ, D.ρ δ f = f) → constantCoeff f = 0 →
      ∃ g : PowerSeries O, (∀ δ, D.ρ δ g = g) ∧ f = piPrime D * g := by
    intro f hf hf0
    obtain ⟨h, rfl⟩ := (part2 f).mp hf
    refine ⟨PowerSeries.subst (piPrime D) (mk fun n => coeff (n + 1) h), (part2 _).mpr ⟨_, rfl⟩,
      ?_⟩
    have e := subst_eq_C_add hpp0 h
    have e0 := congrArg constantCoeff e
    rw [hf0, map_add, map_mul, hpp0, zero_mul, add_zero, constantCoeff_C] at e0
    rw [e, ← e0, map_zero, zero_add]
  exact ⟨part1, part2, part3, part4⟩

end DualFramesAlt.EigenUniformiser
