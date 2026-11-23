import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.PadicUnitSub

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_max_norm {ι : Type*} [Nonempty ι] (f : ι → ℤ_[l]) :
    ∃ i, ∀ j, ‖f j‖ ≤ ‖f i‖ := by
  classical
  by_cases h0 : ∀ j, f j = 0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, fun j => by rw [h0 j, h0 i]⟩
  · push_neg at h0
    have hex : ∃ n, ∃ j, f j ≠ 0 ∧ (f j).valuation = n := by
      obtain ⟨j, hj⟩ := h0
      exact ⟨_, j, hj, rfl⟩
    obtain ⟨i, hi, hiv⟩ := Nat.find_spec hex
    refine ⟨i, fun j => ?_⟩
    by_cases hj : f j = 0
    · rw [hj, norm_zero]; exact norm_nonneg _
    · have hle : Nat.find hex ≤ (f j).valuation := Nat.find_min' hex ⟨j, hj, rfl⟩
      rw [PadicInt.norm_eq_zpow_neg_valuation hj, PadicInt.norm_eq_zpow_neg_valuation hi, hiv]
      apply zpow_le_zpow_right₀ (by exact_mod_cast hl.out.one_lt.le)
      omega

theorem eq_one_of_pow_eq_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) (k : ℕ) (hk : 0 < k) (h : x ^ k = 1) : x = 1 := by
  have e := GlobalTheory.Cyc.norm_pow_nat_sub_one k hk.ne' x hx h2
  rw [h, sub_self, norm_zero] at e
  have hk' : ‖(k : ℤ_[l])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact_mod_cast hk.ne'
  rcases mul_eq_zero.1 e.symm with h' | h'
  · exact sub_eq_zero.1 (norm_eq_zero.1 h')
  · exact absurd h' hk'

theorem eq_of_torsion (u v : ℤ_[l]ˣ) (hu : IsOfFinOrder u) (hv : IsOfFinOrder v)
    (hx : ‖(u : ℤ_[l]) - v‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖(u : ℤ_[l]) - v‖ < (l : ℝ)⁻¹) : u = v := by
  have hw : IsOfFinOrder (u * v⁻¹) := hu.mul hv.inv
  have hnorm : ‖((u * v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = ‖(u : ℤ_[l]) - v‖ := by
    have e : ((u * v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((u : ℤ_[l]) - v) * ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [sub_mul, Units.mul_inv, Units.val_mul]
    rw [e, norm_mul, PadicInt.norm_units, mul_one]
  have h1 := eq_one_of_pow_eq_one _ (by rw [hnorm]; exact hx) (fun h => by rw [hnorm]; exact h2 h)
    (orderOf (u * v⁻¹)) hw.orderOf_pos
    (by rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one])
  have : u * v⁻¹ = 1 := Units.ext (h1.trans Units.val_one.symm)
  exact mul_inv_eq_one.1 this

theorem norm_le_of_toZModPow_eq (n : ℕ) (a b : ℤ_[l])
    (h : PadicInt.toZModPow n a = PadicInt.toZModPow n b) : ‖a - b‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h,
    sub_self]

theorem finite_torsion : {u : ℤ_[l]ˣ | IsOfFinOrder u}.Finite := by
  have : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  refine Set.Finite.of_finite_image
    (f := fun u : ℤ_[l]ˣ => PadicInt.toZModPow 2 (u : ℤ_[l])) (Set.toFinite _) ?_
  intro u hu v hv huv
  have hle := norm_le_of_toZModPow_eq 2 (u : ℤ_[l]) v huv
  have hlt : (l : ℝ) ^ (-((2 : ℕ) : ℤ)) < (l : ℝ)⁻¹ := by
    have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ h1 (by norm_num)
  exact eq_of_torsion u v hu hv (hle.trans hlt.le) (fun _ => hle.trans_lt hlt)

theorem norm_le_inv_of_lt_one (x : ℤ_[l]) (h : ‖x‖ < 1) : ‖x‖ ≤ (l : ℝ)⁻¹ := by
  have := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one x 0).1 (by simpa using h)
  simpa using this

theorem norm_lt_one_iff_toZMod (x : ℤ_[l]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma norm_natCast_padicInt_eq_one_of_not_dvd (n : ℕ) (h : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (n : ℤ)).1 (by rw [Int.cast_natCast]; exact hlt)
  exact_mod_cast this

theorem exists_teich (g : ℤ_[l]ˣ) :
    ∃ w : ℤ_[l]ˣ, IsOfFinOrder w ∧ ‖(w : ℤ_[l]) - g‖ < 1 := by
  have hl2 := hl.out.two_le
  set F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1 with hF
  have hder : ‖F.derivative.aeval (g : ℤ_[l])‖ = 1 := by
    have hn : ¬ l ∣ (l - 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Algebra.algebraMap_self, RingHom.id_apply, norm_mul, norm_pow, PadicInt.norm_units, one_pow,
      mul_one]
    exact_mod_cast norm_natCast_padicInt_eq_one_of_not_dvd (l - 1) hn
  have hval : ‖F.aeval (g : ℤ_[l])‖ < 1 := by
    have hg0 : PadicInt.toZMod (g : ℤ_[l]) ≠ 0 := (g.isUnit.map PadicInt.toZMod).ne_zero
    rw [norm_lt_one_iff_toZMod]
    simp only [hF, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_one, map_sub, map_pow,
      map_one]
    rw [ZMod.pow_card_sub_one_eq_one hg0, sub_self]
  obtain ⟨z, hz, hzg, -, -⟩ := hensels_lemma (F := F) (a := (g : ℤ_[l]))
    (by rw [hder, one_pow]; exact hval)
  rw [hder] at hzg
  have hz' : z ^ (l - 1) = 1 := by
    simpa [hF, sub_eq_zero] using hz
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz' (by omega)
  refine ⟨hu.unit, isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, by omega, Units.ext ?_⟩, ?_⟩
  · rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz', Units.val_one]
  · rw [IsUnit.unit_spec]; exact hzg

private lemma padicInt_norm_natCast_eq_one_of_not_dvd (n : ℕ) (h : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (n : ℤ)).1 (by rw [Int.cast_natCast]; exact hlt)
  exact_mod_cast this

theorem exists_gam_gamK_torsion :
    ∀ (l : ℕ) [Fact l.Prime] (s : ℕ) (Γ : Subgroup ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → u ∈ Γ) → ∃ (gam gamK : ↥Γ) (D : Finset ↥Γ), ‖((gam : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ (∀ g, g ∈ D ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1) ∧ (∀ g : ↥Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖ ≤ ‖((gamK : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖) ∧ ((∀ g : ↥Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖ ≤ ‖((gam : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖) → gamK = gam) ∧ (s = 1 → l ≠ 2 → gamK = gam) := by
  intro l _ s Γ hs hs2 hΓ
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hls : ‖((l : ℤ_[l]) ^ s)‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, inv_pow]
  have hlt1 : ‖((l : ℤ_[l]) ^ s)‖ < 1 := by
    rw [hls]; exact zpow_lt_one_of_neg₀ hl1 (by omega)
  have hunit : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
    rw [PadicInt.isUnit_iff, GlobalTheory.Cyc.padicInt_norm_add_eq_of_lt (by rwa [norm_one]), norm_one]
  have hg0 : (hunit.unit : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s := hunit.unit_spec
  have hg0Γ : hunit.unit ∈ Γ := hΓ _ (by rw [hg0, add_sub_cancel_left])

  have hTfin : ((CommGroup.torsion Γ : Subgroup Γ) : Set Γ).Finite := by
    refine (finite_torsion.preimage Subtype.val_injective.injOn).subset ?_
    intro g hg
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion g).1 hg)
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← Subgroup.coe_pow, hgk, Subgroup.coe_one]⟩
  have hD : ∀ g, g ∈ hTfin.toFinset ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1 := by
    intro g
    rw [Set.Finite.mem_toFinset, SetLike.mem_coe, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hDcard : hTfin.toFinset.card = Nat.card (CommGroup.torsion Γ) := by
    rw [← Nat.card_eq_card_finite_toFinset hTfin]; rfl
  have hDpow : ∀ g ∈ CommGroup.torsion Γ, g ^ hTfin.toFinset.card = 1 := by
    intro g hg
    have h1 := congrArg Subtype.val
      (pow_card_eq_one' (G := CommGroup.torsion Γ) (x := ⟨g, hg⟩))
    rw [hDcard]
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hNpos : 0 < hTfin.toFinset.card :=
    Finset.card_pos.2 ⟨1, (hD 1).2 ⟨1, one_pos, one_pow _⟩⟩
  obtain ⟨gmax, hgmax⟩ :=
    exists_max_norm (l := l) (fun g : Γ => ((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1)
  obtain ⟨gamK, hK1, hK2⟩ : ∃ gamK : Γ,
      (∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖((gamK : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖) ∧
      ((∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖(((⟨hunit.unit, hg0Γ⟩ : Γ) : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖) →
        gamK = ⟨hunit.unit, hg0Γ⟩) := by
    by_cases hc : ∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖(((⟨hunit.unit, hg0Γ⟩ : Γ) : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖
    · exact ⟨⟨hunit.unit, hg0Γ⟩, hc, fun _ => rfl⟩
    · exact ⟨gmax, hgmax, fun h => absurd h hc⟩
  refine ⟨⟨hunit.unit, hg0Γ⟩, gamK, hTfin.toFinset, ?_, hD, hK1, hK2, ?_⟩
  · show ‖(hunit.unit : ℤ_[l]) - 1‖ = _
    rw [hg0, add_sub_cancel_left, hls]
  · intro hs1 hl2
    subst hs1
    apply hK2

    have hcard : hTfin.toFinset.card < l := by
      have hle : hTfin.toFinset.card ≤ (Finset.univ.erase (0 : ZMod l)).card := by
        refine Finset.card_le_card_of_injOn (fun g : Γ => PadicInt.toZMod ((g : ℤ_[l]ˣ) : ℤ_[l]))
          ?_ ?_
        · intro g _
          simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
            Set.mem_singleton_iff, true_and, Finset.mem_erase, Finset.mem_univ, and_true]
          exact ((g : ℤ_[l]ˣ).isUnit.map PadicInt.toZMod).ne_zero
        · intro g hg h hh hgh
          have hgD := (hD g).1 hg
          have hhD := (hD h).1 hh
          obtain ⟨a, ha, hga⟩ := hgD
          obtain ⟨b, hb, hhb⟩ := hhD
          have hlt : ‖((g : ℤ_[l]ˣ) : ℤ_[l]) - ((h : ℤ_[l]ˣ) : ℤ_[l])‖ < 1 := by
            rw [norm_lt_one_iff_toZMod, map_sub, sub_eq_zero]; exact hgh
          apply Subtype.ext
          refine eq_of_torsion _ _ (isOfFinOrder_iff_pow_eq_one.2 ⟨a, ha, ?_⟩)
            (isOfFinOrder_iff_pow_eq_one.2 ⟨b, hb, ?_⟩) (norm_le_inv_of_lt_one _ hlt)
            (fun h2 => absurd h2 hl2)
          · rw [← Subgroup.coe_pow, hga, Subgroup.coe_one]
          · rw [← Subgroup.coe_pow, hhb, Subgroup.coe_one]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at hle
      have := hlp.two_le
      omega
    have hN : ‖((hTfin.toFinset.card : ℕ) : ℤ_[l])‖ = 1 :=
      padicInt_norm_natCast_eq_one_of_not_dvd _ (Nat.not_dvd_of_pos_of_lt hNpos hcard)
    have hgam1 : ‖(hunit.unit : ℤ_[l]) - 1‖ = (l : ℝ)⁻¹ := by
      rw [hg0, add_sub_cancel_left, pow_one, PadicInt.norm_p]
    have hgam : ‖(hunit.unit : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ = (l : ℝ)⁻¹ := by
      rw [GlobalTheory.Cyc.norm_pow_nat_sub_one _ hNpos.ne' _ hgam1.le (fun h2 => absurd h2 hl2), hgam1, hN,
        mul_one]
    intro g
    show _ ≤ ‖(hunit.unit : ℤ_[l]) ^ hTfin.toFinset.card - 1‖
    rw [hgam]
    obtain ⟨w, hw, hwg⟩ := exists_teich (g : ℤ_[l]ˣ)

    have hwΓ : w ∈ Γ := by
      have hmul : w * (g : ℤ_[l]ˣ)⁻¹ ∈ Γ := by
        apply hΓ
        rw [pow_one, ← PadicInt.norm_lt_one_iff_dvd]
        have e : ((w * (g : ℤ_[l]ˣ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
            ((w : ℤ_[l]) - ((g : ℤ_[l]ˣ) : ℤ_[l])) * (((g : ℤ_[l]ˣ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
          rw [sub_mul, Units.mul_inv, Units.val_mul]
        rw [e, norm_mul, PadicInt.norm_units, mul_one]
        exact hwg
      have := Γ.mul_mem hmul g.2
      rwa [inv_mul_cancel_right] at this
    have hwT : (⟨w, hwΓ⟩ : Γ) ∈ CommGroup.torsion Γ := by
      obtain ⟨k, hk, hwk⟩ := isOfFinOrder_iff_pow_eq_one.1 hw
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hwk)⟩
    have hwN : (w : ℤ_[l]) ^ hTfin.toFinset.card = 1 := by
      have h1 := congrArg (fun x : Γ => ((x : ℤ_[l]ˣ) : ℤ_[l])) (hDpow _ hwT)
      simpa using h1
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ((g : ℤ_[l]ˣ) : ℤ_[l]) (w : ℤ_[l]) hTfin.toFinset.card
    apply norm_le_inv_of_lt_one
    rw [← hwN, hc, norm_mul, norm_sub_rev]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one c)) hwg

end GlobalTheory.PadicUnitSub
