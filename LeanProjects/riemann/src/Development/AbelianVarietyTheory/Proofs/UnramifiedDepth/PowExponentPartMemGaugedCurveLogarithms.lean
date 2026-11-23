import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimits
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMemStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.TypPart

variable {C : Type} [Field C]

theorem ge_intCast (V : VF C) (a : ℤ) : V.Ge 0 (a : C) := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa using VF.ge_natCast (V := V) n
  · simpa using (VF.ge_natCast (V := V) n).neg

theorem v_prime_eq_zero (V : VF C) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l) : V.v (p : C) = 0 := by
  have hc : IsCoprime (p : ℤ) (V.l : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp V.l_prime).2 hpl)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : C) * (p : C) + (b : C) * (V.l : C) = 1 := by
    have := congrArg (fun z : ℤ => (z : C)) hab
    simpa using this
  have h0 : (0 : WithTop ℝ) ≤ V.v (p : C) := by simpa [VF.Ge] using VF.ge_natCast (V := V) p
  have ha : (0 : WithTop ℝ) ≤ V.v (a : C) := by simpa [VF.Ge] using ge_intCast V a
  have hb : (0 : WithTop ℝ) ≤ V.v (b : C) := by simpa [VF.Ge] using ge_intCast V b
  by_contra hne
  have hpos : (0 : WithTop ℝ) < V.v (p : C) := lt_of_le_of_ne h0 (Ne.symm hne)
  have e1 : (0 : WithTop ℝ) < V.v ((a : C) * (p : C)) := by
    rw [V.v.map_mul]; exact lt_of_lt_of_le hpos (le_add_of_nonneg_left ha)
  have e2 : (0 : WithTop ℝ) < V.v ((b : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]; exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hb)
  have := V.v.map_lt_add e1 e2
  rw [h1, V.v.map_one] at this
  exact lt_irrefl _ this

theorem ge_of_pow_eq_one (V : VF C) {ζ : C} {p : ℕ} (hp : 0 < p) (h : ζ ^ p = 1) : V.Ge 0 ζ := by
  have h1 : p • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_nsmul] at h1
    have h2 : p • t = 0 := by exact_mod_cast h1
    have h3 : t = 0 := by
      rw [nsmul_eq_mul] at h2
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by exact_mod_cast h) hp.ne'
      · exact h
    rw [h3]

theorem sum_pow_root {ζ : C} {p : ℕ} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ j) ^ m = if p ∣ m then (p : C) else 0 := by
  have e : ∀ j, (ζ ^ j) ^ m = (ζ ^ m) ^ j := fun j => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have hne : ζ ^ m - 1 ≠ 0 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 (sub_eq_zero.1 h'))
    have := geom_sum_mul (ζ ^ m) p
    rw [← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne

open Classical in

def filt (P : ℕ → Prop) (f : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => if P m then PowerSeries.coeff m f else 0

open Classical in
theorem coeff_filt (P : ℕ → Prop) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (filt P f) = if P m then PowerSeries.coeff m f else 0 := by
  simp [filt]

theorem sub_avg [CharZero C] {ζ : C} {p : ℕ} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (f : PowerSeries C) :
    f + -((p : C)⁻¹ • ∑ j ∈ Finset.range p, PowerSeries.rescale (ζ ^ j) f) = filt (fun m => ¬ p ∣ m) f := by
  ext m
  have hp' : (p : C) ≠ 0 := by exact_mod_cast hp.ne'
  rw [coeff_filt, map_add, map_neg, PowerSeries.coeff_smul, map_sum]
  simp_rw [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_pow_root hζ]
  by_cases h : p ∣ m
  · simp [h, hp']
  · simp [h]

theorem filt_filt (P Q : ℕ → Prop) (f : PowerSeries C) :
    filt P (filt Q f) = filt (fun m => P m ∧ Q m) f := by
  ext m
  rw [coeff_filt, coeff_filt, coeff_filt]
  by_cases h : P m <;> by_cases h' : Q m <;> simp [h, h']

theorem filt_congr {P Q : ℕ → Prop} (h : ∀ m, P m ↔ Q m) (f : PowerSeries C) : filt P f = filt Q f := by
  have : P = Q := funext fun m => propext (h m)
  rw [this]

theorem filt_true {P : ℕ → Prop} (h : ∀ m, P m) (f : PowerSeries C) : filt P f = f := by
  ext m
  rw [coeff_filt, if_pos (h m)]

def Good (l n m : ℕ) : Prop := ∀ p < n, p.Prime → p ≠ l → ¬ p ∣ m

theorem coeff_filt_good {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (f : PowerSeries C) (m n : ℕ) (hn : m + 3 ≤ n) :
    PowerSeries.coeff m (filt (Good l n) f) = PowerSeries.coeff m (typ l f) := by
  rw [coeff_filt]
  unfold typ
  by_cases hm : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := hm
    rw [coeff_tyS_pow hl.two_le, if_pos]
    intro p _ hp hpl hd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow hd))
  · rw [coeff_tyS_of_ne _ m (fun s hs => hm ⟨s, hs⟩), if_neg]
    intro hg
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact hg 2 (by omega) Nat.prime_two (Ne.symm hl2) (dvd_zero 2)
    · apply hm
      refine ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_).symm⟩
      intro q hq hqm
      by_contra hne
      exact hg q (by have := Nat.le_of_dvd hpos hqm; omega) hq hne hqm

variable {V : VF C} {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

theorem filt_not_dvd_mem (hX : RLaw X V) (g : Fin 2) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) :
    ((fun i => filt (fun m => ¬ p ∣ m) (a.1 i), fun q => filt (fun m => ¬ p ∣ m) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  have := hX.charZero
  have := hX.closed
  have : NeZero (p : C) := ⟨by exact_mod_cast hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  obtain ⟨h0, hadd, hneg, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  have hζ0 : V.Ge 0 ζ := ge_of_pow_eq_one V hp.pos hζ.pow_eq_one
  have hs : ∀ n : ℕ, ((fun i => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.1 i),
      fun q => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact h0
    | succ n ih =>
      have := hadd _ ih _ (hres (ζ ^ n) (hζ0.pow n) a ha)
      simp only [Finset.sum_range_succ]
      exact this
  have h2 := hadd _ ha _ (hneg _ (GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem C V d I κ X hX g p (v_prime_eq_zero V hp hpl) _ (hs p)))
  convert h2 using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · exact (sub_avg hp.pos hζ (a.1 i)).symm
  · exact (sub_avg hp.pos hζ (a.2 q)).symm

theorem filt_good_mem (hX : RLaw X V) (g : Fin 2)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) (n : ℕ) :
    ((fun i => filt (Good V.l n) (a.1 i), fun q => filt (Good V.l n) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  induction n with
  | zero =>
    have h : ∀ m, Good V.l 0 m := fun m p hp => absurd hp (Nat.not_lt_zero p)
    simp only [filt_true h]
    exact ha
  | succ n ih =>
    by_cases hn : n.Prime ∧ n ≠ V.l
    · have h : ∀ m, Good V.l (n + 1) m ↔ (¬ n ∣ m ∧ Good V.l n m) := by
        intro m
        constructor
        · intro hg
          exact ⟨hg n (by omega) hn.1 hn.2, fun p hp => hg p (by omega)⟩
        · rintro ⟨h1, h2⟩ p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact h1
      have := filt_not_dvd_mem hX g hn.1 hn.2 _ ih
      simp only [filt_filt] at this
      simp only [filt_congr h]
      exact this
    · have h : ∀ m, Good V.l (n + 1) m ↔ Good V.l n m := by
        intro m
        constructor
        · intro hg p hp
          exact hg p (by omega)
        · intro h2 p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact absurd ⟨hpp, hpl⟩ hn
      simp only [filt_congr h]
      exact ih

end GlobalTheory.RowLaw.TypPart

open GlobalTheory.RowLaw.TypPart in

theorem GlobalTheory.RowLaw.typ_mem_Cv : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ a ∈ Cv X V g, ((fun i => typ V.l (a.1 i), fun q => typ V.l (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g a ha
  refine GlobalTheory.RowLaw.cv_closed_under_limits C V d I κ X hX g _ _ (filt_good_mem hX g a ha) fun m => ⟨m + 3, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
