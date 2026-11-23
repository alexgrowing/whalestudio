import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist

noncomputable section

namespace GlobalTheory.HostModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

open NumberField in

theorem _root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n) n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  exact Complex.isPrimitiveRoot_exp n hn.ne'

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

lemma _root_.GlobalTheory.HostModel.zeta_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n * m) ^ m = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

theorem zeta_pow_div {a n : ℕ} (hn : 0 < n) (h : a ∣ n) : zeta n ^ (n / a) = zeta a := by
  obtain ⟨k, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k ha, zeta_mul_pow ha hk]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem zeta_M'_pow_div_A (l : Level H) : zeta l.M' ^ (l.M' / l.A) = zeta l.A :=
  zeta_pow_div (LevelExist.M'_pos l) (Nat.dvd_lcm_right l.M l.A)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.zeta_mem_coeff_of_dvd {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {a : ℕ} (h : a ∣ l.M') : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta a ∈ c.F := by
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (_root_.GlobalTheory.LevelExist.M'_pos l) h
  rw [hk]
  exact pow_mem c.zeta_mem k

theorem zeta_M_mem_coeff {l : Level H} (c : Coeff l) : zeta l.M ∈ c.F :=
  zeta_mem_coeff_of_dvd c (Nat.dvd_lcm_left l.M l.A)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.zeta_A_mem_coeff {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta l.A ∈ c.F :=
  _root_.GlobalTheory.HostModel.zeta_mem_coeff_of_dvd c (by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M'; exact Nat.dvd_lcm_right _ _)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) : H.rt0 ∈ c.F := by
  apply c.le
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA
  exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

def coeff (l : Level H) : Coeff l := LevelExist.minCoeff l

theorem coeff_F (l : Level H) :
    (coeff l).F = IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} := rfl

theorem coeff_F_le_iff (l : Level H) (F : IntermediateField ℚ ℂ) :
    (coeff l).F ≤ F ↔ zeta l.M' ∈ F ∧ ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F := by
  constructor
  · exact fun h => ⟨h (coeff l).zeta_mem, fun τ a => h ((coeff l).conj τ a)⟩
  · rintro ⟨hz, hc⟩
    rw [coeff_F, sup_le_iff, normalClosure_le_iff, IntermediateField.adjoin_simple_le_iff]
    refine ⟨fun f => ?_, hz⟩
    rintro _ ⟨a, rfl⟩
    exact hc f.toRingHom a

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.exists_roots (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] (F : Type) [Field F] [IsAlgClosed F]
    (f : L →+* F) :
    ∃ ζ : ℕ → Fˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧
      ∀ n, 0 < n → ∀ z : L, (z : ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n → (ζ n : F) = f z := by
  set S : Set ℂ := (L : Set ℂ) ∪ Set.range (fun n : ℕ => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n + 1)) with hS
  set Kinf := IntermediateField.adjoin ℚ S with hKinf
  have hL : L ≤ Kinf := fun x hx => IntermediateField.subset_adjoin ℚ S (Or.inl hx)
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x (hx | ⟨n, rfl⟩)
    · exact (IsIntegral.of_finite ℚ (⟨x, hx⟩ : L)).map L.val
    · exact _root_.GlobalTheory.LevelExist.isIntegral_zeta (Nat.succ_pos n)
  haveI : Algebra.IsAlgebraic ℚ Kinf := IntermediateField.isAlgebraic_adjoin hint
  letI : Algebra L Kinf := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  letI : Algebra L F := f.toAlgebra
  haveI : IsScalarTower ℚ L Kinf :=
    IsScalarTower.of_algebraMap_eq fun q => ((IntermediateField.inclusion hL).commutes q).symm
  haveI : Algebra.IsAlgebraic L Kinf := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let g : Kinf →ₐ[L] F := IsAlgClosed.lift
  have hg : ∀ z : L, g (IntermediateField.inclusion hL z) = f z := fun z => g.commutes z
  have hmem : ∀ n, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n ∈ Kinf := by
    intro n
    cases n with
    | zero =>
      have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta 0 = 1 := by
        unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
        simp
      rw [h0]
      exact one_mem _
    | succ n => exact IntermediateField.subset_adjoin ℚ S (Or.inr ⟨n, rfl⟩)
  have hne : ∀ n, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n ≠ 0 := fun n => by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
    exact Complex.exp_ne_zero _
  let w : ℕ → Kinf := fun n => ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, hmem n⟩
  have hw0 : ∀ n, g (w n) ≠ 0 := fun n =>
    (map_ne_zero g).mpr fun h => hne n (congrArg Subtype.val h)
  refine ⟨fun n => Units.mk0 (g (w n)) (hw0 n), ?_, ?_, ?_⟩
  · intro n hn
    rw [← IsPrimitiveRoot.coe_units_iff, Units.val_mk0]
    have h1 : IsPrimitiveRoot (w n) n :=
      IsPrimitiveRoot.of_map_of_injective (f := Kinf.val)
        (show IsPrimitiveRoot (Kinf.val (w n)) n from _root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hn)
        Subtype.val_injective
    exact h1.map_of_injective (f := g) (RingHom.injective (g : Kinf →+* F))
  · intro n m hn hm
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow]
    congr 1
    apply Subtype.ext
    show _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n * m) ^ m = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n
    exact _root_.GlobalTheory.HostModel.zeta_mul_pow hn hm
  · intro n hn z hz
    rw [Units.val_mk0, ← hg z]
    congr 1
    exact Subtype.ext hz.symm

example : zeta 4 = Complex.I := by
  unfold zeta
  rw [show (2 * Real.pi * Complex.I / (4 : ℕ) : ℂ) = Real.pi / 2 * Complex.I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

example : zeta 6 ^ 3 = -1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, zeta_mul_pow two_pos three_pos]
  exact (isPrimitiveRoot_zeta two_pos).eq_neg_one_of_two_right

example (l : Level H) : (coeff l).F ≠ ⊥ := by
  intro h
  have hm := sqrtNegDisc_mem_coeffField (coeff l)
  rw [h, IntermediateField.mem_bot] at hm
  obtain ⟨q, hq⟩ := hm
  have h2 := H.sqrt_neg_disc_sq
  rw [← hq] at h2
  have h3 : q ^ 2 = -(H.d : ℚ) := by
    apply (algebraMap ℚ ℂ).injective
    simpa using h2
  have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg q]

example (l : Level H) : (coeff l).F ≠ ⊤ := by
  intro h
  haveI := (coeff l).fin
  have hc : Countable (coeff l).F := (Module.finBasis ℚ (coeff l).F).equivFun.injective.countable
  rw [h] at hc
  haveI : Countable ℂ := (IntermediateField.topEquiv (F := ℚ) (E := ℂ)).symm.injective.countable
  exact not_countable (Complex.ofReal_injective.countable)

example (H : Host E) : zeta (H.d + 4) ∈ (coeff (level H 5 (by norm_num))).F ∧
    zeta 5 ∈ (coeff (level H 5 (by norm_num))).F :=
  ⟨zeta_M_mem_coeff _, zeta_A_mem_coeff _⟩

end GlobalTheory.HostModel
