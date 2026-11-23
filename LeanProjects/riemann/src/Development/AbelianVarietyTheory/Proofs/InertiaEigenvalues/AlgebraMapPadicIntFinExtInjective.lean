import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_padicInt_of_mem_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (x : ℚ_[l])
    (hx : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL) : ∃ y : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] y = x := by
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 x) := hx
  have hint' : IsIntegral ℤ_[l] x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
      (algebraMap ℚ_[l] ↥LL.1).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

theorem algebraMap_padicInt_finExt_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

theorem algebraMap_padicInt_OL_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
  intro a b h
  exact algebraMap_padicInt_finExt_injective LL (congrArg Subtype.val h)

private theorem associated_prime_of_valuation_eq_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (c : ℤ_[l]) (hc : P.v LL (algebraMap ℤ_[l] ↥LL.1 c) = 1) : Associated c (l : ℤ_[l]) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, AddValuation.map_zero] at hc
    exact WithTop.top_ne_one hc
  have hspec := PadicInt.unitCoeff_spec hc0
  set u := PadicInt.unitCoeff hc0
  have hnn : ∀ w : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 w) := fun w =>
    (P.v_O LL _).mpr (Subalgebra.algebraMap_mem _ w)
  have hu0 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
    have h1 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg (hnn _) (hnn _)).mp h1).1
  have hval : c.valuation = 1 := by
    rw [hspec, map_mul, AddValuation.map_mul, hu0, zero_add, map_pow, AddValuation.map_pow,
      map_natCast, P.v_l LL, nsmul_one] at hc
    exact_mod_cast hc
  refine ⟨u⁻¹, ?_⟩
  conv_lhs => rw [hspec]
  rw [hval, pow_one, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem associated_of_v_sub_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (y : ℤ_[l]) (x : ↥(OL LL)) (hy : algebraMap ℤ_[l] ↥(OL LL) y = x)
    (h : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x - 1) = 1) : Associated (y - 1) (l : ℤ_[l]) := by
  apply associated_prime_of_valuation_eq_one P LL
  have hx : algebraMap ↥(OL LL) ↥LL.1 x = algebraMap ℤ_[l] ↥LL.1 y := by
    rw [← hy]
    rfl
  rw [map_sub, map_one, ← hx]
  exact h

theorem exists_units_hom_lift {Γ R S : Type} [Group Γ] [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (c : Γ →* Sˣ) (hex : ∀ g, ∃ y : R, φ y = (c g : S)) :
    ∃ χ : Γ →* Rˣ, ∀ g, φ (χ g : R) = (c g : S) := by
  choose y hy using hex
  have hinv : ∀ g, y g * y g⁻¹ = 1 := fun g => hφ (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hinv' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hinv g⁻¹
  let u : Γ → Rˣ := fun g => ⟨y g, y g⁻¹, hinv g, hinv' g⟩
  refine ⟨{ toFun := u, map_one' := ?_, map_mul' := ?_ }, fun g => hy g⟩
  · ext
    apply hφ
    simp [u, hy]
  · intro g h
    ext
    apply hφ
    simp [u, hy]

theorem exists_cyclotomicChar_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ (W.s = 1 → Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) := by
  intro l _ P K LL n W
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨h, rfl⟩ := W.resΓ_onto g
    have hmem : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ h : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res h]
      exact (W.χΓ (W.resΓ h) : ↥(OL LL)).2
    obtain ⟨y, hy⟩ := exists_padicInt_of_mem_OL LL _ hmem
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res h]
    rfl
  obtain ⟨χ, hχ⟩ := exists_units_hom_lift (algebraMap ℤ_[l] ↥(OL LL))
    (algebraMap_padicInt_OL_injective LL) W.χΓ hex
  refine ⟨χ, hχ, fun hs => ?_⟩
  apply associated_of_v_sub_one P LL _ _ (hχ W.gam)
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  exact hg

end GlobalTheory
