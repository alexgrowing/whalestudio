import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.NLocPlace

theorem vAdd_int (D : D7) (w : D.what₂.places.Pl) (a : 𝓞 D.what₂.LL) (ha : (a : D.what₂.LL) ≠ 0) :
    0 ≤ vAdd (D.plEq w) (a : D.what₂.LL) ∧ (a ∈ (D.plEq w).asIdeal ↔ 0 < vAdd (D.plEq w) (a : D.what₂.LL)) := by
  have hv0 : (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hle : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a) ≤ 1 :=
    (D.plEq w).valuation_le_one a
  have hmem := (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL) a
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≤ 1 at hle
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) < 1 ↔ _ at hmem
  unfold vAdd
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hmem
  refine ⟨by omega, ?_⟩
  rw [← hmem]
  omega

end GlobalTheory.NLocPlace

namespace GlobalTheory.NLocPlace

theorem ec_int_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl),
    (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧
    ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) →
      (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  intro D M B j w
  have hinj : Function.Injective (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))) :=
    IsFractionRing.injective _ _

  have hval : ∀ x : D.what₂.LL, x ≠ 0 → D.what₂.places.val w x = ((vAdd (D.plEq w) x : ℤ) : WithTop ℤ) :=
    fun x hx => D.val_eq w x hx

  have hsum : ∀ x : D.what₂.LL, x ≠ 0 → vAdd (D.plEq w) x + vAdd (D.plEq w) x⁻¹ = 0 := by
    intro x hx
    have h1 : D.what₂.places.val w (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, AddValuation.map_one]
    rw [AddValuation.map_mul, hval x hx, hval x⁻¹ (inv_ne_zero hx), ← WithTop.coe_add] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (B.ec_w j w _).1
    by_cases ha : (a : D.what₂.LL) = 0
    · rw [ha, AddValuation.map_zero]; exact le_top
    · rw [hval _ ha]
      exact_mod_cast (vAdd_int D w a ha).1
  · have hp0 : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0 := by
      push_cast; exact Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
    rw [(vAdd_int D w _ hp0).2]
    have h1 := D.what₂.places.val_resChar w
    have hc : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      push_cast; rfl
    rw [← hc, hval _ hp0] at h1
    have h2 : vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
      WithTop.coe_injective h1
    rw [h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  · intro a z hz
    by_cases ha : (a : D.what₂.LL) = 0
    · have ha' : a = 0 := by exact_mod_cast ha
      have hz0 : z = 0 := hinj (by rw [hz, ha, map_zero, map_zero])
      subst ha' hz0
      simp
    · have hec : B.ec j w (a : D.what₂.LL) ≠ 0 := by
        rw [map_ne_zero]; exact ha
      obtain ⟨hnn, hiff⟩ := vAdd_int D w a ha
      have hs := hsum _ ha
      rw [hiff]
      constructor
      · rintro hpos ⟨u, hu⟩
        have h1 : algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) (↑u⁻¹ : B.Oc j w) = B.ec j w (a : D.what₂.LL)⁻¹ := by
          rw [map_inv₀, ← hz, ← hu]
          apply eq_inv_of_mul_eq_one_right
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 := (B.ec_w j w (a : D.what₂.LL)⁻¹).2 ⟨_, h1⟩
        rw [hval _ (inv_ne_zero ha)] at h2
        have h3 : (0 : ℤ) ≤ vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ := by exact_mod_cast h2
        omega
      · intro hnu
        by_contra hle
        have h0 : vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ = 0 := by omega
        have h2 : 0 ≤ D.what₂.places.val w (a : D.what₂.LL)⁻¹ := by
          rw [hval _ (inv_ne_zero ha), h0]; rfl
        obtain ⟨y, hy⟩ := (B.ec_w j w _).1 h2
        apply hnu
        have hzy : z * y = 1 := hinj (by rw [map_mul, map_one, hz, hy, ← map_mul, mul_inv_cancel₀ ha, map_one])
        exact ⟨⟨z, y, hzy, by rw [mul_comm]; exact hzy⟩, rfl⟩

end GlobalTheory.NLocPlace
