import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain

theorem dvd_of_map_dvd_of_isIntegral {A' B : Type} [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B]
    [IsDomain B] (g : A' →+* B) (hg : Function.Injective g) (hi : g.IsIntegral) (a x : A') (ha : a ≠ 0)
    (h : g a ∣ g x) : a ∣ x := by
  obtain ⟨b, hb⟩ := h
  have hinj : Function.Injective ((algebraMap B (FractionRing B)).comp g) :=
    (IsFractionRing.injective B (FractionRing B)).comp hg
  let φ : FractionRing A' →+* FractionRing B := IsFractionRing.lift hinj
  have hφ : ∀ y, φ (algebraMap A' _ y) = algebraMap B (FractionRing B) (g y) := fun y =>
    IsFractionRing.lift_algebraMap hinj y
  have ha' : algebraMap A' (FractionRing A') a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A' (FractionRing A'))).2 ha
  have ha'' : algebraMap B (FractionRing B) (g a) ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hq : φ (algebraMap A' (FractionRing A') x / algebraMap A' (FractionRing A') a) = algebraMap B _ b := by
    rw [map_div₀, hφ, hφ, hb, map_mul, mul_div_cancel_left₀ _ ha'']
  have hint : IsIntegral A' (algebraMap A' (FractionRing A') x / algebraMap A' (FractionRing A') a) := by
    obtain ⟨P, hP, hPb⟩ := hi b
    refine ⟨P, hP, φ.injective ?_⟩
    have hc : φ.comp (algebraMap A' (FractionRing A')) = (algebraMap B (FractionRing B)).comp g := RingHom.ext hφ
    rw [Polynomial.hom_eval₂, hq, hc, ← Polynomial.hom_eval₂, hPb, map_zero, map_zero]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨c, IsFractionRing.injective A' (FractionRing A') ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem mem_baseOf_iff_forall_dvd {A : Type} [CommRing A] (a : A) (h : ℕ) (x : Fin h → A) :
    x ∈ baseOf a h ↔ ∀ i, a ∣ x i := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨fun ⟨y, _, e⟩ i => ⟨y i, (congrFun e i).symm⟩, fun k => ?_⟩
  choose c hc using k
  exact ⟨c, trivial, funext fun i => (hc i).symm⟩

theorem dvd_descends_of_isIntegral :
    ∀ (A' B : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B] [IsDomain B] (g : A' →+* B), Function.Injective g → g.IsIntegral → (∀ a x : A', a ≠ 0 → g a ∣ g x → a ∣ x) ∧ ∀ (h : ℕ) (a : A'), a ≠ 0 → ∀ x : Fin h → A', piMap g (Fin h) x ∈ baseOf (g a) h ↔ x ∈ baseOf a h := by
  intro A' B _ _ _ _ _ g hg hi
  refine ⟨dvd_of_map_dvd_of_isIntegral g hg hi, fun h a ha x => ?_⟩
  rw [mem_baseOf_iff_forall_dvd, mem_baseOf_iff_forall_dvd]
  exact forall_congr' fun i => ⟨dvd_of_map_dvd_of_isIntegral g hg hi a (x i) ha, fun k => map_dvd g k⟩

end GlobalTheory.RingChain
