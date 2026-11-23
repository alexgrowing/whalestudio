import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.IntBasis

open IsLocalRing

abbrev adicVal (K : UQ) : Valuation K.E (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem adicVal_le_one_iff (K : UQ) (x : K.E) : adicVal K x ≤ 1 ↔ ∃ a : K.O, algebraMap K.O K.E a = x :=
  ⟨IsDiscreteValuationRing.exists_lift_of_le_one, by
    rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩

theorem adicVal_eq_one_iff (K : UQ) (a : K.O) : adicVal K (algebraMap K.O K.E a) = 1 ↔ IsUnit a := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  simp [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem adicVal_map (h : IsUnrExt K K' d φ) (x : K.E) : adicVal K' (φ x) = adicVal K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx
  have h1 := h.2.2.1 x
  unfold val at h1
  have h2 := neg_inj.1 h1
  have a1 : adicVal K' (φ x) ≠ 0 := (Valuation.ne_zero_iff _).2 hφ
  have a2 : adicVal K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [← WithZero.exp_log a1, ← WithZero.exp_log a2]
  exact congrArg WithZero.exp h2

theorem exists_lift (h : IsUnrExt K K' d φ) :
    ∃ ι : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
  let S := (algebraMap K'.O K'.E).range
  have hS : ∀ a : K.O, (φ.comp (algebraMap K.O K.E)) a ∈ S := fun a => by
    obtain ⟨b, hb⟩ := (adicVal_le_one_iff K' (φ (algebraMap K.O K.E a))).1 (by
      rw [adicVal_map h]; exact (adicVal_le_one_iff K _).2 ⟨a, rfl⟩)
    exact ⟨b, hb⟩
  let e : K'.O ≃+* S := RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective K'.O K'.E (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  refine ⟨e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict S hS), fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict S hS a))

theorem exists_key (h : IsUnrExt K K' d φ) :
    ∃ w : Fin d → K'.E, ∀ (a : Fin d → K.E) (m : Fin d), (∀ k, adicVal K (a k) ≤ adicVal K (a m)) →
      adicVal K' (∑ k, φ (a k) * w k) = adicVal K (a m) := by
  obtain ⟨ι, hι⟩ := exists_lift h
  haveI : IsLocalHom ι := ⟨fun a ha => by
    rw [← adicVal_eq_one_iff] at ha ⊢; rwa [hι, adicVal_map h] at ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ι).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hf : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have hc := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, K'.card_res, K.card_res, h.1, ← pow_mul,
      mul_comm, pow_mul] at hc
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← K.card_res]; exact Finite.one_lt_card
    exact (Nat.pow_right_injective h2 hc).symm
  haveI : Module.Finite (ResidueField K.O) (ResidueField K'.O) := Module.Finite.of_finite
  let bk := Module.finBasisOfFinrankEq _ _ hf
  choose w' hw' using fun i => residue_surjective (bk i)
  refine ⟨fun i => algebraMap K'.O K'.E (w' i), fun a m hm => ?_⟩
  by_cases ham : a m = 0
  · have h0 : ∀ k, a k = 0 := fun k => by
      have := hm k; rw [ham, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
    simp [h0]
  have hb : ∀ k, ∃ b : K.O, algebraMap K.O K.E b = a k / a m := fun k =>
    (adicVal_le_one_iff K _).1 (by rw [map_div₀]; exact div_le_one_of_le₀ (hm k) zero_le')
  choose b hb using hb
  have hbm : b m = 1 := IsFractionRing.injective K.O K.E (by rw [hb, div_self ham, map_one])
  set s : K'.O := ∑ k, ι (b k) * w' k with hs
  have hsum : ∑ k, φ (a k) * algebraMap K'.O K'.E (w' k) = φ (a m) * algebraMap K'.O K'.E s := by
    rw [hs, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hι, hb, map_div₀, ← mul_assoc, mul_div_cancel₀ _ ((map_ne_zero φ).2 ham)]
  have hres : residue K'.O s ≠ 0 := by
    have e1 : residue K'.O s = ∑ k, residue K.O (b k) • bk k := by
      rw [hs, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hw', Algebra.smul_def, RingHom.algebraMap_toAlgebra, ResidueField.map_residue]
    rw [e1]; intro h0
    have := Fintype.linearIndependent_iff.1 bk.linearIndependent _ h0 m
    rw [hbm, map_one] at this; exact one_ne_zero this
  have hsu : IsUnit s := by
    by_contra hn
    exact hres ((residue_eq_zero_iff s).2 ((mem_maximalIdeal s).2 hn))
  rw [hsum, Valuation.map_mul, (adicVal_eq_one_iff K' s).2 hsu, mul_one, adicVal_map h]

theorem intBasis : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    letI : Algebra K.E K'.E := φ.toAlgebra;
    ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, key⟩ := exists_key h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : ∀ a : Fin d → K.E, ∃ m, ∀ k, adicVal K (a k) ≤ adicVal K (a m) := fun a =>
    Finite.exists_max (fun k => adicVal K (a k))
  have hli : LinearIndependent K.E w := by
    rw [Fintype.linearIndependent_iff]; intro g hg
    obtain ⟨m, hm⟩ := hmax g
    have hk := key g m hm
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
    rw [hg, map_zero] at hk
    have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
    intro k; have := hm k; rw [hgm, map_zero] at this
    exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; exact h.2.2.2.2.symm)
  refine ⟨B, fun z => ?_⟩
  have hz : ∑ k, φ (B.repr z k) * w k = z := by
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨m, hm⟩ := hmax (B.repr z)
  have hv := key _ m hm
  rw [hz] at hv
  rw [← adicVal_le_one_iff K' z]
  constructor
  · intro hzO k; rw [← adicVal_le_one_iff]; exact (hm k).trans (hv ▸ hzO)
  · intro hall; rw [hv]; exact (adicVal_le_one_iff K _).2 (hall m)

end GlobalTheory.UnitLemma.Unr.IntBasis
