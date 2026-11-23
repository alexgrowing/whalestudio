import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory

theorem ringOfIntegers_hom_injective (E : Type) [Field E] [NumberField E] (C : Type) [Field C]
    [CharZero C] (f : 𝓞 E →+* C) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  simp only [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  simpa using hn

theorem ringOfIntegers_hom_eq_of_congr_maximalIdeal :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ ((p : ℤ) ∣ NumberField.discr E) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsLocalRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) → ∀ σ σ' : 𝓞 E →+* O, (∀ x, σ x - σ' x ∈ maximalIdeal O) → σ = σ' := by
  intro E _ _ p hp hd C _ _ _ v O _ _ _ hv hpu σ σ' hcong
  classical
  by_contra hne
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj

  have hext : ∀ s : 𝓞 E →+* O, ∃ τ : E →ₐ[ℚ] C,
      ∀ x : 𝓞 E, τ (algebraMap (𝓞 E) E x) = algebraMap O C (s x) := by
    intro s
    refine ⟨(IsFractionRing.lift (K := E)
      (ringOfIntegers_hom_injective E C ((algebraMap O C).comp s))).toRatAlgHom, fun x => ?_⟩
    simp
  obtain ⟨τ, hτ⟩ := hext σ
  obtain ⟨τ', hτ'⟩ := hext σ'
  have hττ : τ ≠ τ' := by
    intro h
    apply hne
    ext x
    apply hinj
    rw [← hτ, ← hτ', h]
  have hmem : ∀ (φ : E →ₐ[ℚ] C) (x : 𝓞 E), ∃ y : O,
      algebraMap O C y = φ (algebraMap (𝓞 E) E x) := by
    intro φ x
    have h1 : IsIntegral ℤ (φ (algebraMap (𝓞 E) E x)) :=
      (x.isIntegral_coe).map (φ.toRingHom.toIntAlgHom)
    have h2 : IsIntegral O (φ (algebraMap (𝓞 E) E x)) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose F hF using hmem
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let e : ι ≃ (E →ₐ[ℚ] C) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis E)])
  let N : Matrix ι ι O := fun i j => F (e j) (RingOfIntegers.basis E i)
  have hN : (algebraMap O C).mapMatrix N =
      Algebra.embeddingsMatrixReindex ℚ C (integralBasis E) e := by
    ext i j
    show algebraMap O C (F (e j) (RingOfIntegers.basis E i)) = _
    simp [hF, Algebra.embeddingsMatrixReindex, integralBasis_apply]
  have hdisc : ((NumberField.discr E : ℤ) : O) = N.det ^ 2 := by
    apply hinj
    rw [map_pow, RingHom.map_det, hN, ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two,
      ← NumberField.coe_discr]
    simp
  have hdet : N.det ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    apply Matrix.det_zero_of_column_eq (i := e.symm τ) (j := e.symm τ')
      (fun h => hττ (e.symm.injective h))
    intro k
    show residue O (F (e (e.symm τ)) (RingOfIntegers.basis E k)) =
      residue O (F (e (e.symm τ')) (RingOfIntegers.basis E k))
    simp only [Equiv.apply_symm_apply]
    have a1 : F τ (RingOfIntegers.basis E k) = σ (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ])
    have a2 : F τ' (RingOfIntegers.basis E k) = σ' (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ'])
    rw [a1, a2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hcong _
  have hdm : ((NumberField.discr E : ℤ) : O) ∈ maximalIdeal O := by
    rw [hdisc]
    exact Ideal.pow_mem_of_mem _ hdet 2 (by norm_num)
  have hpm : (p : O) ∈ maximalIdeal O := hpu
  have hcop : IsCoprime (p : ℤ) (NumberField.discr E) :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory
