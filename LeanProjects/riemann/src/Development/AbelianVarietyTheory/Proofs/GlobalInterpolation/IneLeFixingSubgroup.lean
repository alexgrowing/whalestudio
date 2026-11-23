import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramDiscr

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω)
    {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact y.2

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.UnramDiscr.embedding_eq {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    (hd : ¬ A.valuation ((discr K : ℤ) : Ω) < 1)
    (f g : K →+* Ω) (h : ∀ x : 𝓞 K, A.valuation (f x - g x) < 1) : f = g := by
  classical
  by_contra hfg
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, ← RingOfIntegers.rank K, Module.finrank_eq_card_chooseBasisIndex]
  let e : ι ≃ (K →ₐ[ℚ] Ω) := Fintype.equivOfCardEq hcard
  let b := integralBasis K
  have hint : ∀ (φ : K →+* Ω) (x : 𝓞 K), φ x ∈ A := fun φ x =>
    _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral A
      ((RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom)
  let N : Matrix ι ι A := Matrix.of fun i j => ⟨e j (b i), by
    rw [integralBasis_apply]; exact hint (e j).toRingHom _⟩
  have hM : ((discr K : ℤ) : Ω) = ((N.det ^ 2 : A) : Ω) := by
    have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b e
    rw [← coe_discr] at hdet
    have hN : A.subtype.mapMatrix N = Algebra.embeddingsMatrixReindex ℚ Ω b e := by
      ext i j
      simp [N, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [map_intCast, ← hN, ← RingHom.map_det] at hdet
    rw [hdet]
    simp
  have hF : f.toRatAlgHom ≠ g.toRatAlgHom := by
    intro hc
    apply hfg
    ext x
    exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) hc
  have hres : ((IsLocalRing.residue A).mapMatrix N).det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := e.symm f.toRatAlgHom) (j := e.symm g.toRatAlgHom)
    · simpa using hF
    · intro k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply]
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      simpa [b, integralBasis_apply] using h (RingOfIntegers.basis K k)
  rw [← RingHom.map_det, IsLocalRing.residue_eq_zero_iff] at hres
  apply hd
  rw [hM, ← A.valuation_lt_one_iff]
  exact Ideal.pow_mem_of_mem _ hres 2 (by norm_num)

theorem not_valuation_lt_one {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {q : ℕ}
    (hq : q.Prime) (hA : A.valuation (q : Ω) < 1) {d : ℤ} (hd : ¬ (q : ℤ) ∣ d) :
    ¬ A.valuation (d : Ω) < 1 := by
  intro h
  have hc : IsCoprime (q : ℤ) d :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).mpr hd
  obtain ⟨a, c, hac⟩ := hc
  have e : (a : Ω) * q + c * d = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hac
  have ha : A.valuation (a : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  have hc : A.valuation (c : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A c)
  have h1 : A.valuation ((a : Ω) * q) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le ha) hA
  have h2 : A.valuation ((c : Ω) * d) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le hc) h
  have := Valuation.map_add_lt _ h1 h2
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem ine_le_fixingSubgroup :
    ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] (q : ℕ), q.Prime →
      ¬ ((q : ℤ) ∣ discr K) → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q →
      Formalism.MainNotions.V.Lang.Ine (F := ℚ) A ≤ K.fixingSubgroup := by
  intro K _ q hq hd A ⟨v, hv, hqv⟩ σ hσ
  have hA : A.valuation (q : AlgebraicClosure ℚ) < 1 := by
    simpa using (hv _).mpr hqv
  have key := embedding_eq A (not_valuation_lt_one A hq hA hd)
    ((σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp K.subtype) K.subtype (fun x => by
      refine hσ.2 _ ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral A ?_))
      exact (RingOfIntegers.isIntegral_coe x).map (K.subtype.toIntAlgHom))
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact DFunLike.congr_fun key ⟨x, hx⟩

end GlobalTheory.UnramDiscr
