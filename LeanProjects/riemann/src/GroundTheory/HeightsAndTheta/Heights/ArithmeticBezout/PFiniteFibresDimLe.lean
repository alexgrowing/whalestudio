import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFiniteFibresDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem isMaximal_of_zeroLocus_finite {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [hP : P.IsPrime]
    (hfin : (zeroLocus ℂ P : Set (Fin n → ℂ)).Finite) : P.IsMaximal := by
  have hle : (hfin.toFinset.inf fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))) ≤ P := by
    intro q hq
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P, mem_vanishingIdeal_iff]
    intro z hz
    have hq' := (Finset.inf_le (f := fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ)))
      (hfin.mem_toFinset.2 hz)) hq
    exact (mem_vanishingIdeal_iff.1 hq') z rfl
  obtain ⟨z, -, hz⟩ := hP.inf_le'.1 hle
  have hmax : (vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))).IsMaximal :=
    isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨z, rfl⟩
  rwa [← hmax.eq_of_le hP.ne_top hz]

theorem FiniteFibresDimLe.proof : FiniteFibresDimLe.Statement := by
  intro n d Q A hQ hfin
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  obtain ⟨x, hx⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  set y : Fin d → ℂ := A.mulVec x with hy
  let B := MvPolynomial (Fin n) ℂ ⧸ Q
  let _ : CommRing B := Ideal.Quotient.commRing Q
  let _ : IsDomain B := Ideal.Quotient.isDomain Q
  let _ : Algebra ℂ B := Ideal.Quotient.algebra ℂ
  let _ : Algebra.FiniteType ℂ B := inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ Q))
  let m : Ideal B := M.map (Ideal.Quotient.mk Q)
  have hm : m.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQM)
  have hmp : m.IsPrime := hm.isPrime
  have hmh : (m.height : WithBot ℕ∞) = ringKrullDim B :=
    NumbersDVR.MaximalIdealHeightFG.proof ℂ B m hm
  have hlin : ∀ (z : Fin n → ℂ) (i : Fin d), eval z (ComplexSets.linPoly A i) = A.mulVec z i := by
    intro z i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_comm]
  let f : Fin d → B := fun i => Ideal.Quotient.mk Q (ComplexSets.linPoly A i - C (y i))
  have hfm : Set.range f ⊆ m := by
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_map_of_mem
    rw [hx, mem_vanishingIdeal_singleton_iff]
    simp [hlin, hy]
  have hK := Ideal.height_le_height_add_encard_of_subset (Set.range f) hfm
  have hcard : (Set.range f).encard ≤ d := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  let I : Ideal B := Ideal.span (Set.range f)
  have hIm : I ≤ m := by rw [Ideal.span_le]; exact hfm
  let p := m.map (Ideal.Quotient.mk I)
  have hpp : p.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIm
  have hp0 : p.height ≠ 0 := by
    intro h0
    change m.height ≤ p.height + _ at hK
    rw [h0, zero_add] at hK
    have : (m.height : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      exact_mod_cast hK.trans hcard
    exact absurd (hmh ▸ this) (not_le.2 hlt)
  change (⟨p, hpp⟩ : PrimeSpectrum (B ⧸ I)).asIdeal.height ≠ 0 at hp0
  rw [PrimeSpectrum.height_eq_orderHeight, ne_eq, Order.height_eq_zero] at hp0
  obtain ⟨P, hPlt⟩ := not_isMin_iff.1 hp0
  let π : MvPolynomial (Fin n) ℂ →+* B ⧸ I := (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk Q)
  have hπ : Function.Surjective π :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  let P' : Ideal (MvPolynomial (Fin n) ℂ) := P.asIdeal.comap π
  have hP' : P'.IsPrime := Ideal.comap_isPrime π P.asIdeal
  have hP'max : ¬ P'.IsMaximal := by
    intro hmax
    have hPm : P.asIdeal.IsMaximal := by
      have := Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (m := P') (by
        intro a ha
        change π a ∈ P.asIdeal
        rw [RingHom.mem_ker.1 ha]; exact P.asIdeal.zero_mem)
      rwa [Ideal.map_comap_of_surjective π hπ] at this
    have hle : P.asIdeal ≤ p := hPlt.le
    exact (ne_of_lt hPlt) (PrimeSpectrum.ext (hPm.eq_of_le hpp.ne_top hle))
  apply hP'max
  apply isMaximal_of_zeroLocus_finite
  refine (hfin y).subset ?_
  intro z hz
  rw [mem_zeroLocus_iff] at hz
  have hz' : ∀ q ∈ P', eval z q = 0 := fun q hq => by simpa using hz q hq
  refine ⟨fun q hq => hz' q ?_, ?_⟩
  · change π q ∈ P.asIdeal
    have : π q = 0 := by
      simp [π, Ideal.Quotient.eq_zero_iff_mem.2 hq]
    rw [this]; exact P.asIdeal.zero_mem
  · funext i
    have hmem : ComplexSets.linPoly A i - C (y i) ∈ P' := by
      change π _ ∈ P.asIdeal
      have : π (ComplexSets.linPoly A i - C (y i)) = 0 := by
        change Ideal.Quotient.mk I (f i) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
      rw [this]; exact P.asIdeal.zero_mem
    have := hz' _ hmem
    rw [map_sub, eval_C, hlin, sub_eq_zero] at this
    exact this

end GroundTheory.Heights₂.Heights
