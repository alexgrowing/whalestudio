import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

namespace VerticalPointInjective

theorem coord_ne_zero {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (t : T)
    (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ mCoordIdeal y) : y ⟨(), t⟩ ≠ 0 := by
  intro h0
  apply ht
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp {T : Type} [Fintype T] {K' : Type} [Field K']
    (y : (Σ _ : Unit, T) → K') (s : MRing (fun _ : Unit => T)) (hA : IsArithVar (mCoordIdeal y) 1)
    (hs : IsMultiHomog s (fun _ => 1)) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ Unit (fun _ => T) (mCoordIdeal y) s (fun _ => 1) hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ Unit (fun _ => T) _ W hJ hW.1)

end VerticalPointInjective

open VerticalPointInjective in

theorem VertPointInj.proof (hCh : VertPointChart.Statement) : VertPointInj.Statement := by
  intro T _ K' _ _ y s hA hs hsP W hW W' hW' hWW'
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨t', ht'⟩ := hW'.2 ()
  have hyt : y ⟨(), t⟩ ≠ 0 :=
    coord_ne_zero y t fun h => ht (le_sup_left.trans hW.1.1.2 h)
  obtain ⟨hmax, hrat, hform⟩ := hCh T K' y s hA hs hsP W hW t ht
  obtain ⟨-, -, hform'⟩ := hCh T K' y s hA hs hsP W' hW' t' ht'
  obtain ⟨a', b', hb', hab'⟩ := hrat t'
  have hab'' : (b' : K') * y ⟨(), t'⟩ = a' * y ⟨(), t⟩ := by
    rw [← hab']; field_simp
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := isMultiHomogIdeal_of_mem_divSupp y s hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    have he' : IsMultiHomog g (fun _ => e ()) := by
      have : e = fun _ => e () := funext fun u => by cases u; rfl
      rwa [this] at he
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' (e ()) g he').1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform (e ()) g he').2 ⟨a * a' ^ e (), b' ^ e () * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · exact hb' (hmax.isPrime.mem_of_pow_mem _ h)
      · exact hb h
    · push_cast
      calc (b' : K') ^ e () * b * aeval y g = a * ((b' : K') * y ⟨(), t'⟩) ^ e () := by
            rw [mul_assoc, habg]; ring
        _ = _ := by rw [hab'']; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights
