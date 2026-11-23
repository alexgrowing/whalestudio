import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtPosOfMemDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace VerticalPointLength

theorem maximal_and_mult_eq (hCh : VertPointChart.Statement) (hMC : VertPointMultChart.Statement)
    (hSQ : SectionQuotLocal.Statement) {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} {s : MRing (fun _ : Unit => T)} (hP : IsArithVar (mCoordIdeal y) 1)
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W = locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) := by
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨hmax, hrat, hmem⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, b, -, hb, hab⟩ := (hmem 1 s hs).mp hsW
  rw [pow_one] at hab
  refine ⟨hmax, ?_⟩
  rw [hMC T K' y s hP hs hsP W hW t ht a b hb hab,
    hSQ T K' y s hP hs hsP _ t hmax.isPrime hrat a b hb hab]

end VerticalPointLength

theorem VertPointLength.proof (hCh : VertPointChart.Statement)
    (hInj : VertPointInj.Statement) (hSurj : VertPointSurj.Statement)
    (hMC : VertPointMultChart.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointLength.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj T K' y s hP hs hsP,
      fun m hm => hSurj T K' y s hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights
