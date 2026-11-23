import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsWeightedHomogeneousAevalOfHom
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum hilbFn mixedDiff diffStep
  eventualValue)

theorem mixedDiff_single {K : Type*} (b : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    mixedDiff ![b] h m = h m - h (m - b) := by
  simp [mixedDiff, diffStep]

theorem SegreLiftIntNum.proof : SegreLiftIntNum.Statement := by
  intro F _ K _ _ ι _ W _ β
  unfold intNum
  apply FieldNumbers.Relabel.eventualValue_congr
  intro c
  have key : ∀ M : Unit ⊕ K → ℤ, (∀ j, 0 ≤ M j) → (∀ k, β k ≤ M (Sum.inr k)) →
      mixedDiff ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] (hilbFn (segreLift ι F W)) M =
        mixedDiff ![β] (hilbFn W) (fun k => M (Sum.inr k) + M (Sum.inl ())) := by
    intro M h0 hβ
    have h1 : ∀ j, 0 ≤ (M - IndefiniteRowSideFullHecke.Kleiman2.pullDeg β : Unit ⊕ K → ℤ) j := by
      intro j
      rcases j with _ | k
      · simpa [IndefiniteRowSideFullHecke.Kleiman2.pullDeg] using h0 (Sum.inl ())
      · simpa [IndefiniteRowSideFullHecke.Kleiman2.pullDeg] using hβ k
    rw [mixedDiff_single, mixedDiff_single, hilbFn_segreLift F W M h0,
      hilbFn_segreLift F W _ h1]
    congr 2
    funext k
    simp only [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
    ring
  rw [Filter.eventually_atTop, Filter.eventually_atTop]
  constructor
  · rintro ⟨M₀, hM₀⟩
    refine ⟨fun k => max (max (M₀ (Sum.inr k)) 0) (β k) + max (M₀ (Sum.inl ())) 0, fun n hn => ?_⟩
    have ha1 := le_max_left (M₀ (Sum.inl ())) 0
    have ha2 := le_max_right (M₀ (Sum.inl ())) 0
    have hb : ∀ k, M₀ (Sum.inr k) + max (M₀ (Sum.inl ())) 0 ≤ n k ∧
        0 + max (M₀ (Sum.inl ())) 0 ≤ n k ∧ β k + max (M₀ (Sum.inl ())) 0 ≤ n k := by
      intro k
      have := hn k
      have := le_max_left (max (M₀ (Sum.inr k)) 0) (β k)
      have := le_max_right (max (M₀ (Sum.inr k)) 0) (β k)
      have := le_max_left (M₀ (Sum.inr k)) 0
      have := le_max_right (M₀ (Sum.inr k)) 0
      refine ⟨?_, ?_, ?_⟩ <;> linarith
    let M : Unit ⊕ K → ℤ := Sum.elim (fun _ => max (M₀ (Sum.inl ())) 0)
      (fun k => n k - max (M₀ (Sum.inl ())) 0)
    have hMn : (fun k => M (Sum.inr k) + M (Sum.inl ())) = n := by
      funext k
      simp [M]
    rw [← hMn, ← key M ?_ ?_]
    · apply hM₀
      intro j
      rcases j with _ | k
      · exact ha1
      · show M₀ (Sum.inr k) ≤ n k - max (M₀ (Sum.inl ())) 0
        linarith [(hb k).1]
    · intro j
      rcases j with _ | k
      · exact ha2
      · show 0 ≤ n k - max (M₀ (Sum.inl ())) 0
        linarith [(hb k).2.1]
    · intro k
      show β k ≤ n k - max (M₀ (Sum.inl ())) 0
      linarith [(hb k).2.2]
  · rintro ⟨N, hN⟩
    refine ⟨Sum.elim (fun _ => 0) (fun k => max (max (N k) 0) (β k)), fun M hM => ?_⟩
    have hMl : 0 ≤ M (Sum.inl ()) := hM (Sum.inl ())
    have hMr : ∀ k, max (max (N k) 0) (β k) ≤ M (Sum.inr k) := fun k => hM (Sum.inr k)
    have h0 : ∀ j, 0 ≤ M j := by
      intro j
      rcases j with _ | k
      · exact hMl
      · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hMr k)
    have hβ : ∀ k, β k ≤ M (Sum.inr k) := fun k => le_trans (le_max_right _ _) (hMr k)
    rw [key M h0 hβ]
    apply hN
    intro k
    show N k ≤ M (Sum.inr k) + M (Sum.inl ())
    have := le_trans (le_trans (le_max_left (N k) 0) (le_max_left _ (β k))) (hMr k)
    linarith

example : intNum ℚ (segreLift (fun _ : Unit => Fin 2) ℚ ⊥) ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg 1] =
    intNum ℚ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ![1] :=
  SegreLiftIntNum.proof ℚ Unit (fun _ => Fin 2) ⊥ SegreLiftIntNum.hyps 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
