import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.GlobalFields.CompletionAtPlace.Degree
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.KummerTheory.Splitting
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.QuadPlace

theorem split_or_inert_of_unramified : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ v : Ad3.Pl, (∀ (w : Ad3.K.PlK K) [w.asIdeal.LiesOver v.asIdeal], w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) → (∃ w₁ w₂ : Ad3.K.PlK K, w₁.asIdeal.LiesOver v.asIdeal ∧ w₂.asIdeal.LiesOver v.asIdeal ∧ w₁ ≠ w₂) ∨ (∃ (w : Ad3.K.PlK K) (_ : w.asIdeal.LiesOver v.asIdeal), (∀ w' : Ad3.K.PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) ∧ Module.finrank (Ad3.Qv v) (Ad3.K.Kv K w) = 2 ∧ GroundTheory.LocalField.ord (algebraMap (Ad3.Qv v) (Ad3.K.Kv K w) (unifUnit (Ad3.Qv v) : Ad3.Qv v)) = 1) := by
  classical
  intro K _ _ h2 v he
  by_cases hd : ∃ w₁ w₂ : Ad3.K.PlK K, w₁.asIdeal.LiesOver v.asIdeal ∧ w₂.asIdeal.LiesOver v.asIdeal ∧ w₁ ≠ w₂
  · exact Or.inl hd
  right
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver K v
  haveI := hw
  have huniq : ∀ w' : Ad3.K.PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w := fun w' h' => by
    by_contra hne
    exact hd ⟨w', w, h', hw, hne⟩
  refine ⟨w, hw, huniq, ?_, ?_⟩
  · have hs := SemiLocal.sum_ramificationIdx_mul_inertiaDeg K v
    rw [Finset.sum_eq_single (⟨w, hw⟩ : SemiLocal.PlacesOver K v)
      (fun b _ hb => absurd (Subtype.ext (huniq b.1 b.2)) hb)
      (fun h => absurd (Finset.mem_univ _) h), h2] at hs
    rw [finrank_adicCompletion v w]
    exact hs
  · have hx : algebraMap (Ad3.Qv v) (Ad3.K.Kv K w) (unifUnit (Ad3.Qv v) : Ad3.Qv v) ≠ 0 := by
      simp
    have h1 := valued_algebraMap_adicCompletion v w (unifUnit (Ad3.Qv v) : Ad3.Qv v)
    rw [he w, pow_one, valued_eq_exp_neg_ord hx, valued_eq_exp_neg_ord (Units.ne_zero _),
      ord_unifUnit] at h1
    exact neg_injective (WithZero.exp_injective h1)

end GlobalTheory.CompanionTheory.QuadPlace
