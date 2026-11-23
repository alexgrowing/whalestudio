import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionNormOneNearReSqNeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberFieldStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem traceOpen_field (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
    (h2 : (2 : K) ≠ 0) (hnb : (𝓝[≠] (0 : K)).NeBot) (hsq : SqOpen K) (a b : K) (ha : a ≠ 0) : TraceOpen K a b := by
  intro g hg W hW
  obtain ⟨g', hg'1, hg're, hW'⟩ := GlobalTheory.T.exists_quaternion_normOne_near_re_sq_ne_one K h2 hnb a b ha g hg W hW
  have hu : IsUnit (1 - g'.re ^ 2) := IsUnit.mk0 _ (sub_ne_zero.2 (Ne.symm hg're))
  obtain ⟨O, hO, hmem, hO'⟩ := GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit K a b hsq g' hg'1 hu W hW'
  exact ⟨O, hO, ⟨_, hmem⟩, hO'⟩

theorem traceOpen_inf (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) :
    TraceOpen (InfiniteAdeleRing F) (algebraMap F (InfiniteAdeleRing F) a) (algebraMap F (InfiniteAdeleRing F) b) := by
  refine GlobalTheory.T.quaternionNormOneTraceOpen_pi (InfinitePlace F) (fun w => w.Completion) _ _ (fun w => ?_)
  have h2 : (2 : w.Completion) ≠ 0 := by
    have := (map_ne_zero (algebraMap F w.Completion)).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot F w) (GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero _ h2) _ _ ((map_ne_zero (algebraMap F w.Completion)).2 ha)

theorem traceOpen_fin (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a)
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  refine GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing F a b (fun v => ?_) (GlobalTheory.T.eventually_exists_quaternion_norm_one_re_eq F a b ha hb)
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have := (map_ne_zero (algebraMap F (v.adicCompletion F))).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField F v).2 (GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField F v).1 _ _ ((map_ne_zero (algebraMap F _)).2 ha)

theorem traceOpen_adele : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro F _ _ a b ha hb g hg W hW
  have H : TraceOpen (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) :=
    GlobalTheory.T.quaternionNormOneTraceOpen_prod _ _ _ _ _ _ (traceOpen_inf F a b ha) (traceOpen_fin F a b ha hb)
  exact H g hg W hW
end GlobalTheory.QSA
