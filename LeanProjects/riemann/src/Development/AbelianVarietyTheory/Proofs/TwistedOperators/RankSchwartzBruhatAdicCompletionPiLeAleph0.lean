import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SBCount

theorem countable_compact_open (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsCompact U ∧ IsOpen U}.Countable := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  refine ((Set.countable_setOf_finite_subset hbc).image Set.sUnion).mono ?_
  rintro U ⟨hUc, hUo⟩
  obtain ⟨S, hSb, rfl⟩ := hb.open_eq_sUnion hUo
  obtain ⟨t, htS, htf, hcov⟩ := hUc.elim_finite_subcover_image (b := S) (c := id)
    (fun s hs => hb.isOpen (hSb hs)) (by intro x hx; simpa using hx)
  refine ⟨t, ⟨htf, htS.trans hSb⟩, ?_⟩
  refine le_antisymm (Set.sUnion_subset_sUnion htS) ?_
  intro x hx
  simpa using hcov hx

theorem SB_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (fun _ => (1 : ℂ))) '' {U : Set X | IsCompact U ∧ IsOpen U}) := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  obtain ⟨s, hs⟩ := hcs.isCompact.elim_finite_subcover (fun a : ℂ => f ⁻¹' {a})
    (fun a => hlc.isOpen_fiber a) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hf_eq : f = ∑ a ∈ s, a • (f ⁻¹' {a}).indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator, Set.mem_preimage,
      Set.mem_singleton_iff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_cases hx : x ∈ tsupport f
      · exact absurd (by simpa using hs hx) h
      · exact image_eq_zero_of_notMem_tsupport hx
  rw [hf_eq]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = 0
  · simp [ha]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {a}, ⟨?_, hlc.isOpen_fiber a⟩, rfl⟩)
    refine hcs.isCompact.of_isClosed_subset (hlc.isClosed_fiber a) ?_
    intro x hx
    refine subset_tsupport f ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [Function.mem_support, hx, ha]

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (SB_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compact_open X).image _).to_subtype

end GlobalTheory.SBCount

namespace GlobalTheory.TripleAssembly

theorem rank_SB_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  intro F _ _ κ _ v
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  exact GlobalTheory.SBCount.rank_SB_le _

end GlobalTheory.TripleAssembly
