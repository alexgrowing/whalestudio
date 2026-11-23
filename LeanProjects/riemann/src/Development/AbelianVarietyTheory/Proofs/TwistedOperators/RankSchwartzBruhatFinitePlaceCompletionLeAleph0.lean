import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.SBCount

open TopologicalSpace Cardinal

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {K : Set X | IsCompact K ∧ IsOpen K}.Countable := by
  classical
  have hB := isBasis_countableBasis X
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  refine (Set.countable_range fun t : Finset (countableBasis X) => ⋃ b ∈ t, (b : Set X)).mono ?_
  rintro K ⟨hKc, hKo⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun b : {b : countableBasis X // (b : Set X) ⊆ K} => (b.1 : Set X))
    (fun b => hB.isOpen b.1.2) (fun x hx => by
      obtain ⟨b, hbB, hxb, hbK⟩ := hB.exists_subset_of_mem_open hx hKo
      exact Set.mem_iUnion.2 ⟨⟨⟨b, hbB⟩, hbK⟩, hxb⟩)
  refine ⟨t.image (fun c => c.1), ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hb
    exact c.2 hxb
  · intro x hx
    have := ht hx
    rw [Set.mem_iUnion₂] at this
    obtain ⟨c, hc, hxc⟩ := this
    rw [Set.mem_iUnion₂]
    exact ⟨c.1, Finset.mem_image.2 ⟨c, hc, rfl⟩, hxc⟩

theorem finite_range_of_sb {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : (Set.range f).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun w => f ⁻¹' {w}) (fun w => hf _)
    fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩
  refine (t.finite_toSet.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : f x = 0
  · exact Or.inl hx
  · simpa using Or.inr (by simpa using ht (subset_tsupport f hx))

theorem sb_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun K : Set X => K.indicator (1 : X → ℂ)) '' {K : Set X | IsCompact K ∧ IsOpen K}) := by
  classical
  rintro f ⟨hf, hcs⟩
  have hfin := finite_range_of_sb hf hcs
  have hsum : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · rw [hx]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
      have : x ∉ f ⁻¹' {c} := by simp [hx, Ne.symm hc0]
      simp [Set.indicator_of_notMem this]
    · rw [Finset.sum_eq_single (f x)]
      · simp
      · intro c _ hcx
        have : x ∉ f ⁻¹' {c} := by simp [Ne.symm hcx]
        simp [Set.indicator_of_notMem this]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨hx, by simp⟩) h
  rw [hsum]
  refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {c}, ⟨?_, hf _⟩, rfl⟩)
  have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
  refine hcs.isCompact.of_isClosed_subset (hf.isClosed_fiber c) fun x hx => subset_tsupport f ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [Function.mem_support, hx, hc0]

theorem rank_sb_le_aleph0 (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (sb_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compactOpen X).image _).to_subtype

theorem rank_sb_localField_le : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (κ : Type) [Fintype κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  intro F _ _ v κ _
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI := GlobalTheory.LocAtTopology.secondCountable_localField (Fv F v)
  exact rank_sb_le_aleph0 _

end GlobalTheory.SBCount
