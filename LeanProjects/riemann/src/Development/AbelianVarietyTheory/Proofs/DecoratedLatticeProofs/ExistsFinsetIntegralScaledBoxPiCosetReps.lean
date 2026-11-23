import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxReps

def boxSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) (s : kˣ) : AddSubgroup (n → k) where
  carrier := box n s
  add_mem' hx hy i _ := add_mem_cball (hx i trivial) (hy i trivial)
  zero_mem' i _ := by simp [cball]
  neg_mem' hx i _ := neg_mem_cball (hx i trivial)

theorem exists_finset_box_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  intro k _ _ _ _ n _ r R _
  classical
  set H := boxSubgroup k n r
  have hH : ∀ x, x ∈ H ↔ x ∈ box n r := fun _ => Iff.rfl
  have hq : ∀ a b : n → k, (QuotientAddGroup.mk a : (n → k) ⧸ H) = QuotientAddGroup.mk b ↔ a - b ∈ box n r := by
    intro a b
    rw [QuotientAddGroup.eq, ← hH, ← H.neg_mem_iff]
    simp [neg_add_eq_sub]
  obtain ⟨T, hTsub, hTfin, hcov⟩ := (isCompact_box (n := n) R).elim_finite_subcover_image
    (b := box n R) (c := fun a => (fun x => x - a) ⁻¹' box n r)
    (fun a _ => (isOpen_box r).preimage (continuous_id.sub continuous_const))
    (fun x hx => Set.mem_biUnion hx (show x - x ∈ box n r by rw [sub_self]; exact (boxSubgroup k n r).zero_mem))
  set π : (n → k) → (n → k) ⧸ H := QuotientAddGroup.mk
  let f : (n → k) ⧸ H → (n → k) := fun q =>
    if h : ∃ a ∈ box n R, π a = q then Classical.choose h else 0
  have hf : ∀ a ∈ box n R, f (π a) ∈ box n R ∧ π (f (π a)) = π a := by
    intro a ha
    have h : ∃ b ∈ box n R, π b = π a := ⟨a, ha, rfl⟩
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  refine ⟨(hTfin.toFinset.image π).image f, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
    obtain ⟨q, ⟨t, ht, rfl⟩, rfl⟩ := hb
    exact (hf t (hTsub ht)).1
  · intro a ha
    obtain ⟨t, ht, hat⟩ := Set.mem_iUnion₂.mp (hcov ha)
    have hat' : π a = π t := (hq a t).mpr hat
    refine ⟨f (π a), ⟨?_, ?_⟩, ?_⟩
    · simp only [Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨π t, ⟨t, ht, rfl⟩, by rw [hat']⟩
    · exact (hq a _).mp (hf a ha).2.symm
    · rintro b ⟨hb, hab⟩
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
      obtain ⟨q, ⟨t', ht', rfl⟩, rfl⟩ := hb
      have h1 : π a = π (f (π t')) := (hq a _).mpr hab
      rw [(hf t' (hTsub ht')).2] at h1
      rw [h1]

end GlobalTheory.BoxReps
