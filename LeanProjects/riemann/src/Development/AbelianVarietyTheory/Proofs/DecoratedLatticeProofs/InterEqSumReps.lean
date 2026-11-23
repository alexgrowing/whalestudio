import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

theorem reps_bijective {V : Type} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) {ι : Type} (s : Finset ι) (z : ι → V)
    (hz : ∀ i ∈ s, z i ∈ A₂) (hinj : ∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j)
    (hsurj : ∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) :
    Function.Bijective (fun i : s => ((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
  constructor
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only at h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : z j - z i ∈ A₁ := by simpa [neg_add_eq_sub] using h
    exact Subtype.ext (hinj j hj i hi this).symm
  · intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨i, hi, hyi⟩ := hsurj y hy
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hyi

theorem inter_eq_sum_reps : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ)
    (A₁ A₂ : AddSubgroup V), Formalism.L2.Th1.H.IsHerm H → Formalism.L2.Th1.H.IsSelfDual H A₂ →
    Formalism.L2.Th1.H.IsSemiChar H A₁ α → Formalism.L2.Th1.H.IsSemiChar H A₂ α → ∀ {ι : Type} (s : Finset ι) (z : ι → V),
    (∀ i ∈ s, z i ∈ A₂) → (∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j) → (∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) →
    ∀ F ∈ Formalism.L2.Th1.H.fixedBy H α A₁, ∀ w, Formalism.L2.Th1.H.inter H α A₁ A₂ F w =
      ((Real.sqrt (s.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, α (z i) * Formalism.L2.Th1.H.opU H (z i) F w := by
  intro V _ _ H α A₁ A₂ hH hd₂ hs₁ hs₂ ι s z hz hinj hsurj F hF w
  classical
  have hφ := reps_bijective A₁ A₂ s z hz hinj hsurj
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Finite.of_surjective _ hφ.2
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = s.card := by
    rw [← Fintype.card_of_bijective hφ, Fintype.card_coe]
  have hinv : ∀ (a : A₂), ∀ t ∈ A₁.addSubgroupOf A₂,
      α ((a + t : A₂) : V) * opU H ((a + t : A₂) : V) F w = α (a : V) * opU H (a : V) F w := by
    intro a t ht
    rw [AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ a.2 t.2,
      opU_of_fixed hs₁ hF (AddSubgroup.mem_addSubgroupOf.1 ht), opU_mul, ← mul_assoc (α t), alpha_sq hs₂ t.2, one_mul]
  rw [congrFun (inter_eq (H := H) (α := α) A₁ A₂ F) w, hcard]
  congr 1
  rw [← Finset.sum_coe_sort s]
  refine (Fintype.sum_bijective _ hφ _ _ fun i => ?_).symm
  have ht : -(⟨z i, hz i i.2⟩ : A₂) + Quotient.out (((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) ∈
      A₁.addSubgroupOf A₂ := by
    rw [← QuotientAddGroup.eq]
    exact (QuotientAddGroup.out_eq' _).symm
  have := hinv ⟨z i, hz i i.2⟩ _ ht
  rw [add_neg_cancel_left] at this
  exact this.symm

end GlobalTheory.ThetaInter
