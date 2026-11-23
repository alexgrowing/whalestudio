import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section
namespace GlobalTheory.InertiaDecomp
open Pointwise

theorem iner_decomp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (g : ↥(GK K)), g ∈ (pc P h hN hF hS).Iner → ∃ s : ↥(GK K), s ∈ IK K ∧ s⁻¹ * g ∈ GKin h := by
  intro l _ P K K' h hN hF hS g hg
  haveI : Nontrivial P.R.B := by
    by_contra hB
    have : Subsingleton P.R.B := not_nontrivial_iff_subsingleton.mp hB
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact Submodule.zero_mem _

  have hfix : ∀ x ∈ K0 K', (g : GQ l) x = x := by
    intro x hx
    have h1 : (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩) = algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩ :=
      hg ⟨x, hx⟩
    rw [P.PD_actB] at h1
    have h2 := P.actQ_Kur ((g : ↥(GK K)) : GQ l) ⟨x, hx.2⟩ ⟨_, GlobalTheory.TameInertiaCyclic.map_mem_Kur _ hx.2⟩ rfl
    have h3 := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h2.symm.trans h1)
    exact congrArg Subtype.val h3
  haveI := K'.2

  let S : Subgroup (GQ l) := (MaximalUnramifiedExtension l).fixingSubgroup ⊔ (K'.1).fixingSubgroup
  have hSo : IsOpen (S : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_right (IntermediateField.fixingSubgroup_isOpen K'.1)
  let SC : ClosedSubgroup (GQ l) := ⟨S, Subgroup.isClosed_of_isOpen S hSo⟩
  have hfe : IntermediateField.fixedField (SC : Subgroup (GQ l)) ≤ K0 K' := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    refine IntermediateField.mem_inf.2 ⟨?_, ?_⟩
    · exact (InfiniteGalois.fixedField_fixingSubgroup K'.1).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_right hf))
    · exact (InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_left hf))
  have hgS : (g : GQ l) ∈ S := by
    have e := InfiniteGalois.fixingSubgroup_fixedField SC
    have : (g : GQ l) ∈ (IntermediateField.fixedField (SC : Subgroup (GQ l))).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hfix x (hfe hx)
    rw [e] at this
    exact this
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  have hgS' : (g : GQ l) ∈ ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l)) * ((K'.1).fixingSubgroup : Set (GQ l)) := by
    rw [← Subgroup.normal_mul]; exact hgS
  obtain ⟨b, hb, a, ha, hba⟩ := hgS'
  have haK : a ∈ GK K := GK_le h ha
  have hbK : b ∈ GK K := by
    have : b = (g : GQ l) * a⁻¹ := by rw [← hba, mul_inv_cancel_right]
    rw [this]; exact mul_mem g.2 (inv_mem haK)
  refine ⟨⟨b, hbK⟩, Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hb x hx, ?_⟩
  rw [GKin, Subgroup.mem_subgroupOf]
  have : (((⟨b, hbK⟩ : ↥(GK K))⁻¹ * g : ↥(GK K)) : GQ l) = a := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hba]; simp
  rw [this]; exact ha

end GlobalTheory.InertiaDecomp
