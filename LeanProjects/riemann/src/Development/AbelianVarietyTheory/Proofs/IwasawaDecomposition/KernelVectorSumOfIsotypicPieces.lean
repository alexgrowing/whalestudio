import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.DecompKer

open Formalism.L2.NG (FinTyp)

def isoSetoid (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Setoid (FinTyp L n) where
  r π π' := π.Iso π'
  iseqv := ⟨fun π => Formalism.L2.NG.IsoRep.refl _, fun {π _} h => Formalism.L2.NG.IsoRep.symm π.stable h,
    fun h h' => Formalism.L2.NG.IsoRep.trans h h'⟩

theorem isotIn_le_of_iso {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) {π π' : FinTyp D.host.E n}
    (h : π.Iso π') : principalLevelFrame.isotIn (D := D) ρ C π' ≤ principalLevelFrame.isotIn (D := D) ρ C π := by
  obtain ⟨T, hT⟩ := h
  refine iSup₂_le fun Φ hΦ => ?_
  rintro _ ⟨f, rfl⟩
  have hE : principalLevelFrame.IsEqvA ρ π (Φ.comp T.toLinearMap) ∧ LinearMap.range (Φ.comp T.toLinearMap) ≤ C := by
    refine ⟨fun g a => ?_, ?_⟩
    · have e : T ⟨Formalism.L2.NG.rt D.host.E n g a, π.stable g a a.2⟩ =
          ⟨Formalism.L2.NG.rt D.host.E n g (T a), π'.stable g _ (T a).2⟩ :=
        Subtype.ext (hT g a _ rfl)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [e]
      exact hΦ.1 g (T a)
    · rintro _ ⟨a, rfl⟩
      exact hΦ.2 ⟨T a, rfl⟩
  refine Submodule.mem_iSup_of_mem (Φ.comp T.toLinearMap) (Submodule.mem_iSup_of_mem hE ⟨T.symm f, ?_⟩)
  simp

end GlobalTheory.DecompKer

open GlobalTheory.DecompKer in

theorem GlobalTheory.decomp_kernels_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  intro D n A _ _ ρ C B h1 h2 h3 h4 ι O hO x hx hOx
  classical
  let S := isoSetoid D.host.E n
  let q : Formalism.L2.NG.FinTyp D.host.E n → Quotient S := Quotient.mk S
  have hC : ∀ π, principalLevelFrame.isotIn (D := D) ρ C π ≤ C := fun π => iSup₂_le fun Φ h => h.2
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hx
  set t := f.support.image q with ht
  let y : Quotient S → A := fun c => ∑ π ∈ f.support with q π = c, f π
  have hxy : (f.sum fun _ xi => xi) = ∑ c ∈ t, y c := by
    rw [Finsupp.sum]
    exact (Finset.sum_fiberwise_of_maps_to (fun π hπ => Finset.mem_image_of_mem q hπ) _).symm
  have hrep : ∀ π c, q π = c → c.out.Iso π := fun π c hq =>
    Quotient.exact (s := S) (by rw [Quotient.out_eq]; exact hq.symm)
  have hyI : ∀ c, y c ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := by
    intro c
    refine Submodule.sum_mem _ fun π hπ => ?_
    exact isotIn_le_of_iso ρ C (hrep π c (Finset.mem_filter.mp hπ).2) (hf π)
  have hni : ∀ c c' : Quotient S, c ≠ c' → ¬ c.out.Iso c'.out := by
    intro c c' hne hI
    apply hne
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound hI
  have hB0 : ∀ u ∈ C, B u 0 = 0 := by
    intro u hu
    have := h1 u hu 0 C.zero_mem 0 C.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at this
    simpa using this
  have hOy : ∀ i, ∀ c ∈ t, O i (y c) = 0 := by
    intro i c hc
    set u := O i (y c) with hu
    have huI : u ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := hO i c.out (y c) (hyI c)
    have huC : u ∈ C := hC _ huI

    let Z : Submodule ℂ A :=
      { carrier := {v | v ∈ C ∧ B u v = 0}
        zero_mem' := ⟨C.zero_mem, hB0 u huC⟩
        add_mem' := fun {a b} ha hb => ⟨C.add_mem ha.1 hb.1, by
          have := h1 u huC a ha.1 b hb.1 1
          rw [one_smul] at this
          rw [this, ha.2, hb.2]; simp⟩
        smul_mem' := fun c' a ha => ⟨C.smul_mem c' ha.1, by
          have := h1 u huC 0 C.zero_mem a ha.1 c'
          rw [zero_add] at this
          rw [this, hB0 u huC, ha.2]; simp⟩ }
    have hsum : ∑ c' ∈ t, O i (y c') = 0 := by
      rw [← map_sum, ← hxy]; exact hOx i
    have hrest : ∑ c' ∈ t.erase c, O i (y c') ∈ Z := by
      refine Submodule.sum_mem _ fun c' hc' => ?_
      have hne : c' ≠ c := (Finset.mem_erase.mp hc').1
      have hv : O i (y c') ∈ principalLevelFrame.isotIn (D := D) ρ C c'.out := hO i c'.out (y c') (hyI c')
      exact ⟨hC _ hv, h4 c.out c'.out (hni c c' (Ne.symm hne)) u huI _ hv⟩
    have hueq : u = -∑ c' ∈ t.erase c, O i (y c') := by
      rw [eq_neg_iff_add_eq_zero, hu, Finset.add_sum_erase t (fun c' => O i (y c')) hc, hsum]
    have huZ : u ∈ Z := by rw [hueq]; exact Z.neg_mem hrest
    by_contra hne
    have := h3 u huC hne
    rw [huZ.2] at this
    simp at this
  rw [hxy]
  refine Submodule.sum_mem _ fun c hc => ?_
  refine Submodule.mem_iSup_of_mem c.out (Submodule.mem_inf.mpr ⟨hyI c, ?_⟩)
  exact Submodule.mem_iInf _ |>.mpr fun i => LinearMap.mem_ker.mpr (hOy i c hc)
