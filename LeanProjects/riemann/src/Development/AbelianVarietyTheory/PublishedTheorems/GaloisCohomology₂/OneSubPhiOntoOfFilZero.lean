import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjective

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

def PhiSubOneOntoFilZero {l : ℕ} [Fact l.Prime] (C : Core l) : Prop :=
  ∀ y : Per.Bcris l, ∃ x : Per.Bcris l, C.ι x ∈ Per.FilD l 0 ∧ Per.φB l x - x = y

def FontaineBcris : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (C : Core l),
    C.TensorInj ∧ C.PhiInj ∧ C.IotaInj ∧ C.Fund ∧ PhiSubOneOntoFilZero C ∧ C.FundOnto ∧ C.Regular

namespace FontaineBcris

variable {l : ℕ} [Fact l.Prime]

theorem tensorInj (h : FontaineBcris) (C : Core l) : C.TensorInj := (h l C).1

theorem phiInj (h : FontaineBcris) (C : Core l) : C.PhiInj := (h l C).2.1

theorem iotaInj (h : FontaineBcris) (C : Core l) : C.IotaInj := (h l C).2.2.1

theorem fund (h : FontaineBcris) (C : Core l) : C.Fund := (h l C).2.2.2.1

theorem ontoFilZero (h : FontaineBcris) (C : Core l) : PhiSubOneOntoFilZero C := (h l C).2.2.2.2.1

theorem fundOnto (h : FontaineBcris) (C : Core l) : C.FundOnto := (h l C).2.2.2.2.2.1

theorem regular (h : FontaineBcris) (C : Core l) : C.Regular := (h l C).2.2.2.2.2.2

theorem oneSubPhiOnto_of_filZero {C : Core l} (h : PhiSubOneOntoFilZero C) : C.OneSubPhiOnto := by
  intro y
  obtain ⟨x, -, hx⟩ := h (-y)
  exact ⟨x, by rw [← neg_sub, hx, neg_neg]⟩

theorem filZero_of_onto {C : Core l} (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : PhiSubOneOntoFilZero C := by
  intro y
  obtain ⟨x, hx⟩ := h1 y
  obtain ⟨b, hb, hF⟩ := h2 (C.ι x)
  refine ⟨b - x, by rwa [map_sub], ?_⟩
  rw [map_sub, hb, ← hx]
  ring

theorem of_rest (h : ∀ (l : ℕ) [Fact l.Prime] (C : Core l),
    C.TensorInj ∧ C.Fund ∧ C.FundOnto ∧ C.Regular) : FontaineBcris := fun l _ C =>
  ⟨(h l C).1, phiB_injective l, (ULaws.u_laws l C).2.2.2.1, (h l C).2.1,
    filZero_of_onto (one_sub_phi_onto l C) (h l C).2.2.1, (h l C).2.2.1, (h l C).2.2.2⟩

example (l : ℕ) [Fact l.Prime] : Nonempty (Core l) := nonempty_core l

end FontaineBcris

end GlobalTheory.Published
