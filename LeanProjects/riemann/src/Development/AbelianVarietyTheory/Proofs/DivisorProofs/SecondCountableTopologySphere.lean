import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing
import ReciprocityTheory.AnalyticForms.PotentialTheory.FubiniStudyPotentialProductIsPotential

set_option autoImplicit false

noncomputable section

open Set Matrix OnePoint
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame

namespace GlobalTheory.BcUnique

open GlobalTheory.CxForm

def appendV (n m : ℕ) : (V n × V m) ≃L[ℂ] V (n + m) :=
  (((EuclideanSpace.equiv (Fin n) ℂ).prodCongr (EuclideanSpace.equiv (Fin m) ℂ)).trans
    (ReciprocityTheory.AnForm.M.appendCLE n m)).trans (EuclideanSpace.equiv (Fin (n + m)) ℂ).symm

section Prod

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {n m : ℕ}

def prodAtlas (A : HolAtlas M n) (B : HolAtlas N m) : HolAtlas (M × N) (n + m) where
  ι := A.ι × B.ι
  e i := ((A.e i.1).prod (B.e i.2)).transHomeomorph (appendV n m).toHomeomorph
  cover y := ⟨((A.cover y.1).choose, (B.cover y.2).choose), (A.cover y.1).choose_spec, (B.cover y.2).choose_spec⟩
  holo i j := by
    have hA := A.holo i.1 j.1
    have hB := B.holo i.2 j.2
    have e : (((A.e j.1).prod (B.e j.2)).transHomeomorph (appendV n m).toHomeomorph) ∘
        (((A.e i.1).prod (B.e i.2)).transHomeomorph (appendV n m).toHomeomorph).symm =
        fun z => appendV n m ((A.e j.1 ∘ (A.e i.1).symm) ((appendV n m).symm z).1,
          (B.e j.2 ∘ (B.e i.2).symm) ((appendV n m).symm z).2) := rfl
    rw [e]
    have d1 : Differentiable ℂ fun z => ((appendV n m).symm z).1 :=
      ((ContinuousLinearMap.fst ℂ (V n) (V m)).comp ((appendV n m).symm : V (n + m) →L[ℂ] V n × V m)).differentiable
    have d2 : Differentiable ℂ fun z => ((appendV n m).symm z).2 :=
      ((ContinuousLinearMap.snd ℂ (V n) (V m)).comp ((appendV n m).symm : V (n + m) →L[ℂ] V n × V m)).differentiable
    refine (appendV n m).differentiable.comp_differentiableOn (DifferentiableOn.prodMk ?_ ?_)
    · exact hA.comp d1.differentiableOn fun z hz => ⟨hz.1.1, hz.2.1⟩
    · exact hB.comp d2.differentiableOn fun z hz => ⟨hz.1.2, hz.2.2⟩

end Prod

abbrev sphere : HolAtlas (OnePoint ℂ) 1 := HolAtlas.ofFin ReciprocityTheory.AnForm.M.p1

instance secondCountableTopology_sphere : SecondCountableTopology (OnePoint ℂ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin (Module.finrank ℝ ℂ + 1)) (V := ℂ) (by simp)).secondCountableTopology

abbrev famAtlas {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) : HolAtlas (M × OnePoint ℂ) (n + 1) :=
  prodAtlas A sphere

def fib {M : Type} (t : OnePoint ℂ) (y : M) : M × OnePoint ℂ := (y, t)

variable {M : Type} [TopologicalSpace M] {n r s : ℕ} {A : HolAtlas M n}

theorem isHolo_fib (A : HolAtlas M n) (t : OnePoint ℂ) : (famAtlas A).IsHolo A (fib t) := by
  refine ⟨continuous_id.prodMk continuous_const, fun j i => ?_⟩
  have e : (famAtlas A).e i ∘ fib t ∘ (A.e j).symm =
      fun v => appendV n 1 ((A.e i.1 ∘ (A.e j).symm) v, sphere.e i.2 t) := rfl
  rw [e]
  refine (appendV n 1).differentiable.comp_differentiableOn (DifferentiableOn.prodMk ?_ (differentiableOn_const _))
  exact (A.holo j i.1).mono fun v hv => ⟨hv.1, hv.2.1⟩

def IsInduced (T : HermSeq A r s) : Prop :=
  ∀ a, ∀ y ∈ T.U a, T.sub a y = subGram (T.mid a y) ∧ T.quot a y = quotGram (T.mid a y)

def bcFld (T : HermSeq A r s) : A.Fld := fun x =>
  (ofValues (extTrace (fun v => T.mid (T.cover x.pt).choose (x.ch.symm v)) x.crd) : Alt n)

end GlobalTheory.BcUnique
