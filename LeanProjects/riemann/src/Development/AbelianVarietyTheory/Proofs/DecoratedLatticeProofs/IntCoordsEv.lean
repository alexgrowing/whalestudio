import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlaceStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

theorem alg_int_ev (c : D.host.F) : ∀ᶠ w in Filter.cofinite,
    algebraMap D.host.F (Fv D.host.F w) c ∈ (w : Pl D).adicCompletionIntegers D.host.F :=
  (algebraMap D.host.F (Af D.host.F) c).2

theorem repr_tmul_loc (w : Pl D) (x : Fv D.host.F w) (e : D.host.E) (i : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (x ⊗ₜ[D.host.F] e) i =
      x * algebraMap D.host.F (Fv D.host.F w) ((Module.finBasis D.host.F D.host.E).repr e i) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

theorem int_coords_ev : ∀ᶠ w in Filter.cofinite, ∀ z ∈ intAE D, ∀ i,
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
      (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z) i ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ w in Filter.cofinite, ∀ i j,
      algebraMap D.host.F (Fv D.host.F w) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) i) ∈
        (w : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact alg_int_ev _
  filter_upwards [hev] with w hw
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, o, rfl⟩ := hy
    intro i
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [hc, repr_tmul_loc]
    refine mul_mem (hα w) ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl
    rw [ho, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hw i j) _
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [map_add, map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  | neg x _ hx => intro i; rw [map_neg, map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

theorem sum_repr_tmul (w : Pl D) (y : Fv D.host.F w ⊗[D.host.F] D.host.E) :
    ∑ i, (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr y i ⊗ₜ[D.host.F]
      (Module.finBasis D.host.F D.host.E) i = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem glue : ∀ (D : D7) (a : Pl D → AE D), (∀ x, a x ∈ idAt D (· = x)) →
    (∃ T : Finset (Pl D), ∀ x ∉ T, a x ∈ intAt D (· = x)) →
    ∃ s : AE D, infPart D s = 0 ∧ ∀ x, s - a x ∈ idOff D (· = x) := by
  intro D a _ ⟨T, hT⟩
  classical
  set b := Module.finBasis D.host.F D.host.E
  let c : Fin (Module.finrank D.host.F D.host.E) → (w : Pl D) → Fv D.host.F w := fun i w =>
    (Algebra.TensorProduct.basis (Fv D.host.F w) b).repr (compAt D w (a w)) i
  have hc : ∀ i, ∀ᶠ w in Filter.cofinite, c i w ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
    intro i
    filter_upwards [int_coords_ev (D := D), T.finite_toSet.compl_mem_cofinite] with w hw hwT
    exact hw _ (hT w hwT).2 i
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun i => RestrictedProduct.mk (c i) (hc i)
  refine ⟨∑ i, pairA D.host.F 0 (C i) ⊗ₜ[D.host.F] b i, ?_, fun x => ?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => infPart_pair _ _
  · unfold idOff
    refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
    obtain ⟨w, rfl⟩ := w
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [compAt_pair]
    exact sum_repr_tmul w (compAt D w (a w))

end GlobalTheory.FinPlLoc
