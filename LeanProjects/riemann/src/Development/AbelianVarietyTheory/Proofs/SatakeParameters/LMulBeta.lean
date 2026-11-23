import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

def Clos {R : Type} [CommRing R] (S : Subring R) (π : R) : Subring R where
  carrier := {x | ∀ n : ℕ, ∃ s ∈ S, π ^ n ∣ x - s}
  mul_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s * s', mul_mem hs hs', a * c' + s' * c, ?_⟩
    linear_combination a * hc' + s' * hc
  one_mem' := fun n => ⟨1, one_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s + s', add_mem hs hs', c + c', ?_⟩
    linear_combination hc + hc'
  zero_mem' := fun n => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha n
    obtain ⟨s, hs, c, hc⟩ := ha n
    refine ⟨-s, neg_mem hs, -c, ?_⟩
    linear_combination -hc

variable {l : ℕ} [Fact l.Prime]

def linv (l : ℕ) [Fact l.Prime] : Per.AinfP l := ((GlobalTheory.RingBasics.isUnit_l l).unit⁻¹ : (Per.AinfP l)ˣ)

theorem mul_linv : ((l : ℕ) : Per.AinfP l) * linv l = 1 := (GlobalTheory.RingBasics.isUnit_l l).mul_val_inv

def beta (ϖ : Per.Fl l) : Per.AinfP l :=
  linv l * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - 1

theorem l_mul_beta (ϖ : Per.Fl l) : ((l : ℕ) : Per.AinfP l) * beta ϖ =
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - ((l : ℕ) : Per.AinfP l) := by
  have h := mul_linv (l := l)
  rw [beta]
  linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) * h

def Sa (ϖ : Per.Fl l) : Subalgebra (Per.Ainf l) (Per.AinfP l) := Algebra.adjoin _ {beta ϖ}

def Sg (ϖ : Per.Fl l) : Subring (Per.BdRp l) :=
  (Sa ϖ).toSubring.map (algebraMap (Per.AinfP l) (Per.BdRp l))

def betaD (ϖ : Per.Fl l) : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ)

end GlobalTheory.Pst.StLat
