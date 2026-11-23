import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D}

def divPts (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) : AddSubgroup (WO S T) where
  carrier := {y | c • y = y ∧ N • y ∈ Λ}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], by rw [nsmul_add]; exact Λ.add_mem hx2 hy2⟩
  zero_mem' := ⟨smul_zero _, by rw [nsmul_zero]; exact Λ.zero_mem⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], by rw [smul_neg]; exact Λ.neg_mem hx2⟩

theorem mem_divPts {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} {y : WO S T} :
    y ∈ divPts Λ c N ↔ c • y = y ∧ N • y ∈ Λ := Iff.rfl

abbrev DQ (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) :=
  ↥(divPts Λ c N) ⧸ (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N)

noncomputable def rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) : ↥(divPts Λ c N) :=
  (QuotientAddGroup.mk_surjective q).choose

theorem mk_rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) :
    (QuotientAddGroup.mk (rep q) : DQ Λ c N) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

theorem rep_injective {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} :
    Function.Injective fun q : DQ Λ c N => ((rep q : ↥(divPts Λ c N)) : WO S T) := by
  intro q₁ q₂ h
  rw [← mk_rep q₁, ← mk_rep q₂, Subtype.ext h]

variable (ψ : AddChar (AF D.host.F) ℂ)

noncomputable def qChar (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) (t : WO S T)
    (ht : ∀ g ∈ Λ, ψ (symplO S T t g) = 1) : AddChar (DQ Λ c N) ℂ where
  toFun q := Quotient.liftOn' q (fun y => ψ (symplO S T t y)) (fun y₁ y₂ h => by
    have h' := QuotientAddGroup.leftRel_apply.mp h
    rw [AddSubgroup.mem_addSubgroupOf] at h'
    have : ((y₂ : ↥(divPts Λ c N)) : WO S T) = y₁ + ((-y₁ + y₂ : ↥(divPts Λ c N)) : WO S T) := by
      push_cast; abel
    rw [this, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul, ht _ h'.1, mul_one])
  map_zero_eq_one' := by
    change ψ (symplO S T t 0) = 1
    rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
  map_add_eq_mul' q₁ q₂ := by
    induction q₁ using QuotientAddGroup.induction_on with
    | H y₁ =>
    induction q₂ using QuotientAddGroup.induction_on with
    | H y₂ =>
    change ψ (symplO S T t ((y₁ + y₂ : ↥(divPts Λ c N)) : WO S T)) = ψ (symplO S T t y₁) * ψ (symplO S T t y₂)
    rw [AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

end GlobalTheory.DivPtFourier
