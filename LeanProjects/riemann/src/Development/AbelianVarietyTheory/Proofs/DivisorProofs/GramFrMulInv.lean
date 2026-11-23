import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.FlipTranslate

open GlobalTheory.ExportSeries.Model (ct)

variable {D : D7}

def gramFr (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D) :=
  ct β.val * V.gram.map (eToEAf D) * β.val

def gramFrInv (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D) :=
  (β⁻¹).val * (V.gram⁻¹).map (eToEAf D) * ct (β⁻¹).val

def diagW (D : D7) (n r : ℕ) (a : D.host.E) : Matrix (Fin n) (Fin n) (Datum.EAf D) :=
  Matrix.diagonal fun k => if k.val < r then 1 else eToEAf D a

def IsFlipElt (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (r : ℕ) (e : AE D) (a : D.host.E) (g : GA D V) : Prop :=
  SuppAt e V g ∧ toEAf D e • ((β⁻¹).val * (mt V g).map (toEAf D) * β.val) = toEAf D e • (diagW D V.rank r a * gramFr V β)

def conjK (PP : Pl D.host.E) : kP PP →+* kP (conjPl PP) :=
  Ideal.quotientMap (conjPl PP).asIdeal starOHom fun a ha => by
    show starO (starO a) ∈ PP.asIdeal
    rwa [starO_starO]

theorem conjK_mk (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    conjK PP (Ideal.Quotient.mk PP.asIdeal a) = Ideal.Quotient.mk (conjPl PP).asIdeal (starO a) := rfl

theorem resS_conj (PP : Pl D.host.E) (s s' : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : (s' : Datum.EAf D) = GlobalTheory.AdelicLatMove.cF D (s : Datum.EAf D)) :
    resS D.host.F (conjPl PP) s' = conjK PP (resS D.host.F PP s) := by
  have e : s' = sigS D.sp.cm s := Subtype.ext (h.trans (sigS_coe _ _).symm)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resS D.host.F PP s)
  have h0 : resS D.host.F PP (s - oToS D.host.F D.host.E a) = 0 := by rw [map_sub, resS_oToS, ha, sub_self]
  have h1 := (resS_sigS_eq_zero_iff D.sp.cm (isConjPl_conjPl PP) _).2 h0
  rw [map_sub, map_sub, sigS_oToS, resS_oToS, sub_eq_zero] at h1
  rw [e, h1, ← ha, conjK_mk]

theorem gramFr_mul_inv (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : gramFr V β * gramFrInv V β = 1 := by
  have h1 : ct β.val * ct (β⁻¹).val = 1 := by
    rw [← GlobalTheory.ExportSeries.Model.ct_mul, Units.inv_mul]
    simp [ct]
  unfold gramFr gramFrInv
  calc _ = ct β.val * (V.gram.map (eToEAf D) * (β.val * (β⁻¹).val) * (V.gram⁻¹).map (eToEAf D)) * ct (β⁻¹).val := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, GlobalTheory.PlaceVec.gram_map_mul_inv, Matrix.mul_one, h1]

theorem gramFr_int {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Datum.EAf D)}
    (hV : IsSelfDualC V Λ) (f : Formalism.L2.DIV.IsFrame β Λ) : IsIntM (gramFr V β) ∧ IsIntM (gramFrInv V β) :=
  GlobalTheory.ExportSeries.Model.gram_frame_int V hV f

theorem diagW_mul (n r : ℕ) (a b : D.host.E) : diagW D n r a * diagW D n r b = diagW D n r (a * b) := by
  unfold diagW
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs
  · rw [one_mul]
  · rw [map_mul]

theorem diagW_one (n r : ℕ) : diagW D n r 1 = 1 := by
  unfold diagW
  simp only [map_one, ite_self, Matrix.diagonal_one]

theorem diagW_int (n r : ℕ) (a : 𝓞 D.host.E) : IsIntM (diagW D n r (a : D.host.E)) := by
  intro i j
  unfold diagW
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact one_mem _
  · exact Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)
  · exact zero_mem _

end GlobalTheory.FlipTranslate
