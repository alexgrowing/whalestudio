import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem cj_cj (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (UpperTheory.Gal.Int.Div.cj E z) = z :=
  Units.ext (GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol _)

private theorem cj_quo_mul (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (quo E z) * quo E z = 1 := by
  rw [quo_apply, _root_.map_div, cj_cj, div_mul_div_comm, mul_comm z, div_self']

private theorem scal_mem (a : ℕ) (y : Ideles E) (h : UpperTheory.Gal.Int.Div.cj E y * y = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin a) y ∈ UA E a := by
  have hy : conjAd E (y : Ad E) * (y : Ad E) = 1 := congrArg Units.val h
  have e : ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) =
      Matrix.diagonal fun _ => (y : Ad E) := rfl
  show (((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).map (conjAd E)).transpose * 1 *
    ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1
  rw [e, Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  simp only [Function.comp_apply, hy]
  exact Matrix.diagonal_one

private theorem continuous_scal (a : ℕ) :
    Continuous (fun y : Ideles E => (Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a)) :=
by
  have h : Continuous ((Matrix.scalar (Fin a)).toMonoidHom : Ad E →* Matrix (Fin a) (Fin a) (Ad E)) :=
    Continuous.matrix_diagonal (A := fun (x : Ad E) (_ : Fin a) => x) (continuous_pi fun _ => continuous_id)
  exact Continuous.units_map _ h

private theorem continuous_quo : Continuous (quo E) :=
  continuous_id.div' (Continuous.units_map _ GlobalTheory.BCT.GlobLev.continuous_conj_ad)

private theorem ratGL_scalar (a : ℕ) (k : Eˣ) :
    ratGL E a (Matrix.GeneralLinearGroup.scalar (Fin a) k) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (diagUnits E k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap E (Ad E) (Matrix.diagonal (fun _ => (k : E)) i j) =
    Matrix.diagonal (fun _ => algebraMap E (Ad E) (k : E)) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem quo_diag (k : Eˣ) :
    quo E (diagUnits E k) =
      diagUnits E (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) := by
  have e : UpperTheory.Gal.Int.Div.cj E (diagUnits E k) =
      diagUnits E (Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) :=
    Units.ext (conjAd_algebraMap (k : E))
  rw [quo_apply, e, _root_.map_div]

end

theorem UpperTheory.Gal.Int.Div.zetaEx_of :
    ZetaEx := by
  intro E _ _ _ a
  refine ⟨MonoidHom.codRestrict ((Matrix.GeneralLinearGroup.scalar (Fin a)).comp (quo E)) (UA E a)
    (fun z => scal_mem a _ (cj_quo_mul z)), fun z => rfl, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((continuous_scal a).comp continuous_quo) _
  · intro z x
    refine Subtype.ext (Units.ext ?_)
    exact (Matrix.scalar_commute ((quo E z : Ideles E) : Ad E) (fun r => mul_comm _ r) x.1.val).eq
  · intro k
    refine Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.scalar (Fin a)
      (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k), ?_⟩
    rw [ratGL_scalar, ← quo_diag]
    rfl
  · intro z hz
    refine Subtype.ext ?_
    change Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z) = 1
    rw [quo_apply, hz, div_self', map_one]
