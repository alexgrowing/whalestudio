import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

open GlobalTheory.SplitPts in
private noncomputable def cEq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cpl w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (conjE E) w) ⟨(conjLoc (conjE E) w).injective, fun y => ⟨psi w y, conjLoc_psi w y⟩⟩

open GlobalTheory.SplitPts in
private theorem conjInvT_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (g : GL (Fin a) ((cpl w).adicCompletion E)) :
    GlobalTheory.LFun.ConjPlace.invT (cEq w) a g = invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

private theorem invT_invT {R : Type} [CommRing R] {a : ℕ} (h : GL (Fin a) R) : invT a R (invT a R h) = h := by
  apply Units.ext
  change ((invT a R h)⁻¹ : GL (Fin a) R).val.transpose = h.val
  rw [← map_inv]
  change (((h⁻¹)⁻¹ : GL (Fin a) R).val.transpose).transpose = h.val
  rw [inv_inv, Matrix.transpose_transpose]

open GlobalTheory.SplitPts in
private theorem conjInvT_symm_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (h : GL (Fin a) (w.adicCompletion E)) :
    (GlobalTheory.LFun.ConjPlace.invT (cEq w) a).symm h = invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := by
  rw [MulEquiv.symm_apply_eq, conjInvT_eq, invT_map,
    show Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (Matrix.GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _), invT_invT]

open GlobalTheory.SplitPts in
theorem UpperTheory.Gal.Int.Div.locIso_of :
    LocIso := by
  intro E _ _ _ a w hw
  refine ⟨?_, ?_⟩
  · unfold locU
    rw [(over_split hw).2.1]
  let e := GlobalTheory.LFun.ConjPlace.invT (cEq w) a
  have hc1 : Continuous e := by
    have e1 : (e : GL (Fin a) ((cpl w).adicCompletion E) → GL (Fin a) (w.adicCompletion E)) =
        fun g => invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) := funext (conjInvT_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec (conjE E) w).1))
  have hc2 : Continuous e.symm := by
    have e1 : (e.symm : GL (Fin a) (w.adicCompletion E) → GL (Fin a) ((cpl w).adicCompletion E)) =
        fun h => invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := funext (conjInvT_symm_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))
  refine ⟨{ e with continuous_toFun := hc1, continuous_invFun := hc2 }, fun x => ?_, fun g hg => ?_, ?_⟩
  · change e (cLoc (cpl w) x) = cLoc w x
    have h := comp_eq x w
    rw [conjInvT_eq w]
    set m := Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (cLoc (cpl w) x) with hm
    have h' : m.val.transpose * (cLoc w x).val = 1 := h
    apply Units.ext
    change ((m⁻¹ : GL (Fin a) _).val).transpose = (cLoc w x).val
    calc ((m⁻¹ : GL (Fin a) _).val).transpose
        = ((m⁻¹ : GL (Fin a) _).val).transpose * (m.val.transpose * (cLoc w x).val) := by rw [h', Matrix.mul_one]
      _ = (m.val * (m⁻¹ : GL (Fin a) _).val).transpose * (cLoc w x).val := by
          rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (cLoc w x).val := by
          rw [Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  · exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (cEq w)
      (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff (cEq w) (conjLoc_spec (conjE E) w).2.2) g).1 hg
  · intro V _ _ σ hσ
    have h1 := GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap (cEq w).symm
      (conjLoc_spec (conjE E) w).1 (σ.comp (GlobalTheory.TypeTame.invTranspose a))
      (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose _ a V σ hσ)
    convert h1 using 1
    refine MonoidHom.ext fun g => ?_
    change σ (e g) = σ (GlobalTheory.TypeTame.invTranspose a (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g))
    rw [conjInvT_eq w]
    rfl
