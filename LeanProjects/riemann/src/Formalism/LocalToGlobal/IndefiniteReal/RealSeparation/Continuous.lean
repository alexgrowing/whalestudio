import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FrameMatEqGlobal
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {D : D7} {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V} {s : GA D A →* GA D T}

set_option maxHeartbeats 1000000 in

theorem map_formula_one {R : Type*} [CommRing R] (φ : AE D →+* R) (hι : HSpace.IsIsomEmb A T ι) (h : GA D A)
    (hh : (mt A h).map φ = 1) :
    ((frameMat T A ι).map (incA D) * mt A h * (embP' A T ι).map (incA D) +
      (1 - (frameMat T A ι * embP' A T ι).map (incA D))).map φ = 1 := by
  have e : ((frameMat T A ι).map (incA D) * mt A h * (embP' A T ι).map (incA D)).map φ =
      ((frameMat T A ι * embP' A T ι).map (incA D)).map φ := by
    rw [Matrix.map_mul, Matrix.map_mul, hh, Matrix.mul_one, Matrix.map_mul (f := incA D), Matrix.map_mul]
  rw [Matrix.map_add _ (map_add φ), e, Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    add_sub_cancel]

theorem s_mem_GinfC (hι : HSpace.IsIsomEmb A T ι) (hemb : IsEmbHom ι s) {a : GA D A} (ha : a ∈ GinfC A) :
    s a ∈ GinfC T := by
  have key : ∀ (V : HSp D) (g : GA D V), ((finHom V g : GL (Fin V.rank) _) : Matrix _ _ _) =
      (mt V g).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom :=
    fun V g => rfl
  have ha' : finHom A a = 1 := ha
  have hh : (mt A a).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      = 1 := by
    rw [← key, ha', Units.val_one]
  show finHom T (s a) = 1
  apply Units.ext
  rw [key, Units.val_one, mt_of_embRel hι (hemb a)]
  exact map_formula_one _ hι a hh

end Formalism.IndefR.Mi

end
