import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.TamCnt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

def compV (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E)

def locHom (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.Published.SUAdelic σ J →* GL (Fin M) (Fv F v ⊗[F] E) where
  toFun h := Units.map (compV (E := E) v).toRingHom.mapMatrix.toMonoidHom (HA.mat (AF F) σ J h.1)
  map_one' := by
    change Units.map (compV (E := E) v).toRingHom.mapMatrix.toMonoidHom (1 : GL (Fin M) (AF F ⊗[F] E)) = 1
    exact map_one _
  map_mul' a b := by
    change Units.map (compV (E := E) v).toRingHom.mapMatrix.toMonoidHom
      (HA.mat (AF F) σ J a.1 * HA.mat (AF F) σ J b.1) = _
    exact map_mul _ _ _

theorem locHom_val (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (h : GlobalTheory.Published.SUAdelic σ J) :
    ((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) =
      (finMat σ J h.1).map (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) := by
  unfold finMat
  rw [Matrix.map_map]
  change (compV (E := E) v).toRingHom.mapMatrix
      ((HA.mat (AF F) σ J h.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = _
  rw [RingHom.mapMatrix_apply]
  congr 1
  funext x
  change compV v x = (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) x
  rw [← Algebra.TensorProduct.map_comp]
  rfl

end GlobalTheory.TamCnt
