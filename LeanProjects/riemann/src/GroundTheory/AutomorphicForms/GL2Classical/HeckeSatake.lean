import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.GL2Classical.HeckePetersson
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.LocalAtPlace

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm ValuativeRel Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Rat.HeightOneSpectrum

variable (p : ℕ) [hp : Fact p.Prime]

def placeAt : HeightOneSpectrum (𝓞 ℚ) := (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩

variable {p}

variable (p)

abbrev Qp : Type := (placeAt p).adicCompletion ℚ

abbrev locMat (γ : GL (Fin 2) ℚ) : GL (Fin 2) (Qp p) :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qp p)) γ

def toInts (x : 𝒪[Qp p]) : (placeAt p).adicCompletionIntegers ℚ :=
  ⟨x, (GroundTheory.Global.mem_valuationInteger_iff (placeAt p) (x : Qp p)).1 x.2⟩

def ofInts (y : (placeAt p).adicCompletionIntegers ℚ) : 𝒪[Qp p] :=
  ⟨(y : Qp p), (GroundTheory.Global.mem_valuationInteger_iff (placeAt p) (y : Qp p)).2 y.2⟩

theorem toInts_mul (x y : 𝒪[Qp p]) : toInts p (x * y) = toInts p x * toInts p y := Subtype.ext rfl

def integersMulEquiv : 𝒪[Qp p] ≃* (placeAt p).adicCompletionIntegers ℚ :=
  { toFun := toInts p, invFun := ofInts p, left_inv := fun _ => Subtype.ext rfl,
    right_inv := fun _ => Subtype.ext rfl, map_mul' := toInts_mul p }

theorem irreducible_toInts : Irreducible (toInts p (GLnLocal.uniformizer (Qp p))) :=
  (MulEquiv.irreducible_iff (integersMulEquiv p)).2 (GLnLocal.irreducible_uniformizer (Qp p))

theorem valued_uniformizer :
    Valued.v (GLnLocal.uniformizer (Qp p) : Qp p) = WithZero.exp (-1 : ℤ) := by
  have h := GroundTheory.Global.valued_of_irreducible (placeAt p) (irreducible_toInts p)
  exact h

theorem uniformizer_ne_zero : (GLnLocal.uniformizer (Qp p) : Qp p) ≠ 0 := fun h =>
  (GLnLocal.irreducible_uniformizer (Qp p)).ne_zero (Subtype.ext h)

variable {N : ℕ} [NeZero N]

open Spherical Iwasawa

def localRightRep : Representation ℂ (GL (Fin 2) (Qp p)) (AdelicGL ℚ 2 → ℂ) :=
  finRightRep.comp (localEmbedding (placeAt p))

variable {k : ℤ}

theorem gMat_univ (c : Pairs (Finset.univ : Finset (Fin 2)) → 𝓀[Qp p]) :
    gMat Finset.univ c = torusPow (Qp p) 2 (fun _ => 1) := by
  ext i j
  rw [gMat_apply, coe_torusPow, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
  simp [lamS, Matrix.one_apply, Matrix.diagonal_apply]

variable [MeasurableSpace (GL (Fin 2) (Qp p))] [BorelSpace (GL (Fin 2) (Qp p))]
  (μ : Measure (GL (Fin 2) (Qp p))) [μ.IsHaarMeasure]

end GL2Classical

end

end GroundTheory.Automorphic
