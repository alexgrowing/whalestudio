import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameGLTwoDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import Formalism.PeriodIntegrals.CuspInfChar

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.GLTwoHecke

section Matrices

variable {R : Type} [CommRing R]

def dg (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, (b : R)], !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

def up (b : R) : GL (Fin 2) R :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

variable (R) in

def wy : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

@[simp] theorem dg_val (a b : Rˣ) : (dg a b).1 = !![(a : R), 0; 0, (b : R)] := rfl
@[simp] theorem up_val (b : R) : (up b).1 = !![1, b; 0, 1] := rfl
@[simp] theorem wy_val : (wy R).1 = !![0, 1; 1, 0] := rfl

end Matrices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def twoCols {n r : ℕ} (h1 : 1 < r) (C : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin 2) E :=
  C.submatrix id (Fin.castLE h1)

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def IsBlockEmb (X Y : Matrix (Fin n) (Fin r) E) (h1 : 1 < r) (j : GL (Fin 2) (AF F ⊗[F] E) →* GAd σ J) : Prop :=
  Continuous j ∧ ∀ h : GL (Fin 2) (AF F ⊗[F] E),
    (matHom _ σ J (j h)).1 * adMat F (twoCols h1 X) = adMat F (twoCols h1 X) * h.1 ∧
    (matHom _ σ J (j h)).1 * adMat F (twoCols h1 Y) = adMat F (twoCols h1 Y) * cT (sigR (AF F) σ) (h⁻¹).1 ∧
    ∀ z ∈ colPerp σ J X {i | i.val < 2} ⊓ colPerp σ J Y {i | i.val < 2}, (matHom _ σ J (j h)).1 *ᵥ z = z

def singleNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* FiniteAdeleRing (𝓞 E) E where
  toFun := singleFin w
  map_mul' := singleFin_mul w
  map_zero' := map_zero _
  map_add' := map_add _

variable (F) in

def locNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* AF F ⊗[F] E :=
  (GlobalTheory.LFun.extZero F E).comp (((GlobalTheory.LFun.finAdEquiv F E).symm : _ →+* _).toNonUnitalRingHom.comp (singleNU w))

variable (F) in

def gl2_local_to_adelic_embedding (w : HeightOneSpectrum (𝓞 E)) : GL (Fin 2) (w.adicCompletion E) →* GL (Fin 2) (AF F ⊗[F] E) :=
  PI.CuspInfChar.emb (locNU F w)

def qChr (χ : (AF F ⊗[F] E)ˣ →* Circle) (z : ℝ) (t : (AF F ⊗[F] E)ˣ) : ℂ :=
  (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

end GlobalTheory.GLTwoHecke

end
