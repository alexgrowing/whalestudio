import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TwistRatBij

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem inclR_eq (e : E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e = (Algebra.TensorProduct.lid F E).symm e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.lid_symm_apply]

theorem inclR_lid (x : F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (Algebra.TensorProduct.lid F E x) = x := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).symm_apply_apply x

theorem lid_inclR (e : E) :
    Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e) = e := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).apply_symm_apply e

theorem lid_sigR (σ : E →ₐ[F] E) (x : F ⊗[F] E) :
    σ (Algebra.TensorProduct.lid F E x) =
      Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

abbrev matOf {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR R σ J from x) : GL (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E))

theorem diagH_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Formalism.UG.UJ (σ : E →+* E) J) (i j : Fin n) :
    matOf (diagH σ J F g) i j =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := rfl

theorem diagH_bijective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), Function.Bijective (diagH σ J F) := by
  intro F E _ _ _ σ n J
  constructor
  · intro g h hgh
    apply Subtype.ext; apply Units.ext; ext i j
    have h1 := congrArg (fun x => matOf x i j) hgh
    simp only [diagH_val] at h1
    have h2 := congrArg (Algebra.TensorProduct.lid F E) h1
    rwa [lid_inclR, lid_inclR] at h2
  · intro h
    let h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR F σ J := h
    let L : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
    let g : GL (Fin n) E := Formalism.UG.bc L h'.1
    have hL : ∀ x, (σ : E →+* E) (L x) = L (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := fun x => lid_sigR σ x
    have hmem : g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      have hh : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) ((h'.1 : GL (Fin n) (F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J *
          ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J := h'.2
      have hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J).map L = J := by
        ext r s; exact lid_inclR (J r s)
      show Formalism.UG.cT (σ : E →+* E) ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) * J *
        ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) = J
      generalize ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) = M at hh ⊢
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) (σ : E →+* E) L hL, ← hJ,
        ← Matrix.map_mul, ← Matrix.map_mul, hh]
    refine ⟨⟨g, hmem⟩, ?_⟩
    apply Subtype.ext; apply Units.ext; ext i j
    exact inclR_lid _

end GlobalTheory.TwistRatBij
