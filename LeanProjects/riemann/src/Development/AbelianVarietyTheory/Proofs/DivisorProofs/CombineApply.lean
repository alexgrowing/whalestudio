import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

noncomputable section

namespace GlobalTheory.ThKUTr

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

@[reducible] def starOf {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) :
    StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by simp only [map_mul, mul_comm]
  star_add a b := map_add σ a b

def combine (ι : Type) (n : ℕ) (R : Type) [CommRing R] :
    (ι → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) ((ι → ℂ) × R) where
  toFun p := Matrix.of fun i j => (fun w => p.1 w i j, p.2 i j)
  map_one' := by
    ext i j
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' p q := by
    ext i j
    · simp [Matrix.mul_apply, Finset.sum_apply, Prod.fst_sum]
    · simp [Matrix.mul_apply, Prod.snd_sum]
  map_zero' := by ext i j <;> simp
  map_add' p q := by ext i j <;> simp

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def glueM (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (n : ℕ) :
    (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →+*
      Matrix (Fin n) (Fin n) (AE F E) :=
  (Φ.symm.toRingHom.mapMatrix).comp (combine (InfinitePlace F) n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))

theorem glueM_apply (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) {n : ℕ}
    (p : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (i j : Fin n) : glueM Φ n p i j = Φ.symm (fun w => p.1 w i j, p.2 i j) := rfl

def rawT (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) {n : ℕ}
    (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (H : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :
    (∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) × H →* GL (Fin n) (AE F E) :=
  (Units.map (glueM Φ n).toMonoidHom).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp
    (MonoidHom.prodMap (MulEquiv.piUnits.symm.toMonoidHom.comp (Pi.monoidHom fun v =>
      (MulAut.conj (P v)).toMonoidHom.comp ((Formalism.REAL.UJ (ε v)).subtype.comp (Pi.evalMonoidHom _ v)))) H.subtype))

theorem rawT_val (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) {n : ℕ}
    (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (H : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (x : (∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) × H) :
    ((rawT Φ ε P H x : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) =
      glueM Φ n (fun v => (P v : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat (x.1 v) * ((P v)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ),
        ((x.2 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :=
  rfl

def trHom (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (H : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (h : ∀ x, rawT Φ ε P H x ∈ UG (cA σ) (incM F J)) :
    (∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) × H →* UA σ J :=
  (rawT Φ ε P H).codRestrict _ h

theorem mat_trHom (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (H : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (h : ∀ x, rawT Φ ε P H x ∈ UG (cA σ) (incM F J))
    (x : (∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) × H) :
    mat (trHom σ J Φ ε P H h x) = ((rawT Φ ε P H x : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := rfl

end Glue

end GlobalTheory.ThKUTr
