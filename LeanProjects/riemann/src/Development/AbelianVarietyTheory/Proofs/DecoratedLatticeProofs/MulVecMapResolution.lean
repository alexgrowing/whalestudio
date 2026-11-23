import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.MulVecTensorResolution

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mulVec_map_tmul {v : HeightOneSpectrum (𝓞 F)} {k l : ℕ} (M : Matrix (Fin k) (Fin l) E)
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : Fin l → E) :
    Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) (fun i => a ⊗ₜ[F] x i) =
      fun j => a ⊗ₜ[F] (Matrix.mulVec M x) j := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    TensorProduct.tmul_sum]

theorem map_mem_latLoc {v : HeightOneSpectrum (𝓞 F)} {k l : ℕ} (M : Matrix (Fin k) (Fin l) E)
    {L₁ : Submodule (𝓞 E) (Fin l → E)} {L₂ : Submodule (𝓞 E) (Fin k → E)}
    (hM : ∀ x ∈ L₁, Matrix.mulVec M x ∈ L₂) {w : Fin l → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (hw : w ∈ GlobalTheory.AdelicU.latLoc F L₁ v) :
    Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) w ∈ GlobalTheory.AdelicU.latLoc F L₂ v := by
  refine GlobalTheory.AdelicU.latLoc_induction
    (p := fun w => Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) w ∈
      GlobalTheory.AdelicU.latLoc F L₂ v) ?_ ?_ ?_ ?_ hw
  · intro a ha x hx
    rw [mulVec_map_tmul]
    exact GlobalTheory.AdelicU.tmul_mem_latLoc ha (hM x hx)
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · intro y z hy hz
    rw [Matrix.mulVec_add]; exact add_mem hy hz
  · intro y hy
    rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_map_resolution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n m t : ℕ}
    {e e' : Matrix (Fin n) (Fin t) R} {i₀ : Matrix (Fin n) (Fin m) R} {qX qY : Matrix (Fin t) (Fin n) R}
    {q0 : Matrix (Fin m) (Fin n) R} (h : e * qX + i₀ * q0 + e' * qY = 1) (y : Fin n → S) :
    y = e.map φ *ᵥ (qX.map φ *ᵥ y) + i₀.map φ *ᵥ (q0.map φ *ᵥ y) + e'.map φ *ᵥ (qY.map φ *ᵥ y) := by
  have h' := congrArg φ.mapMatrix h
  simp only [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul] at h'
  simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  rw [h', Matrix.one_mulVec]

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {n m t : ℕ} {e e' : Matrix (Fin n) (Fin t) E} {i₀ : Matrix (Fin n) (Fin m) E} {qX qY : Matrix (Fin t) (Fin n) E} {q0 : Matrix (Fin m) (Fin n) E}, e * qX + i₀ * q0 + e' * qY = (1 : Matrix (Fin n) (Fin n) E) → qX * e = (1 : Matrix (Fin t) (Fin t) E) → qX * i₀ = (0 : Matrix (Fin t) (Fin m) E) → qX * e' = (0 : Matrix (Fin t) (Fin t) E) → q0 * e = (0 : Matrix (Fin m) (Fin t) E) → q0 * i₀ = (1 : Matrix (Fin m) (Fin m) E) → q0 * e' = (0 : Matrix (Fin m) (Fin t) E) → qY * e = (0 : Matrix (Fin t) (Fin t) E) → qY * i₀ = (0 : Matrix (Fin t) (Fin m) E) → qY * e' = (1 : Matrix (Fin t) (Fin t) E) → ∀ {L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)} {L' : Submodule (NumberField.RingOfIntegers E) (Fin m → E)} {L₁ : Submodule (NumberField.RingOfIntegers E) (Fin t → E)}, (∀ (z : Fin n → E), z ∈ L ↔ Matrix.mulVec qX z ∈ L₁ ∧ Matrix.mulVec q0 z ∈ L' ∧ Matrix.mulVec qY z ∈ L₁) → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (y : Fin n → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E), y ∈ GlobalTheory.AdelicU.latLoc F L v ↔ Matrix.mulVec (Matrix.map qX fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L₁ v ∧ Matrix.mulVec (Matrix.map q0 fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L' v ∧ Matrix.mulVec (Matrix.map qY fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L₁ v := by
  intro F E _ _ _ _ n m t e e' i₀ qX qY q0 hsum hXe hXi hXe' h0e h0i h0e' hYe hYi hYe' L L' L₁ hL v y
  have mX : ∀ x ∈ L, Matrix.mulVec qX x ∈ L₁ := fun x hx => ((hL x).1 hx).1
  have m0 : ∀ x ∈ L, Matrix.mulVec q0 x ∈ L' := fun x hx => ((hL x).1 hx).2.1
  have mY : ∀ x ∈ L, Matrix.mulVec qY x ∈ L₁ := fun x hx => ((hL x).1 hx).2.2
  have me : ∀ x ∈ L₁, Matrix.mulVec e x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXe, Matrix.one_mulVec]; exact hx,
     by rw [Matrix.mulVec_mulVec, h0e, Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, hYe, Matrix.zero_mulVec]; exact zero_mem _⟩
  have mi : ∀ x ∈ L', Matrix.mulVec i₀ x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXi, Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, h0i, Matrix.one_mulVec]; exact hx,
     by rw [Matrix.mulVec_mulVec, hYi, Matrix.zero_mulVec]; exact zero_mem _⟩
  have me' : ∀ x ∈ L₁, Matrix.mulVec e' x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXe', Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, h0e', Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, hYe', Matrix.one_mulVec]; exact hx⟩
  constructor
  · intro hy
    exact ⟨map_mem_latLoc qX mX hy, map_mem_latLoc q0 m0 hy, map_mem_latLoc qY mY hy⟩
  · rintro ⟨h1, h2, h3⟩
    have key : y = Matrix.mulVec (Matrix.map e fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map qX fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) +
        Matrix.mulVec (Matrix.map i₀ fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map q0 fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) +
        Matrix.mulVec (Matrix.map e' fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map qY fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) :=
      mulVec_map_resolution
        (Algebra.TensorProduct.includeRight : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E).toRingHom hsum y
    rw [key]
    exact add_mem (add_mem (map_mem_latLoc e me h1) (map_mem_latLoc i₀ mi h2)) (map_mem_latLoc e' me' h3)

end GlobalTheory.MulVecTensorResolution
