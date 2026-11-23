import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsomTransport

section Ring

variable {A : Type} [CommRing A] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def conjGL (φ : Matrix m n A) (ψ : Matrix n m A) (h1 : φ * ψ = 1) (h2 : ψ * φ = 1) (g : GL n A) : GL m A where
  val := φ * g.1 * ψ
  inv := φ * (g⁻¹).1 * ψ
  val_inv := by
    rw [Matrix.mul_assoc (φ * g.1), ← Matrix.mul_assoc ψ, ← Matrix.mul_assoc ψ, h2, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc φ, Units.mul_inv, Matrix.mul_one, h1]
  inv_val := by
    rw [Matrix.mul_assoc (φ * (g⁻¹).1), ← Matrix.mul_assoc ψ, ← Matrix.mul_assoc ψ, h2, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc φ, Units.inv_mul, Matrix.mul_one, h1]

omit [DecidableEq n] in
theorem conj_unitary (σ : A →+* A) (φ : Matrix m n A) (ψ : Matrix n m A) (h1 : φ * ψ = 1)
    (J : Matrix n n A) (J' : Matrix m m A) (hJ : Formalism.UG.cT σ φ * J' * φ = J) (g : Matrix n n A)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT σ (φ * g * ψ) * J' * (φ * g * ψ) = J' := by
  have e1 : Formalism.UG.cT σ (φ * g * ψ) * J' * (φ * g * ψ) =
      Formalism.UG.cT σ ψ * (Formalism.UG.cT σ g * (Formalism.UG.cT σ φ * J' * φ) * g) * ψ := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  have e2 : Formalism.UG.cT σ (φ * ψ) * J' * (φ * ψ) =
      Formalism.UG.cT σ ψ * (Formalism.UG.cT σ φ * J' * φ) * ψ := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg, ← hJ, ← e2, h1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

end Ring

theorem stab_iff_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  constructor
  · intro hs x
    have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
      funext fun i => evF_sgT_ne hw _
    have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
    have := hs fun i => sgT E v (x i)
    rw [mem_lamHat_iff, mem_lamHat_iff] at this
    simp only [hev] at this
    constructor
    · intro h0
      have h1 := this.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [hxv]; exact h0
        · rw [hx w hw]; exact zero_mem _) v
      rwa [hxv] at h1
    · intro h0
      have h1 := this.2 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [hxv]; exact h0
        · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
      rwa [hxv] at h1
  · intro hs y
    rw [mem_lamHat_iff, mem_lamHat_iff]
    refine forall_congr' fun w => ?_
    rw [hev]
    by_cases hw : w = v
    · subst hw; exact hs _
    · rw [hg w hw, Units.val_one, Matrix.one_mulVec]

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V V' : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (f : AF F ⊗[F] E) (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv F v ⊗[F] E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)), IsIdemOf E v f → φ * ψ = 1 → ψ * φ = 1 → (∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V' v) → (Formalism.UG.cT (sigR (Fv F v) hc.sig) φ * JR (Fv F v) V'.gram : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)) * φ = JR (Fv F v) V.gram → ∀ g, Supp hc V f g → ∃ g', Supp hc V' f g' ∧ (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ ∧ (Stab hc V' g' ↔ Stab hc V g) := by
  intro F E _ _ _ _ _ _ hc V V' v f φ ψ hf h1 h2 hL hJ g hg
  have hu : conjGL φ ψ h1 h2 (locMat hc V v g) ∈ HR (Fv F v) hc.sig V'.gram :=
    conj_unitary _ φ ψ h1 _ _ hJ _ (locMat_mem hc V v g)
  obtain ⟨g', hg', e⟩ := (GlobalTheory.SuppLocal.supp_local F E hc V' v f hf).2.2 _ hu
  have e' : (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ := by rw [e]; rfl
  refine ⟨g', hg', e', ?_⟩
  rw [stab_iff_loc hc V' v g' ((GlobalTheory.SuppLocal.supp_iff hc V' hf g').1 hg').2,
    stab_iff_loc hc V v g ((GlobalTheory.SuppLocal.supp_iff hc V hf g).1 hg).2, e']
  constructor
  · intro hs x
    have := hs (φ.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mulVec_mulVec] at this
    rw [hL, hL ((locMat hc V v g).1.mulVec x)]
    exact this
  · intro hs y
    have := hs (ψ.mulVec y)
    rw [hL, hL ((locMat hc V v g).1.mulVec _), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    exact this

end GlobalTheory.IsomTransport
