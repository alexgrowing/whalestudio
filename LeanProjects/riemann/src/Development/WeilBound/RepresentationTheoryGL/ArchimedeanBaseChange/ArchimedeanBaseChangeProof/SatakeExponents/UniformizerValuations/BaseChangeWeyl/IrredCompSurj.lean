import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.BcWeyl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemB

section Conj

variable {L : Type} [Field L] (s : L →+* L) {n : ℕ}

theorem conj_mem_GU (P Q X : Matrix (Fin n) (Fin n) L) (hPQ : P * Q = 1) (hX : cT s X * 1 * X = 1) :
    cT s (Q * X * P) * (cT s P * P) * (Q * X * P) = cT s P * P := by
  have h1 : cT s Q * cT s P = 1 := by rw [← cT_mul, hPQ, cT_one]
  rw [Matrix.mul_one] at hX
  rw [cT_mul, cT_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT s Q) (cT s P), h1, Matrix.one_mul, ← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul,
    ← Matrix.mul_assoc (cT s X) X, hX, Matrix.one_mul]

theorem conj_mem_UJ (P Q Y : Matrix (Fin n) (Fin n) L) (hPQ : P * Q = 1)
    (hY : cT s Y * (cT s P * P) * Y = cT s P * P) :
    cT s (P * Y * Q) * 1 * (P * Y * Q) = 1 := by
  have h1 : cT s Q * cT s P = 1 := by rw [← cT_mul, hPQ, cT_one]
  rw [Matrix.mul_one, cT_mul, cT_mul]
  calc cT s Q * (cT s Y * cT s P) * (P * Y * Q) = cT s Q * (cT s Y * (cT s P * P) * Y) * Q := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hY]
        simp only [Matrix.mul_assoc]
        rw [hPQ, Matrix.mul_one, h1]

def conjU (b : GL (Fin n) L) (hb : cT s b.val * b.val = antiJ L n) (H : Subgroup (GL (Fin n) L))
    (hH : ∀ g, g ∈ H ↔ g ∈ UJ s (1 : Matrix (Fin n) (Fin n) L)) : H ≃* GU s n where
  toFun x := ⟨b⁻¹ * x.1 * b, by
    have hx : cT s (x.1 : Matrix (Fin n) (Fin n) L) * 1 * x.1 = 1 := (hH _).1 x.2
    change cT s _ * antiJ L n * _ = antiJ L n
    rw [← hb]
    simp only [Units.val_mul]
    exact conj_mem_GU s _ _ _ (Units.mul_inv b) hx⟩
  invFun y := ⟨b * y.1 * b⁻¹, by
    refine (hH _).2 ?_
    have hy : cT s (y.1 : Matrix (Fin n) (Fin n) L) * antiJ L n * y.1 = antiJ L n := y.2
    rw [← hb] at hy
    change cT s _ * 1 * _ = 1
    simp only [Units.val_mul]
    exact conj_mem_UJ s _ _ _ (Units.mul_inv b) hy⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjU_val (b : GL (Fin n) L) (hb : cT s b.val * b.val = antiJ L n) (H : Subgroup (GL (Fin n) L))
    (hH : ∀ g, g ∈ H ↔ g ∈ UJ s (1 : Matrix (Fin n) (Fin n) L)) (x : H) :
    ((conjU s b hb H hH x : GU s n) : GL (Fin n) L) = b⁻¹ * x.1 * b := rfl

end Conj

theorem irred_comp_surj {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

end PositivityTheory.Rg.BcB.F.LemB

end
