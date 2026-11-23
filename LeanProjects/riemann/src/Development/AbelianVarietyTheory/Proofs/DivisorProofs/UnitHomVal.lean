import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.IndLineGL GlobalTheory.EmbChart
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCoord

abbrev Ix (m : ℕ) : Type := Σ i : Fin 3, Fin (blk3 m i)

def eIx (m n : ℕ) (h : m + 2 = n) : Ix m ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr (by simp [Fin.sum_univ_three, blk3]; omega))

def gamS {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R) : Matrix (Ix m) (Ix m) R
  | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨0, _⟩ => -1
  | ⟨1, i⟩, ⟨1, j⟩ => K i j
  | _, _ => 0

def gam {R : Type} [Ring R] {m n : ℕ} (e : Ix m ≃ Fin n) (K : Matrix (Fin m) (Fin m) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.reindex e e (gamS K)

def colS {E : Type} {n m : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin m) E) : Ix m → Fin n → E
  | ⟨0, _⟩ => x
  | ⟨1, j⟩ => fun r => ι r j
  | ⟨2, _⟩ => y

def basMat {E : Type} [Field E] {n m : ℕ} (H : Plane E n m) (e : Ix m ≃ Fin n) : Matrix (Fin n) (Fin n) E :=
  fun r k => colS H.x H.y H.ι (e.symm k) r

open Classical in

def basGL {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {v : Pl F} (t : E →ₐ[F] Fv F v) {n m : ℕ}
    (H : Plane E n m) (e : Ix m ≃ Fin n) : GL (Fin n) (Fv F v) :=
  if h : IsUnit ((basMat H e).map t).det then Matrix.nonsingInvUnit _ h else 1

def gT {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) : GL (Fin m) R :=
  ⟨(g : Matrix (Fin m) (Fin m) R)ᵀ, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩

theorem gT_val {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) :
    (gT g : Matrix (Fin m) (Fin m) R) = (g : Matrix (Fin m) (Fin m) R)ᵀ := rfl

def levDual {R : Type} [CommRing R] {m : ℕ} (K : GL (Fin m) R) (l : Levi R (fun i : Fin 3 => Fin (blk3 m i))) :
    Levi R (fun i : Fin 3 => Fin (blk3 m i))
  | ⟨0, _⟩ => (l 2)⁻¹
  | ⟨1, _⟩ => (K⁻¹ * gT (show GL (Fin m) R from (l 1)⁻¹) * K : GL (Fin m) R)
  | ⟨2, _⟩ => (l 0)⁻¹

section Idele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : Pl F}

def ptA (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) : AE F E :=
  1 + tensAt E v ((splitAlgEquiv hcm t).symm (p, q) - 1)

theorem ptA_mul (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q p' q' : Fv F v) :
    ptA hcm t p q * ptA hcm t p' q' = ptA hcm t (p * p') (q * q') := by
  set Y := (splitAlgEquiv hcm t).symm (p, q)
  set Z := (splitAlgEquiv hcm t).symm (p', q')
  have hYZ : (splitAlgEquiv hcm t).symm (p * p', q * q') = Y * Z := by
    rw [← map_mul]; rfl
  have e1 : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1) := by ring
  have e2 : tensAt E v (Y - 1) * tensAt E v (Z - 1) = tensAt E v ((Y - 1) * (Z - 1)) := by
    rw [tensAt_mul_right, compFin_tensAt]
  simp only [ptA, hYZ, e1, map_add, ← e2]
  ring

theorem ptA_one (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : ptA hcm t 1 1 = 1 := by
  have : (splitAlgEquiv hcm t).symm ((1 : Fv F v), (1 : Fv F v)) = 1 := by
    rw [← map_one (splitAlgEquiv hcm t).symm]; rfl
  rw [ptA, this, sub_self, map_zero, add_zero]

def unitHom (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : (Fv F v)ˣ × (Fv F v)ˣ →* (AE F E)ˣ where
  toFun x := ⟨ptA hcm t x.1 x.2, ptA hcm t (x.1⁻¹ : (Fv F v)ˣ) (x.2⁻¹ : (Fv F v)ˣ),
    by rw [ptA_mul, Units.mul_inv, Units.mul_inv, ptA_one],
    by rw [ptA_mul, Units.inv_mul, Units.inv_mul, ptA_one]⟩
  map_one' := Units.ext (by simp only [Prod.fst_one, Prod.snd_one, Units.val_one]; exact ptA_one hcm t)
  map_mul' x y := Units.ext (by simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul]; exact (ptA_mul hcm t _ _ _ _).symm)

theorem unitHom_val (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ × (Fv F v)ˣ) :
    (unitHom hcm t x : AE F E) = ptA hcm t x.1 x.2 := rfl

def chrAbs (χ : Chr F E) (z : ℝ) : (AE F E)ˣ →* ℂˣ where
  toFun s := Units.mk0 ((χ s : ℂ) * (((absE F E s : ℝ) ^ z : ℝ) : ℂ)) (by
    refine mul_ne_zero (Circle.coe_ne_zero _) ?_
    have h : absE F E s ≠ 0 := fun h0 => by
      have := congrArg (absE F E) (mul_inv_cancel s)
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) z).ne')
  map_one' := Units.ext (by simp)
  map_mul' s s' := Units.ext (by
    simp only [map_mul, Units.val_mul, Units.val_mk0, Circle.coe_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    push_cast; ring)

def xiOne (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (χ : Chr F E) (z : ℝ) : (Fv F v)ˣ →* ℂˣ :=
  (chrAbs χ z).comp ((unitHom hcm t).comp (MonoidHom.inl _ _))

def xiTwo (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (χ : Chr F E) (z : ℝ) : (Fv F v)ˣ →* ℂˣ :=
  (chrAbs χ z).comp ((unitHom hcm t).comp ((MonoidHom.inr _ _).comp (invMonoidHom : (Fv F v)ˣ →* (Fv F v)ˣ)))

end Idele

end GlobalTheory.SplitCoord
