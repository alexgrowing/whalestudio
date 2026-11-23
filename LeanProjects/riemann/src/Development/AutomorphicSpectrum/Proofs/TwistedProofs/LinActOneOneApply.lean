import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist

noncomputable section

open NumberField IsDedekindDomain Matrix
open Formalism.UG (Tj Ov qV IsUnifV Hecke IsBiInv conv dosetInd IsCommensurated GLint)
open GlobalTheory.LFun (KGL heckeVec IsSatVecGL satEig seg)

namespace GlobalTheory.CompanionTheory.Ipf.Val.SphM

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem absV_mul (x y : Cv v) : absV v (x * y) = absV v x * absV v y := by
  simp [absV, map_mul]

theorem absV_nonneg (x : Cv v) : 0 ≤ absV v x := by
  simp [absV]

theorem absV_one : absV v (1 : Cv v) = 1 := by
  simp [absV]

def phi0 (n c : ℕ) : Matrix (Fin n) (Fin c) (Cv v) → ℂ :=
  Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1

theorem linAct_one_one_apply {a b : ℕ} (g : GL (Fin a) (Cv v)) (h : GL (Fin b) (Cv v))
    (Φ : Matrix (Fin b) (Fin a) (Cv v) → ℂ) (y : Matrix (Fin b) (Fin a) (Cv v)) :
    linAct v 1 1 g h Φ y =
      ((absV v g.1.det ^ ((b : ℝ) / 2) * absV v h.1.det ^ (-(a : ℝ) / 2) : ℝ) : ℂ) * Φ ((h⁻¹).1 * y * g.1) := by
  simp [linAct]

def omega (n c : ℕ) : Representation ℂ (GL (Fin c) (Cv v) × GL (Fin n) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) where
  toFun p :=
    { toFun := linAct v 1 1 p.1 p.2
      map_add' := fun Φ Ψ => by
        funext y
        simp only [linAct_one_one_apply, Pi.add_apply, mul_add]
      map_smul' := fun z Φ => by
        funext y
        simp only [linAct_one_one_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    ext Φ y
    simp [linAct_one_one_apply, absV_one]
  map_mul' := fun p p' => by
    ext Φ y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, linAct_one_one_apply, Prod.fst_mul, Prod.snd_mul,
      Units.val_mul, Matrix.det_mul, absV_mul, _root_.mul_inv_rev]
    rw [Real.mul_rpow (absV_nonneg v _) (absV_nonneg v _), Real.mul_rpow (absV_nonneg v _) (absV_nonneg v _)]
    have e : (p'.2⁻¹).1 * (p.2⁻¹).1 * y * (p.1.1 * p'.1.1) =
        (p'.2⁻¹).1 * ((p.2⁻¹).1 * y * p.1.1) * p'.1.1 := by
      simp only [Matrix.mul_assoc]
    rw [e]
    push_cast
    ring

end GlobalTheory.CompanionTheory.Ipf.Val.SphM

end
