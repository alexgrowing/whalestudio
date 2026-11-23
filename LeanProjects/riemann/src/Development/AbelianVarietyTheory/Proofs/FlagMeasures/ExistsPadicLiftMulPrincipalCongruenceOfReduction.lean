import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LiftRed

theorem liftred_exists : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, Valued.v z < 1 → ‖θ z‖ < 1) → ∀ (A : GL (Fin n) (v.adicCompletion F)) (γ : GL (Fin n) (ZMod g)), (∀ a b, Valued.v ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1) → ∃ k ∈ (GlobalTheory.GLp.red g n).ker, Matrix.GeneralLinearGroup.map θ.toRingHom A = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n k := by
  intro F _ _ v g n _ θ hθ A γ hA

  have hent : ∀ a b, ‖θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b) -
      ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])‖ < 1 := by
    intro a b
    have h := hθ _ (hA a b)
    rwa [map_sub, map_natCast] at h
  have hle : ∀ a b, ‖θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b)‖ ≤ 1 := by
    intro a b
    have h1 : ‖((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])‖ ≤ 1 := by
      exact_mod_cast PadicInt.norm_le_one ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℤ_[g])
    have := IsUltrametricDist.norm_add_le_max
      (θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b) -
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g]))
      ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le (le_of_lt (hent a b)) h1)
  let Mx : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => ⟨θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b), hle a b⟩
  have hred : Mx.map (PadicInt.toZMod (p := g)) = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext a b
    simp only [Matrix.map_apply]
    have hm : Mx a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℤ_[g]) ∈
        RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast]
      exact hent a b
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero] at hm
    exact hm
  have hdet : IsUnit Mx.det := by
    by_contra hnu
    have hm : Mx.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnu
    rw [RingHom.mem_ker, RingHom.map_det,
      show (PadicInt.toZMod (p := g)).mapMatrix Mx = (γ : Matrix (Fin n) (Fin n) (ZMod g)) from hred] at hm
    have hu : IsUnit (γ : Matrix (Fin n) (Fin n) (ZMod g)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    rw [hm] at hu
    exact not_isUnit_zero hu
  let M : GL (Fin n) ℤ_[g] := Matrix.nonsingInvUnit Mx hdet
  have hMred : GlobalTheory.GLp.red g n M = γ := by
    ext a b
    have := congrFun (congrFun hred a) b
    exact this
  have hMinc : GlobalTheory.GLp.inc g n M = Matrix.GeneralLinearGroup.map θ.toRingHom A := by
    ext a b
    rfl
  set N := Function.invFun (GlobalTheory.GLp.red g n) γ with hN
  have hNred : GlobalTheory.GLp.red g n N = γ := Function.invFun_eq ⟨M, hMred⟩
  refine ⟨N⁻¹ * M, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hNred, hMred, inv_mul_cancel]
  · rw [GlobalTheory.GLp.lift, ← hN, ← map_mul, mul_inv_cancel_left, hMinc]

end GlobalTheory.LiftRed
