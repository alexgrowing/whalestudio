import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Eqv Formalism.IndefR
open scoped TensorProduct

namespace Formalism.L2.SG.EvalTIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def uM' (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (v : InfinitePlace D.host.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ := uMat (x.1 v)

def Pi (v : InfinitePlace D.host.F) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (Formalism.IndefR.RationalEmbedding.inst D).P v

theorem P_isUnit_det' (v : InfinitePlace D.host.F) : IsUnit (Pi (D := D) v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)

theorem thetaV_eq_psiT_i (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : (Formalism.IndefR.RationalEmbedding.inst D).φ (Formalism.L2.Host.tauPl D ρ) x = tauE D ρ x := by
      show Formalism.MainNotions.S.embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = _
      rw [Equiv.symm_apply_apply]
      rfl
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem infMat_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig (D.sp.Y 0).gram (thetaC D ρ) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM' x (Formalism.L2.Host.tauPl D ρ) = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (psiT D ρ) *
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT_i ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC_i {M : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : x.1 = 1 ↔ ∀ v, uM' x v = 1 := by
  constructor
  · intro h v
    show uMat (x.1 v) = 1
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ x.1 = 1 := by
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff_i]
  have hc : ∀ ρ, ((matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D)).map (thetaC D ρ) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg_i, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
    have e' : Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM' x (Formalism.L2.Host.tauPl D ρ)
        = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹) * Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC_i
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det' _)]

theorem tauF_eq_i : Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : Lev.finE (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = (x.2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq_i] at hb
  exact hb.symm

theorem iota_symm_mem_GinfC (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) :
    (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GinfC (D.sp.Y 0) ↔ x.2 = 1 := by
  show finHom (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = 1 ↔ _
  rw [Formalism.IndefR.Eqv.finHom_eq_one_iff, finE_brg_i]
  constructor
  · intro e
    exact Subtype.ext e
  · intro e
    rw [e]
    rfl

end Formalism.L2.SG.EvalTIota

end
