import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def uM (x : (UI.instV fr).GA) (v : InfinitePlace D.host.F) : Matrix (Fin V.rank) (Fin V.rank) ℂ := uMat (x.1 v)

theorem thetaV_eq_psiT (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : tauE D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = tauE D ρ x := by
      rw [Equiv.symm_apply_apply]
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem P_isUnit_det (v : InfinitePlace D.host.F) : IsUnit (fr.P v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (fr.unit v)

theorem infMat_brg (x : (UI.instV fr).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D ρ) (UI.brg fr x) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM fr x (Formalism.L2.Host.tauPl D ρ) = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D V (UI.brg fr x)).map (psiT D ρ) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((UI.brg_isBridge fr) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT fr ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC {M : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff (x : (UI.instV fr).GA) : x.1 = 1 ↔ ∀ v, uM fr x v = 1 := by
  unfold uM uMat
  constructor
  · rintro h v
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC (x : (UI.instV fr).GA) : UI.brg fr x ∈ GfC V ↔ x.1 = 1 := by
  have key : UI.brg fr x ∈ GfC V ↔ (matA D V (UI.brg fr x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff]
  have hc : ∀ ρ, ((matA D V (UI.brg fr x)).map (infPart D)).map (thetaC D ρ) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
    have e' : fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM fr x (Formalism.L2.Host.tauPl D ρ)
        = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ * (fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) *
          (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det fr _)]

theorem tauF_eq : Formalism.L2.SG.AdBridge.tauF (UI.instV fr) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (UI.instV fr) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg (x : (UI.instV fr).GA) : Lev.finE V (UI.brg fr x) = (x.2.1 : GL (Fin V.rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((UI.brg_isBridge fr) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq] at hb
  exact hb.symm

end Formalism.IndefR.Eqv

end
