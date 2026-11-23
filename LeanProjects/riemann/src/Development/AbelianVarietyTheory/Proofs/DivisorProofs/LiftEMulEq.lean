import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocCoLocDarboux

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.WeilImpl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftE_mul_eq (v : Pl F) (z : Fv F v ⊗[F] E) (M : AE F E) :
    liftE v z * M = liftE v (z * compFin F E v M) := by
  have h1 : GlobalTheory.LatVac.liftV v 1 • liftE (E := E) v z = liftE v z := by
    rw [GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, GlobalTheory.HoweLocal.LocCoords.compFin_liftE]
  rw [← h1, smul_mul_assoc, GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, map_mul,
    GlobalTheory.HoweLocal.LocCoords.compFin_liftE]

theorem at_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : At (evFin F v) (liftE (E := E) v z) := by
  intro u hu
  have h1 : GlobalTheory.LatVac.liftV v 1 • liftE (E := E) v z = liftE v z := by
    rw [GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, GlobalTheory.HoweLocal.LocCoords.compFin_liftE]
  rw [← h1, smul_smul, mul_comm, GlobalTheory.HoweLocal.LocCoords.liftV_mul, hu, mul_zero, map_zero, zero_smul]

end GlobalTheory.HoweLocal.WeilImpl

namespace GlobalTheory.HoweLocal.WeilImpl

theorem impl_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    ∀ g w, ∀ φ ∈ SB (κ → Fv F v), omL g (co.rho (GlobalTheory.LatVac.psiAt ψ v) w φ) =
      co.rho (GlobalTheory.LatVac.psiAt ψ v) (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ) := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB hstd hW v _hv inst2 eB hcomp omL hL co hco g w φ hφ
  classical
  have hat : ∀ x : Matrix (Fin a) (Fin b) (Fv F v ⊗[F] E), At (evFin F v) (x.map (liftE v)) := by
    intro x u hu; funext i j; exact at_liftE v (x i j) u hu
  have hrho : ∀ (x : Matrix (Fin a) (Fin b) (Fv F v ⊗[F] E)) (φ₀ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (dA.rho ψ (x.map (liftE v))) φ₀ (co.rho (GlobalTheory.LatVac.psiAt ψ v) x φ₀) := by
    intro x φ₀
    have h := GlobalTheory.VacBridge.rho_acts_locCo dA ψ v _ (hat x) φ₀
    rw [← hco x] at h
    convert h using 2
    simp only [Darboux.rho]
    first | rfl | (congr 1; exact Subsingleton.elim _ _) | congr
  have hSB : ∀ x, ∀ φ₀ ∈ SB (κ → Fv F v), co.rho (GlobalTheory.LatVac.psiAt ψ v) x φ₀ ∈ SB (κ → Fv F v) := by
    intro x φ₀ h0
    have := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 v (co.e x) φ₀ h0
    convert this using 2
    simp only [Darboux.rho]
    first | rfl | (congr 1; exact Subsingleton.elim _ _) | congr
  have hpresR : ∀ x, ∀ Φ ∈ schA F κ, dA.rho ψ x Φ ∈ schA F κ := by
    intro x Φ hΦ
    exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hstd κ _ Φ hΦ
  have hm : (((g : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)) : GL (Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b) (Fin b) (Fv F v ⊗[F] E)) = (mat ((eB.symm g : UAtGrp σ B (evFin F v)) : UA σ B.J)).map (compFin F E v) := by
    have := hcomp.1 (eB.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hact : actB (cA σ) (eB.symm g).1 (w.map (liftE v)) = (actB (GlobalTheory.HoweLocal.cv σ v) g w).map (liftE v) := by
    funext i j
    simp only [actB, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, hm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [liftE_mul_eq]; rfl
  have h1 := GlobalTheory.ThK.LocalOps.acts_comp v (hpresR (w.map (liftE v))) (hrho w φ) (hL g _ (hSB w φ hφ)).2
  have h2 := GlobalTheory.ThK.LocalOps.acts_comp v (fun Φ hΦ => hW.pres (eB.symm g).1 Φ hΦ) (hL g φ hφ).2
    (hrho (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ))
  have h2' : Acts (evFin F v) (omB (eB.symm g).1 ∘ dA.rho ψ (w.map (liftE v))) φ
      (co.rho (GlobalTheory.LatVac.psiAt ψ v) (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ)) := by
    intro r hr
    have := h2 r hr
    simp only [Function.comp_apply] at this ⊢
    rw [hW.impl (eB.symm g).1 (w.map (liftE v)) _ hr.2, hact]
    exact this
  exact GlobalTheory.HoweLocal.LocOpsW.acts_uniq v _ hφ h1 h2'

end GlobalTheory.HoweLocal.WeilImpl
