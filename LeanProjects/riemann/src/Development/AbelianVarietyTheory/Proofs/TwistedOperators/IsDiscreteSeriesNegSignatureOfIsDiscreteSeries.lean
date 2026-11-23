import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.DSFlip

variable {n : ℕ} (ε : Fin n → Bool)

theorem jm_not : Formalism.REAL.Jm (fun a => !ε a) = -Formalism.REAL.Jm ε := by
  ext a b
  by_cases hab : a = b
  · subst hab; cases h : ε a <;> simp [Formalism.REAL.Jm, h]
  · simp [Formalism.REAL.Jm, hab]

theorem inUJ_not (g : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.inUJ (fun a => !ε a) g ↔ Formalism.REAL.inUJ ε g := by
  unfold Formalism.REAL.inUJ
  rw [jm_not, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uJset_not : Formalism.MainNotions.S.UJset (fun a => !ε a) = Formalism.MainNotions.S.UJset ε :=
  Set.ext fun g => inUJ_not ε g

theorem kset_not : Formalism.REAL.Kset (fun a => !ε a) = Formalism.REAL.Kset ε := by
  ext g
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq, jm_not, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_not : Formalism.REAL.rhoC (fun a => !ε a) = Formalism.REAL.rhoC ε := by
  funext a; simp [Formalism.REAL.rhoC]

theorem rhoN_not : Formalism.REAL.rhoN (fun a => !ε a) = Formalism.REAL.rhoN ε := by
  funext a; simp [Formalism.REAL.rhoN]

theorem lowK_not (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK (fun a => !ε a) lam = Formalism.QuantumDeterminants.lowK ε lam := by
  simp only [Formalism.QuantumDeterminants.lowK, rhoC_not, rhoN_not]

theorem vNormSq_not (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq (fun a => !ε a) μ = Formalism.MainNotions.S.vNormSq ε μ := by
  simp only [Formalism.MainNotions.S.vNormSq, rhoC_not]

theorem cDom_not (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom (fun a => !ε a) μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp [Formalism.MainNotions.S.CDom]

theorem isKTypeOf_not {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf (fun a => !ε a) σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, Formalism.MainNotions.S.IsKStableOn, kset_not, cDom_not]

def flipU : Formalism.REAL.UJ (fun a => !ε a) ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (inUJ_not ε _).1 g.2⟩
  invFun g := ⟨g.1, (inUJ_not ε _).2 g.2⟩
  left_inv g := rfl
  right_inv g := rfl
  map_mul' g h := rfl

theorem flipU_cont : Continuous (flipU ε) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem flipU_symm_cont : Continuous (flipU ε).symm :=
  Continuous.subtype_mk continuous_subtype_val _

theorem memLp_flip {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU ε) 2 (Formalism.REAL.muG (fun a => !ε a)) := by
  haveI : ((Formalism.REAL.muG (fun a => !ε a)).map (flipU ε)).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ (flipU ε) (flipU_cont ε) (flipU_symm_cont ε)
  refine MemLp.comp_of_map ?_ (flipU_cont ε).measurable.aemeasurable
  rw [Measure.isMulLeftInvariant_eq_smul ((Formalism.REAL.muG (fun a => !ε a)).map (flipU ε)) (Formalism.REAL.muG ε)]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem flipU_apply (g : Formalism.REAL.UJ (fun a => !ε a)) :
    ((flipU ε g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) := rfl

theorem coefOn_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H) :
    Formalism.MainNotions.S.coefOn (ε := fun a => !ε a) σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU ε := by
  funext g
  simp only [Function.comp_apply, Formalism.MainNotions.S.coefOn, Formalism.MainNotions.S.umat, flipU_apply]

end GlobalTheory.DSFlip

theorem GlobalTheory.PairLift.isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ ⟨hc, hn, hu, hi, hsq, ⟨S, hS⟩, hmin⟩
  refine ⟨hc, hn, ?_, ?_, ?_, ⟨S, ?_⟩, ?_⟩
  · rw [GlobalTheory.DSFlip.uJset_not]; exact hu
  · rw [GlobalTheory.DSFlip.uJset_not]; exact hi
  · intro v w
    rw [GlobalTheory.DSFlip.coefOn_flip]
    exact GlobalTheory.DSFlip.memLp_flip ε (hsq v w)
  · rw [GlobalTheory.DSFlip.isKTypeOf_not, GlobalTheory.DSFlip.lowK_not]; exact hS
  · intro μ S' hS'
    rw [GlobalTheory.DSFlip.lowK_not, GlobalTheory.DSFlip.vNormSq_not, GlobalTheory.DSFlip.vNormSq_not]
    exact hmin μ S' ((GlobalTheory.DSFlip.isKTypeOf_not ε σ μ S').1 hS')

end
