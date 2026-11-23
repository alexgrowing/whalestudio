import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime]

def emb (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp (σ.toAlgHom.comp L.1.val)

def phiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (emb P σ L) (AlgHom.id ℚ_[l] P.R.BdR) (fun _ _ => Commute.all _ _)

def PhiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    Fin a → P.R.BdR :=
  fun i => phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) x)

variable (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ)

theorem emb_apply (c : ↥L.1) : emb P σ L c = algebraMap (Om l) P.R.BdR (σ (c : Om l)) := rfl

theorem phiS_tmul (c : ↥L.1) (b : P.R.BdR) :
    phiS P σ L (c ⊗ₜ b) = algebraMap (Om l) P.R.BdR (σ (c : Om l)) * b := by
  simp [phiS, emb]

theorem PhiS_tmul (v : Fin a → ↥L.1) (b : P.R.BdR) :
    PhiS P σ L a (v ⊗ₜ b) = fun i => algebraMap (Om l) P.R.BdR (σ (v i : Om l)) * b := by
  funext i
  simp [PhiS, phiS_tmul]

theorem PhiS_add (x y : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (x + y) = PhiS P σ L a x + PhiS P σ L a y := by
  funext i
  simp [PhiS]

theorem PhiS_zero : PhiS P σ L a 0 = 0 := by
  funext i
  simp [PhiS]

theorem PhiS_sum {ι : Type} (s : Finset ι) (x : ι → (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (∑ i ∈ s, x i) = ∑ i ∈ s, PhiS P σ L a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PhiS_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, PhiS_add, ih]

theorem PhiS_sm (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) r x) = fun i => phiS P σ L r * PhiS P σ L a x i := by
  funext i
  simp only [PhiS]
  rw [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self, map_mul]

theorem PhiS_mulR (b : P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) b x) = fun i => b * PhiS P σ L a x i := by
  rw [← GlobalTheory.DRFil.sm_one_tmul, PhiS_sm, phiS_tmul]
  funext i
  simp

end GlobalTheory.HodgeAt
