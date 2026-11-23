import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7}

def tens {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ := fun t => Φ (t - b • t) * Ψ (b • t)

theorem tens_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) (t : WO S T) :
    tens b Φ Ψ t = Φ (t - b • t) * Ψ (b • t) := rfl

def tensL {S T : HSp D} (b : AE D) (Ψ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := tens b Φ Ψ
  map_add' Φ Φ' := by funext t; simp only [tens, Pi.add_apply, add_mul]
  map_smul' c Φ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

def tensR {S T : HSp D} (b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := tens b Φ Ψ
  map_add' Ψ Ψ' := by funext t; simp only [tens, Pi.add_apply, mul_add]
  map_smul' c Ψ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensL_apply {S T : HSp D} (b : AE D) (Ψ Φ : WO S T → ℂ) : tensL b Ψ Φ = tens b Φ Ψ := rfl

theorem tensR_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : tensR b Φ Ψ = tens b Φ Ψ := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def eSum (p : ι → SplitPt D k) (J : List ι) : AE D := (J.map fun i => (p i).e).sum

theorem eSum_cons (p : ι → SplitPt D k) (i : ι) (J : List ι) : eSum p (i :: J) = (p i).e + eSum p J := by
  simp [eSum]

open Classical in

def datJ (p : ι → SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}
    (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (J : List ι) (t : WO S T) : ℂ :=
  if IsHalf (eSum p J) t then (J.map fun i => Ψ i (rd (α i) (β i) t)).prod else 0

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  rw [← p.sec_one, p.pr_sec]

theorem pr_of_mul_eq_zero (p : SplitPt D k) {a : AE D} (h : p.e * a = 0) : p.pr a = 0 := by
  have := congrArg p.pr h
  rwa [map_mul, pr_e, one_mul, map_zero] at this

theorem mul_eSum (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, a * (p j).e = 0) : a * eSum p J = 0 := by
  induction J with
  | nil => simp [eSum]
  | cons j J ih =>
    rw [eSum_cons, mul_add, h j (List.mem_cons_self), ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'), add_zero]

theorem eSum_mul (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, (p j).e * a = 0) : eSum p J * a = 0 := by
  rw [mul_comm]; exact mul_eSum p a J fun j hj => by rw [mul_comm]; exact h j hj

theorem eSum_idem (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup) :
    eSum p J * eSum p J = eSum p J := by
  induction J with
  | nil => simp [eSum]
  | cons i J ih =>
    rw [List.nodup_cons] at hJ
    have h1 : (p i).e * eSum p J = 0 := mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    have h2 : eSum p J * (p i).e = 0 := by rw [mul_comm, h1]
    rw [eSum_cons, add_mul, mul_add, mul_add, (p i).split.1, h1, h2, ih hJ.2, add_zero, zero_add]

theorem pr_eSum (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup)
    (i : ι) (hi : i ∈ J) : (p i).pr (eSum p J) = 1 := by
  induction J with
  | nil => simp at hi
  | cons j J ih =>
    rw [List.nodup_cons] at hJ
    rw [eSum_cons, map_add]
    by_cases hij : i = j
    · subst hij
      rw [pr_e, pr_of_mul_eq_zero (p i) (mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)), add_zero]
    · rw [pr_of_mul_eq_zero (p i) (horth i j hij), zero_add, ih hJ.2 ((List.mem_cons.1 hi).resolve_left hij)]

end GlobalTheory.FinPl.PutIn

end
