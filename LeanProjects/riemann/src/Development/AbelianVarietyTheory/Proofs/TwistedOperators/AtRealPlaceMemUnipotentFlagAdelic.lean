import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct

noncomputable section
open Matrix
open Classical

namespace GlobalTheory.FlagRealUnip

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

def single (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) : ℂ →+ AE D :=
  σ.comp (AddMonoidHom.single (fun _ : D.what₂.Tau => ℂ) τ)

theorem single_apply (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (c : ℂ) :
    single σ τ c = σ (Pi.single τ c) := rfl

set_option maxHeartbeats 2000000 in
theorem chart_mul_incA {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (z : D.what₂.Tau → ℂ) (y : D.host.E) :
    σ z * incA D y = σ (fun τ => z τ * tauE D τ y) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, hσ.fin, hσ.fin, zero_mul, sub_zero]
  · have hy : θ τ (infPart D (incA D y)) = tauE D τ y := by
      show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ y)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      exact (hσ.inf τ).1 y
    have e1 := (infPart D).map_sub (σ z * incA D y) (σ fun τ => z τ * tauE D τ y)
    have e2 := (infPart D).map_mul (σ z) (incA D y)
    have e3 := (θ τ).map_sub (infPart D (σ z * incA D y)) (infPart D (σ fun τ => z τ * tauE D τ y))
    have e4 := (θ τ).map_mul (infPart D (σ z)) (infPart D (incA D y))
    rw [e1, e3, e2, e4, hσ.comp, hσ.comp, hy, sub_self]

theorem single_mul_incA {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) (c : ℂ) (y : D.host.E) :
    single σ τ c * incA D y = single σ τ (c * tauE D τ y) := by
  rw [single_apply, single_apply, chart_mul_incA hσ]
  congr 1
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem map_mulVec_single {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) {m k : ℕ} (M : Matrix (Fin m) (Fin k) D.host.E) (c : Fin k → ℂ) :
    (M.map (incA D)) *ᵥ (fun j => single σ τ (c j)) = fun i => single σ τ ((M.map (tauE D τ) *ᵥ c) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, single_mul_incA hσ, mul_comm]

end GlobalTheory.FlagRealUnip

namespace GlobalTheory.FlagRealUnip

variable {D : D7}

theorem subOne_mulVec {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (B : HSp D)
    (τ : D.what₂.Tau) {u : Matrix (Fin B.rank) (Fin B.rank) ℂ} {h : GA D B} (hh : IsAtTau θ B τ u h)
    (x : Fin B.rank → D.host.E) :
    subOne B h *ᵥ ratV x = fun i => single σ τ (((u - 1) *ᵥ fun k => tauE D τ (x k)) i) := by
  funext i
  have hent : ∀ j, subOne B h i j = single σ τ ((u - 1) i j) := fun j => by
    unfold subOne
    rw [Matrix.sub_apply, GlobalTheory.PointAtPlaceHom.entry_eq hσ B τ hh i j, add_sub_cancel_left, Matrix.sub_apply]
    rfl
  simp only [Matrix.mulVec, dotProduct, hent, ratV, single_mul_incA hσ, ← map_sum]

theorem conj_gram (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau) :
    (e.map (tauE D τ))ᴴ * gramAt D B τ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).map (tauE D τ) := by
  rw [Matrix.map_mul]
  congr 1
  ext k i
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
  exact (tauE_sig τ (e i k)).symm

end GlobalTheory.FlagRealUnip

namespace GlobalTheory.FlagRealUnip

theorem atTau_mem_NFlag : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  intro D θ hθ B ρ e τ u hu
  obtain ⟨huU, h1, h2⟩ := hu
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ huU
  refine Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := h1 i
    refine ⟨fun k => single σ τ (a k), fun j hj => by show single σ τ (a j) = 0; rw [ha0 j hj, map_zero], ?_⟩
    rw [subOne_mulVec hσ B τ hs, map_mulVec_single hσ]
    funext k
    exact congrArg (fun v => single σ τ (v k)) ha
  · obtain ⟨a, ha⟩ := h2 (fun k => tauE D τ (x k)) (by
      rw [conj_gram]
      funext k
      have := RingHom.map_mulVec (tauE D τ) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram) x k
      rw [hx] at this
      exact this.symm.trans (map_zero _))
    refine ⟨fun k => single σ τ (a k), ?_⟩
    rw [subOne_mulVec hσ B τ hs, map_mulVec_single hσ]
    funext k
    exact congrArg (fun v => single σ τ (v k)) ha

end GlobalTheory.FlagRealUnip
