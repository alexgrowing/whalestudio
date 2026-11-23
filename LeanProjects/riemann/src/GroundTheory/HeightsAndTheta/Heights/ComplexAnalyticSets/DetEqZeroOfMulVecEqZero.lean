import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

noncomputable section

def analyticAtSubring {σ : Type} [Fintype σ] (p : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g p}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem mem_analyticAtSubring {σ : Type} [Fintype σ] {p : σ → ℂ} {g : (σ → ℂ) → ℂ} :
    g ∈ analyticAtSubring p ↔ AnalyticAt ℂ g p :=
  Iff.rfl

def analyticAtComp {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    analyticAtSubring (L x) →+* analyticAtSubring x where
  toFun g := ⟨fun z => (g : (τ → ℂ) → ℂ) (L z), AnalyticAt.comp g.2 (L.analyticAt x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem analyticAtComp_apply {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (g : analyticAtSubring (L x)) (z : σ → ℂ) :
    (analyticAtComp x L g : (σ → ℂ) → ℂ) z = (g : (τ → ℂ) → ℂ) (L z) :=
  rfl

def analyticAtEval {σ : Type} [Fintype σ] (p y : σ → ℂ) : analyticAtSubring p →+* ℂ :=
  (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) y).comp (analyticAtSubring p).subtype

@[simp] theorem analyticAtEval_apply {σ : Type} [Fintype σ] (p y : σ → ℂ) (g : analyticAtSubring p) :
    analyticAtEval p y g = (g : (σ → ℂ) → ℂ) y :=
  rfl

def analyticAtGerm {σ : Type} [Fintype σ] (p : σ → ℂ) : analyticAtSubring p →+* holGerms p :=
  ((Germ.coeRingHom (𝓝 p)).comp (analyticAtSubring p).subtype).codRestrict (holGerms p)
    fun g => ⟨g, g.2, rfl⟩

theorem analyticAtGerm_eq_iff {σ : Type} [Fintype σ] {p : σ → ℂ} (a b : analyticAtSubring p) :
    analyticAtGerm p a = analyticAtGerm p b ↔ (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 p] b := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem analyticAtGerm_surjective {σ : Type} [Fintype σ] (p : σ → ℂ) :
    Function.Surjective (analyticAtGerm p) := by
  rintro ⟨φ, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem det_eq_zero_of_mulVec_eq_zero {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by
  have he : (A.adjugate * A) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at he
  calc A.det = A.det * ∑ m, β m * e m := by rw [h1, mul_one]
    _ = ∑ m, β m * (A.det * e m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by
      have := congrFun he m
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, mul_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
