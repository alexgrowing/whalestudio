import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FrobeniusTwistEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BddAboveSubDegsOfJointlyMono

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen

namespace GlobalTheory.CurveSemiAbelianConjecture

def CurveData {T : Type} [Fintype T] {N : ℕ} (q : ℕ) [Fact q.Prime] (j : ℕ) (r : T → Fin N → ℝ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k q)
    (C : Scheme.{0}) (_ : Algebra k Γ(C, ⊤)) (_ : IsIntegral C), IsSmoothProjCurve k C ∧
  ∃ (ι : Type) (_ : Fintype ι) (φ : Equiv.Perm ι) (c : ι → ι) (L H : ι → C.Modules) (rL rH : ι → ℕ)
    (M HH : C.Modules) (g : ℕ) (te : T → ι),
    Function.Involutive c ∧ (∀ σ, IsVB (L σ) (rL σ)) ∧ (∀ σ, IsVB (H σ) (rH σ)) ∧
    (∀ σ, IsExtension (dual (L (c σ))) (H σ) (L σ)) ∧
    (∀ σ, IsExtension (frobTwist q k (L σ)) (H (φ σ)) (frobTwist q k (dual (L (c σ))))) ∧
    IsVB M g ∧ IsVB HH (2 * g) ∧ IsExtension (dual M) HH M ∧ (∃ v : frobTwist q k M ⟶ HH, Mono v) ∧
    Nonempty (M ≅ ∐ L) ∧ Function.Injective te ∧ (∀ σ, σ ∈ Set.range te ↔ c σ ∉ Set.range te) ∧
    (∀ τ, PowerSumSmul.psum r τ j = (deg k (L (c (te τ))) : ℝ)) ∧
    (∀ τ, PowerSumSmul.psum r τ N = (deg k (L (c (te τ))) : ℝ) - deg k (L (te τ))) ∧
    (∀ τ (m : ℕ), 1 ≤ m → m ≤ j → m < N →
      ∃ (S : C.Modules) (i : S ⟶ M), IsCohSub i ∧ PowerSumSmul.psum r τ m ≤ (deg k S : ℝ)) ∧
    (∀ τ (m : ℕ), j < m → m < N →
      ∃ (S : C.Modules) (i : S ⟶ M), IsCohSub i ∧
        PowerSumSmul.psum r τ m ≤ (deg k (L (c (te τ))) : ℝ) - deg k (L (te τ)) + deg k S)

open GlobalTheory.VB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen in

theorem degData_of_curveData (hS : GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen.SlopeAndEigenDegrees) {T : Type} [Fintype T] {N : ℕ}
    (q : ℕ) [Fact q.Prime] (j : ℕ) (r : T → Fin N → ℝ) (h : CurveData q j r) :
    GlobalTheory.PowerSumSmul.DegData j (q : ℝ) r := by
  classical
  obtain ⟨k, _, _, _, C, _, _, hC, ι, _, φ, c, L, H, rL, rH, M, HH, g, te, hc, hL, hH, hH1, hH2, hM, hHH, hMH, hF,
    ⟨eM⟩, hte, hΨ, h0, hN, hlo, hhi⟩ := h
  haveI : Infinite k := IsAlgClosed.instInfinite
  obtain ⟨P, hP⟩ := (exists_isMaxSubDeg_iff (k := k) (F := M)).2
    (GlobalTheory.VB.bddAbove_subDegs_of_isVB k C hC.toIsProjCurve M g hM)
  have hslope := hS.1 q k C hC M HH g hM hHH hMH hF P hP
  obtain ⟨hdegH, hC1, hsum⟩ := hS.2 q k C hC ι φ c hc L H rL rH hL hH hH1 hH2
  have hΨ' : ∀ σ, σ ∈ Finset.univ.image te ↔ c σ ∉ Finset.univ.image te := by
    intro σ; simpa using hΨ σ
  have h2 := hsum M ⟨eM⟩ (Finset.univ.image te) hΨ'
  rw [Finset.sum_image (fun a _ b _ e => hte e)] at h2

  have hdual : ∀ σ, deg k (dual (L σ)) = -deg k (L σ) := by
    intro σ
    have e := hH1 (c σ)
    rw [hc σ] at e
    obtain ⟨i, p, w, hSE⟩ := e
    have := (hL (c σ)).isFiniteQC
    have := (hH (c σ)).isFiniteQC
    have := (hL σ).dual.isFiniteQC
    have e1 := hC.toIsProjCurve.deg_shortExact hSE
    have e2 := hdegH (c σ)
    have e3 := hC1 σ
    simp only at e1
    omega
  have hM' : ∀ τ m, j < m → m < N → ∃ (S : C.Modules) (i : S ⟶ M), IsCohSub i ∧ PowerSumSmul.psum r τ m ≤ (deg k S : ℝ) := by
    intro τ m h1 h2
    obtain ⟨S, i, hi, hle⟩ := hhi τ m h1 h2
    refine ⟨S, i, hi, ?_⟩
    rw [hC1 (te τ)] at hle
    simpa using hle
  refine ⟨(P : ℝ), ((-deg k M : ℤ) : ℝ), by exact_mod_cast hP.nonneg, ?_, ?_, ?_, ?_⟩
  · have := (Int.cast_le (R := ℝ)).2 hslope
    push_cast at this ⊢
    linarith
  · intro τ m h1 h2
    obtain ⟨S, i, hi, hle⟩ : ∃ (S : C.Modules) (i : S ⟶ M), IsCohSub i ∧ PowerSumSmul.psum r τ m ≤ (deg k S : ℝ) := by
      by_cases hm : m ≤ j
      · exact hlo τ m h1 hm h2
      · exact hM' τ m (by omega) h2
    haveI := hi.mono
    haveI := hi.isFiniteQC
    have := hP.deg_le i
    exact le_trans hle (by exact_mod_cast this)
  · intro τ
    rw [hN τ, hC1 (te τ)]
    ring
  · simp only [h0]
    have h3 : (2 : ℤ) * ∑ τ, (-deg k (L (c (te τ)))) = -deg k M := by
      rw [← h2]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hdual, hC1 (te τ)]
    have h4 := congrArg (Int.cast : ℤ → ℝ) h3
    push_cast at h4 ⊢
    rw [Finset.sum_neg_distrib] at h4
    linarith

end GlobalTheory.CurveSemiAbelianConjecture
