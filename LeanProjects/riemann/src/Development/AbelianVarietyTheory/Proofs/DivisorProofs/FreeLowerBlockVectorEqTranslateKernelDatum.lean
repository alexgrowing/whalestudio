import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRankStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.FreeBlockMove

theorem vecFree_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ' = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i ξ χ ξR Q ω φ hK p hp hξ hV y₀ hy₀
  obtain ⟨φ₁, hφ₁, k₁, hk₁, c₁, m, e₁, i₁, i₁', c₁0, L₁⟩ := GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK p hp hξ hV
  obtain ⟨φ', hφ', k₂, hk₂, c₂, e₂, i₂, i₂', c₂0, L₂⟩ := GlobalTheory.T.typePlaces_datum_move_to_fullRank D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK y₀ hy₀ φ₁ hφ₁
  refine ⟨φ', hφ', k₂ * k₁, mul_mem hk₂ hk₁, c₂ * c₁, m, ?_, ?_, ?_, mul_ne_zero c₂0 c₁0, ?_⟩
  · have hm : ((k₂ * k₁, (1 : GA D (Wc D i))) : GA D (Vc D i) × GA D (Wc D i)) = (k₂, 1) * (k₁, 1) := by
      simp
    rw [e₂, e₁, hm, map_mul ω, Module.End.mul_apply, map_smul, smul_smul, map_mul D.what₂.embLL]
  · have := i₂.mul i₁
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · have := i₂'.mul i₁'
    simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  · intro h hh w hw
    have := L₁ (h * k₂) (mul_mem hh hk₂) w (L₂ h hh w hw)
    simpa [mul_assoc] using this

end GlobalTheory.FreeBlockMove
