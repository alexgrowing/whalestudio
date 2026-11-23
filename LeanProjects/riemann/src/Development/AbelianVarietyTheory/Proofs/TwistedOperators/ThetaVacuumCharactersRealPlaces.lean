import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignaturesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

namespace GlobalTheory.VacuumCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem signBlockDeterminant_diagonalPhases_zpow {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) (x : Bool → ℤ) :
    signBlockDeterminant ε true (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x true *
      signBlockDeterminant ε false (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x false =
      Complex.exp (Complex.I * ∑ j, (x (ε j) : ℂ) * t j) := by
  have key : ∀ e : Bool, signBlockDeterminant ε e (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x e =
      Complex.exp (Complex.I * ∑ j ∈ Finset.univ.filter (fun j => ε j = e), (x e : ℂ) * t j) := by
    intro e
    rw [signBlockDeterminant, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal]
    simp only [Function.comp_apply]
    rw [← Complex.exp_sum,
      ← Complex.exp_int_mul,
      Finset.sum_subtype (Finset.univ.filter fun j => ε j = e) (p := fun j => ε j = e) (by simp)]
    congr 1
    try simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [key, key, ← Complex.exp_add, ← mul_add,
    ← Finset.sum_fiberwise (M := ℂ) (s := (Finset.univ : Finset (Fin n))) (g := ε)
      (f := fun j : Fin n => (x (ε j) : ℂ) * (t j : ℂ)), Fintype.sum_bool]
  congr 3 <;> refine Finset.sum_congr rfl fun j hj => ?_ <;> rw [(Finset.mem_filter.1 hj).2]

theorem diag_mem_Kset {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) :
    (diagonal fun j => Complex.exp (Complex.I * t j)) ∈ Formalism.REAL.Kset ε := by
  have hu : ∀ j, star (Complex.exp (Complex.I * t j)) * Complex.exp (Complex.I * t j) = 1 := by
    intro j
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact hu j
  · rw [Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext j
    ring

theorem torusVac_of_compactFock {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ)
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (h : CompactFock ψ θ M M' ω f τ aS aT) :
    TorusVac θ M M' ω f τ aS aT := by
  obtain ⟨x, y, hx, hy, hK⟩ := h
  intro t t'
  have hact := hK _ (diag_mem_Kset (M.ε τ) t) _ (diag_mem_Kset (M'.ε τ) t') 1
  rw [map_one, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.ptOf_one] at hact
  rw [hact, signBlockDeterminant_diagonalPhases_zpow, signBlockDeterminant_diagonalPhases_zpow, ← Complex.exp_add, ← mul_add]
  have hx' : ∀ j, ((x (M.ε τ j) : ℤ) : ℂ) = ((wtS (M'.ε τ) aT (M.ε τ j) : ℚ) : ℂ) := fun j => by
    rw [← hx j]; push_cast; rfl
  have hy' : ∀ i, ((y (M'.ε τ i) : ℤ) : ℂ) = ((wtT (M.ε τ) aS (M'.ε τ i) : ℚ) : ℂ) := fun i => by
    rw [← hy i]; push_cast; rfl
  simp only [hx', hy']

theorem vacChar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  intro D V W S S' M M' θ ψ χS χT ω f τ aS aT hθ hW hS hT hV
  have hF := GlobalTheory.ChainFr.isVacF_of_isVacVec hV
  have hK := GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF hV.ne
  have hL := GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF
  have hC : CompactFock ψ θ M M' ω f τ aS aT := by
    obtain ⟨x, y, hx, hy, hk⟩ := hK
    refine ⟨x, y, hx, hy, fun g hg k hk' P => ?_⟩
    have e := hk g hg k hk' P
    rwa [GlobalTheory.ChainFr.ptF_ofModel] at e
  refine ⟨torusVac_of_compactFock ψ θ M M' ω f τ aS aT hC, hC, ?_, ?_⟩
  · intro X hX P z
    have e := hL.1 X hX P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    rw [sub_eq_add_neg, ← neg_smul]
    exact e
  · intro Y hY P z
    have e := hL.2 Y hY P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    exact e

end GlobalTheory.VacuumCharacter

end
