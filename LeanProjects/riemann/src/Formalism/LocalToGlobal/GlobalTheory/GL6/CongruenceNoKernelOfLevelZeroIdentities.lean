import Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionExtendsFromClasses
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

section UnramifiedDiagonal

variable (D : D7) (u : D.what₂.Word)

def DiamondCommutesLevelZero : Prop :=
  ∀ v v' (a : ((D.mem u).A.Fv v')ˣ), ∀ φ ∈ (D.fm u).Fi 0,
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) ∧
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ)

def TraceDiamondInvariantLevelZero : Prop :=
  ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi 0, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v φ

def DUFormulaLevelZero : Prop :=
  ∀ v, ∀ φ ∈ (D.fm u).Fi 0, Dop D u 0 v (Uop D u 0 v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • Nm D u 0 v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • trp D u 0 v φ

variable {D u}

theorem norm_commutes_hecke_level_zero (hc : DiamondCommutesLevelZero D u) (v v' : (D.mem u).A.vT) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    Nm D u 0 v' (Uop D u 0 v φ) = Uop D u 0 v (Nm D u 0 v' φ) ∧
    Nm D u 0 v' (Dop D u 0 v φ) = Dop D u 0 v (Nm D u 0 v' φ) := by
  simp only [norm_eq_sum_diamond, map_sum]
  exact ⟨Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).1, Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).2⟩

theorem trace_zero_of_norm_zero_level_zero (ht : TraceDiamondInvariantLevelZero D u) (v : (D.mem u).A.vT) (φ : Fn D u 0)
    (hφ : φ ∈ (D.fm u).Fi 0) (hN : Nm D u 0 v φ = 0) : trp D u 0 v φ = 0 := by
  have h1 : ∑ a : ((D.mem u).A.Fv v)ˣ, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v (Nm D u 0 v φ) := by
    rw [norm_eq_sum_diamond, map_sum]
  rw [hN, map_zero, Finset.sum_congr rfl (fun a _ => ht v a φ hφ), Finset.sum_const,
    Finset.card_univ] at h1
  have hc : (Fintype.card ((D.mem u).A.Fv v)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

theorem hecke_ramified_zero_of_identities (Tf : FormsTied D u) (hT : (D.mem u).A.T ≠ 0) (hc : DiamondCommutesLevelZero D u)
    (ht : TraceDiamondInvariantLevelZero D u) (h6 : DUFormulaLevelZero D u) : HeckeRamifiedLevelZero D u := by
  intro v φ hφ
  have hU : ∀ ψ ∈ MramI D u 0, Uop D u 0 v ψ ∈ MramI D u 0 := by
    intro ψ hψ; rw [mem_ramified_forms_iff] at hψ ⊢
    refine ⟨U_op_preserves_forms_level_zero Tf v ψ hψ.1, fun v' => ?_⟩
    rw [(norm_commutes_hecke_level_zero hc v v' ψ hψ.1).1, hψ.2 v', map_zero]
  have hD : ∀ ψ ∈ MramI D u 0, Dop D u 0 v ψ ∈ MramI D u 0 := by
    intro ψ hψ; rw [mem_ramified_forms_iff] at hψ ⊢
    refine ⟨D_op_preserves_forms_level_zero Tf v ψ hψ.1, fun v' => ?_⟩
    rw [(norm_commutes_hecke_level_zero hc v v' ψ hψ.1).2, hψ.2 v', map_zero]
  have hDU : ∀ ψ ∈ MramI D u 0, Dop D u 0 v (Uop D u 0 v ψ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • ψ := by
    intro ψ hψ
    have hψ' := (mem_ramified_forms_iff D u ψ).1 hψ
    rw [h6 v ψ hψ'.1, hψ'.2 v, trace_zero_of_norm_zero_level_zero ht v ψ hψ'.1 (hψ'.2 v), smul_zero, sub_zero, add_zero]
  have := ramified_forms_finite_dimensional D u 0
  have hc0 : ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hT)
  exact ⟨hU φ hφ, hD φ hφ, U_D_of_D_U_on_finite_dim (MramI D u 0) (Uop D u 0 v) (Dop D u 0 v) _ hc0 hU hDU φ hφ⟩

theorem congruence_no_kernel_of_level_zero_identities
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      HeckeIntegralLevelZero D u ∧ DiamondCommutesLevelZero D u ∧ TraceDiamondInvariantLevelZero D u ∧ DUFormulaLevelZero D u ∧ SecondBranchInclusionLength D u) : CongruenceLatticeLengthBoundFamily :=
  congruence_no_kernel_family_minimal fun D u hT hS hA => by
    obtain ⟨h4, hc, ht, h6, hB⟩ := h D u hT hS hA
    obtain ⟨Tf, -⟩ := hT
    exact ⟨h4, hecke_ramified_zero_of_identities Tf (by have := hS.1; omega) hc ht h6, hB⟩

end UnramifiedDiagonal

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
