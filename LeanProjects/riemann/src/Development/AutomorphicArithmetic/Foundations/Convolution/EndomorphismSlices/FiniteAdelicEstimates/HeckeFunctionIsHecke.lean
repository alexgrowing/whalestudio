import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_in {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∈ Z) :
    intersection_update_fsHerm_neg_one Z T φ e w = φ w := by simp [intersection_update_fsHerm_neg_one, h]

private theorem slot_eq_fn2_of_not_mem_of_mem {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∉ Z) (h' : w ∈ T) :
    intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w) := by simp [intersection_update_fsHerm_neg_one, h, h']

private theorem position_out {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∉ Z) (h' : w ∉ T) :
    intersection_update_fsHerm_neg_one Z T φ e w = (K2 a b w : Set _).indicator 1 := by simp [intersection_update_fsHerm_neg_one, h, h']

private theorem heckeFunction_mul (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := by
  funext m
  simp only [fn2, Ex.fn, PositivityTheory.Rg.BcN.F2.mconv]

private theorem heckeFunction_one (w : Pl E) : fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem heckeFunction_isHecke (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) : IsHecke (K2 a b w) (fn2 a b w e) :=
  Asm.exHecke2 E a b w e

private theorem ind_hecke (w : Pl E) : IsHecke (K2 a b w) ((K2 a b w : Set _).indicator 1) := heckeFunction_isHecke w .one

private theorem ind_ind (w : Pl E) : PositivityTheory.Rg.BcN.F2.mconv ((K2 a b w : Set _).indicator 1) ((K2 a b w : Set _).indicator 1) =
    ((K2 a b w : Set _).indicator 1 : GLw a w × GLw b w → ℂ) :=
  ((locAlg E a b ∅ ⟨fun w => KGL w a, fun w => KGL w b, fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩ w).2.2.2.2 _ (ind_hecke w)).1

variable {Z : Finset (Pl E)} (L : Lv a b Z)

private theorem position_hecke {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    IsHecke ((L.L₁ w).prod (L.L₂ w)) (intersection_update_fsHerm_neg_one Z T φ e w) := by
  by_cases hZ : w ∈ Z
  · rw [position_in hZ]; exact hφ w hZ
  · obtain ⟨h₁, h₂⟩ := L.off w hZ
    rw [h₁, h₂]
    by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT]; exact heckeFunction_isHecke w _
    · rw [position_out hZ hT]; exact ind_hecke w

private theorem ln_fix : L.Fix L.ln := fun w _ => (locAlg E a b Z L w).1

private theorem position_ln {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T φ e w) (L.ln w) = intersection_update_fsHerm_neg_one Z T φ e w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (position_hecke L hφ e w)).1

private theorem ln_position {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (L.ln w) (intersection_update_fsHerm_neg_one Z T φ e w) = intersection_update_fsHerm_neg_one Z T φ e w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (position_hecke L hφ e w)).2

private theorem ln_ln (w : Pl E) : PositivityTheory.Rg.BcN.F2.mconv (L.ln w) (L.ln w) = L.ln w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (locAlg E a b Z L w).1).1

private theorem position_one (T : Finset (Pl E)) : intersection_update_fsHerm_neg_one Z T L.ln (fun _ => .one) = L.ln := by
  funext w
  by_cases hZ : w ∈ Z
  · exact position_in hZ
  · have h := (locAlg E a b Z L w).2.2.1 hZ
    by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT, heckeFunction_one, h]
    · rw [position_out hZ hT, h]

private theorem position_empty (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : intersection_update_fsHerm_neg_one Z ∅ L.ln e = L.ln := by
  funext w
  by_cases hZ : w ∈ Z
  · exact position_in hZ
  · rw [position_out hZ (Finset.notMem_empty w), (locAlg E a b Z L w).2.2.1 hZ]

private theorem position_mul {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T φ e w) (intersection_update_fsHerm_neg_one Z T L.ln e' w) = intersection_update_fsHerm_neg_one Z T φ (fun w => (e w).mul (e' w)) w := by
  by_cases hZ : w ∈ Z
  · rw [position_in hZ, position_in hZ, position_in hZ]
    exact ((locAlg E a b Z L w).2.2.2.1 _ (hφ w hZ)).1
  · by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ hT, heckeFunction_mul]
    · rw [position_out hZ hT, position_out hZ hT, position_out hZ hT, ind_ind]

private theorem position_insert {T : Finset (Pl E)} {w : Pl E} (hw : w ∉ T)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (x : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z {w} L.ln e x) (intersection_update_fsHerm_neg_one Z T L.ln e x) = intersection_update_fsHerm_neg_one Z (insert w T) L.ln e x := by
  by_cases hZ : x ∈ Z
  · rw [position_in hZ, position_in hZ, position_in hZ]
    exact ln_ln L x
  · by_cases hx : x = w
    · subst hx
      rw [slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_singleton_self x), position_out hZ hw, slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_insert_self x T)]
      exact ((locAlg E a b Z L x).2.2.2.2 _ (heckeFunction_isHecke x _)).1
    · by_cases hT : x ∈ T
      · rw [position_out hZ (by simpa using hx), slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_insert_of_mem hT)]
        exact ((locAlg E a b Z L x).2.2.2.2 _ (heckeFunction_isHecke x _)).2.1
      · rw [position_out hZ (by simpa using hx), position_out hZ hT, position_out hZ (by simp [hx, hT]), ind_ind]

end

theorem hkMul : HkMul := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ
  have hF := (ffAlg E a b l₁ l₂ D A S hS).2
  have hT := positionTest E a b S Z L hZ
  have hln : IsTestP L.ln := hT.2.1
  have hfix : L.Fix L.ln := ln_fix L
  have hs : ∀ T φ e, L.Fix φ → IsTestP (intersection_update_fsHerm_neg_one Z T φ e) := fun T φ e h => (hT.2.2 φ h).2 T e
  have hsl : ∀ T e, IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) := fun T e => hs T L.ln e hfix
  refine ⟨(hF _ _ hln hln).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show mulF A.ν (A.ff S L.ln L.ln) (A.ff S L.ln L.ln) = A.ff S L.ln L.ln
    rw [(hF _ _ hln hln).2.2.2.2 _ _ hln hln]
    exact congrArg₂ (A.ff S) (funext (ln_ln L)) (funext (ln_ln L))
  · show adjF (A.ff S L.ln L.ln) = A.ff S L.ln L.ln
    rw [(hF _ _ hln hln).2.1]
    have h : (fun w => lfStar (L.ln w)) = L.ln := funext fun w => (locAlg E a b Z L w).2.1
    rw [h]
  · intro T
    show A.ff S (intersection_update_fsHerm_neg_one Z T L.ln fun _ => .one) (intersection_update_fsHerm_neg_one Z T L.ln fun _ => .one) = A.ff S L.ln L.ln
    rw [position_one L T]
  · intro e₁ e₂
    show A.ff S (intersection_update_fsHerm_neg_one Z ∅ L.ln e₁) (intersection_update_fsHerm_neg_one Z ∅ L.ln e₂) = A.ff S L.ln L.ln
    rw [position_empty L, position_empty L]
  · intro T φ e₁ e₂ hφ
    have t₁ := hs T φ e₁ hφ
    have t₂ := hsl T e₂
    refine ⟨(hF _ _ t₁ t₂).1, ?_, fun e₁' e₂' => ?_⟩
    · show mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) (A.ff S L.ln L.ln) =
        A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)
      rw [(hF _ _ t₁ t₂).2.2.2.2 _ _ hln hln]
      exact congrArg₂ (A.ff S) (funext (position_ln L hφ e₁)) (funext (position_ln L hfix e₂))
    · show mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))
          (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁') (intersection_update_fsHerm_neg_one Z T L.ln e₂')) =
        A.ff S (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).mul (e₁' w)) (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).mul (e₂' w))
      rw [(hF _ _ t₁ t₂).2.2.2.2 _ _ (hsl T e₁') (hsl T e₂')]
      exact congrArg₂ (A.ff S) (funext (position_mul L hφ e₁ e₁')) (funext (position_mul L hfix e₂ e₂'))
  · intro T e₁ e₂
    have t₁ := hsl T e₁
    have t₂ := hsl T e₂
    refine ⟨(hF _ _ t₁ t₂).1, ?_⟩
    show mulF A.ν (A.ff S L.ln L.ln) (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) =
      A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)
    rw [(hF _ _ hln hln).2.2.2.2 _ _ t₁ t₂]
    exact congrArg₂ (A.ff S) (funext (ln_position L hfix e₁)) (funext (ln_position L hfix e₂))
  · intro T w e₁ e₂ hw
    show A.ff S (intersection_update_fsHerm_neg_one Z (insert w T) L.ln e₁) (intersection_update_fsHerm_neg_one Z (insert w T) L.ln e₂) =
      mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln e₁) (intersection_update_fsHerm_neg_one Z {w} L.ln e₂))
        (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))
    rw [(hF _ _ (hsl _ e₁) (hsl _ e₂)).2.2.2.2 _ _ (hsl T e₁) (hsl T e₂)]
    exact (congrArg₂ (A.ff S) (funext (position_insert L hw e₁)) (funext (position_insert L hw e₂))).symm

end UpperTheory.Zero.ConvolutionTheory.EB
