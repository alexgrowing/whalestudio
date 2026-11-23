import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def wfam {d : ℕ} {α : Type} (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d :=
  L.map (fun t => (t.1, t.2.map F)) ++ [(c, [])]

def WFamApp : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ)
    (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ),
    WOp.app (wfam L F c) v x = (L.map fun t => t.1 * vfW (t.2.map F) v x).sum + c * v x

def WFamSymb : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ)
    (x ξ : Fin d → ℝ) (τ : α → ℂ), 1 ≤ j → (∀ t ∈ L, ∀ X ∈ t.2, ((ξ ⬝ᵥ F X x : ℝ) : ℂ) = τ X) →
    WOp.symb (wfam L F c) j x ξ = (L.map fun t => if t.2.length = j then t.1 * (t.2.map τ).prod else 0).sum

def TrRealLie : Prop :=
  ∀ (k r : ℕ) (A X : B.Mat k r), B.inLie k r A → B.inLie k r X →
    (((Matrix.trace (A * X)).re : ℝ) : ℂ) = Matrix.trace (A * X)

def CkLevOn : Prop :=
  ∀ (k r m : ℕ) (Dm : Set (B.Mat k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E),
    Q.CkLev k r 0 m Dm f → B.CkOn (m : ℕ∞) (B.GV k r ∩ Dm) f

theorem wfam_ok {d : ℕ} {α : Type} {O : Set (Fin d → ℝ)} (L : List (ℂ × List α))
    (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ) (hL : ∀ t ∈ L, t.2.length ≤ j)
    (hF : ∀ X, ContDiffOn ℝ ∞ (F X) O) : FamOK O (wfam L F c) j := by
  intro t ht
  rw [wfam, List.mem_append] at ht
  rcases ht with ht | ht
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    refine ⟨by simpa using hL t0 ht0, ?_⟩
    intro V hV
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hV
    exact hF X
  · simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, by simp⟩

theorem opCVOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCVOf := by
  intro hRw hCW k r z z' d O U κ Φ u hC hOm hCk hev j hj1 hjn
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨Ys, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r j hj1 hjn
  choose c hc using hev
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (Ys i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapROf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapROf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z' Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapLOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapLOf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VL κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).2), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VL κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • t.2.foldr Q.LdV u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).2, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ hΞ hcov
    rw [hS d _ L (VL κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ X hΞ ((hL t ht).2 X hX)])]
    exact hsym Ξ hΞ

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
