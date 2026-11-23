import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FamOK {d : ℕ} (O : Set (Fin d → ℝ)) (P : WOp d) (m : ℕ) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O

def OpCV : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ 2 * r + k + 1 → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * Ξ₀.charpoly.coeff (2 * r + k + 1 - j)

def OpCapR : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z'] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ₀ Bs).charpoly.coeff (k - j)

def OpCapL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ : B.Mat k r), B.inLie k r Ξ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace (Ξ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def OpCVOf : Prop := RwChart → CapWords → OpCV

def OpCapROf : Prop := RwChart → CapRWords → OpCapR

def OpCapLOf : Prop := RwChart → CapLWords → OpCapL

def NilOfCharpoly : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ j, 1 ≤ j → j ≤ n → M.charpoly.coeff (n - j) = 0) → IsNilpotent M

def ConjAlg : Prop :=
  ∀ (k r : ℕ) (g : B.Mat k r), g ∈ B.GV k r →
    (∀ A : B.Mat k r, B.inLie k r A → B.inLie k r (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, IsNilpotent A → IsNilpotent (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, A ≠ 0 → g * A * g⁻¹ ≠ 0) ∧
    ∀ A X : B.Mat k r, Matrix.trace ((g * A * g⁻¹) * (g * X * g⁻¹)) = Matrix.trace (A * X)

def CovL : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
      (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * X)).re

def opOne {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d := [(1, [V]), (-c, [])]

theorem opOne_app {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    WOp.app (opOne V c) v x = vfD V v x - c * v x := by
  simp [opOne, WOp.app, vfW]
  ring

theorem opOne_symb {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (x ξ : Fin d → ℝ) :
    WOp.symb (opOne V c) 1 x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) := by
  simp [opOne, WOp.symb]

theorem opOne_ok {d : ℕ} {O : Set (Fin d → ℝ)} {V : (Fin d → ℝ) → (Fin d → ℝ)} (c : ℂ) (hV : ContDiffOn ℝ ∞ V O) :
    FamOK O (opOne V c) 1 := by
  intro t ht
  simp only [opOne, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine ⟨by simp, ?_⟩
    intro W hW
    simp only [List.mem_singleton] at hW
    rw [hW]; exact hV
  · exact ⟨by simp, by simp⟩

theorem re_trace_span {k r q : ℕ} (A : B.Mat k r) (Xs : Fin q → B.Mat k r) (a : Fin q → ℝ)
    (h : ∀ i, (Matrix.trace (A * Xs i)).re = 0) :
    (Matrix.trace (A * ∑ i, ((a i : ℝ) : ℂ) • Xs i)).re = 0 := by
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, h i, mul_zero]

theorem fin_shift {n : ℕ} {p : ℕ → Prop} (h : ∀ j : Fin n, p ((j : ℕ) + 1)) : ∀ j, 1 ≤ j → j ≤ n → p j := by
  intro j h1 h2
  have := h ⟨j - 1, by omega⟩
  simpa [Nat.sub_add_cancel h1] using this

theorem chartSysWOfParts_of (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly)
    (hConj : ConjAlg) (hCovL : CovL) : ChartSysWOfParts := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 k r z z' d O U κ Φ u hk hz hz' hT hT' hC hOm hG
  obtain ⟨hCk, hNR, hNL, hCLe, hCRe, hCVe⟩ := hG
  obtain ⟨huc, hfld, hw⟩ := h2 k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨q, Xs, hXs, hspan⟩ := h3 k r
  obtain ⟨Bs, hBs⟩ := h8 k r z hz hT
  obtain ⟨Bs', hBs'⟩ := h8 k r z' hz' hT'
  have oCV := hCV h2 h4 k r z z' d O U κ Φ u hC hOm hCk hCVe
  have oCR := hCR h2 h5 k r z z' d O U κ Φ u Bs' hC hOm hCk hBs' (hCRe Bs' hBs')
  have oCL := hCL h2 h6 k r z z' d O U κ Φ u Bs hC hOm hCk hBs (hCLe Bs hBs)
  have hXin : ∀ i, B.inLie k r (Xs i) := fun i => (hspan (Xs i) (hXs i)).1
  choose cR hcR using fun i => hNR (Xs i) (hXs i)
  choose cL hcL using fun i => hNL (Xs i) (hXs i)
  choose PV cV hcV0 hPVok hPVapp hPVsym using
    fun j : Fin (2 * r + k + 1) => oCV ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PR cRR hcR0 hPRok hPRapp hPRsym using
    fun j : Fin k => oCR ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PL cLL hcL0 hPLok hPLapp hPLsym using
    fun j : Fin k => oCL ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  have hOmx : ∀ x ∈ O, κ x ∈ JF.Om k r z z' := fun x hx => ⟨(hC.2.2.2.2.1 x hx).1, hOm x hx⟩
  refine ⟨Fin q ⊕ Fin q ⊕ Fin (2 * r + k + 1) ⊕ Fin k ⊕ Fin k, inferInstance,
    Sum.elim (fun i => opOne (VR κ Φ (Xs i)) (cR i)) (Sum.elim (fun i => opOne (VL κ Φ (Xs i)) (cL i))
      (Sum.elim PV (Sum.elim PR PL))),
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (Sum.elim (fun j => (j : ℕ) + 1)
      (Sum.elim (fun j => (j : ℕ) + 1) (fun j => (j : ℕ) + 1)))),
    ?_, ?_, huc, ?_, ?_⟩
  · rintro (i | i | j | j | j)
    · show 1 ≤ 2 * r + k + 1; omega
    · show 1 ≤ 2 * r + k + 1; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; exact Nat.succ_le_of_lt j.isLt
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
  · rintro (i | i | j | j | j)
    · exact opOne_ok _ (hfld _).1
    · exact opOne_ok _ (hfld _).2
    · exact hPVok j
    · exact hPRok j
    · exact hPLok j
  · rintro (i | i | j | j | j) x hx
    · show WOp.app (opOne (VR κ Φ (Xs i)) (cR i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).1
      simp only [B.Rw, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcR i _ (hOmx x hx), smul_eq_mul, sub_self]
    · show WOp.app (opOne (VL κ Φ (Xs i)) (cL i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).2
      simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcL i _ (hOmx x hx), smul_eq_mul, sub_self]
    · exact hPVapp j x hx
    · exact hPRapp j x hx
    · exact hPLapp j x hx
  · intro x hx ξ hξ hall
    obtain ⟨Ξ₀, hΞ₀, hΞ₀0, hcov⟩ := h1 k r d O U κ Φ hC x hx ξ
    have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    obtain ⟨cLie, cNil, cNe, cTr⟩ := hConj k r (κ x) hg
    have hcovL := hCovL k r d O U κ Φ hC x hx ξ Ξ₀ hΞ₀ hcov
    have hΞ : B.inLie k r (κ x * Ξ₀ * (κ x)⁻¹) := cLie Ξ₀ hΞ₀
    have hNRz : ∀ i, (Matrix.trace (Ξ₀ * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inl i)
      change WOp.symb (opOne (VR κ Φ (Xs i)) (cR i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcov _ (hXin i)]
      exact_mod_cast h0
    have hNLz : ∀ i, (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inr (Sum.inl i))
      change WOp.symb (opOne (VL κ Φ (Xs i)) (cL i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcovL _ (hXin i)]
      exact_mod_cast h0
    have hVF : ∀ j : Fin (2 * r + k + 1), Ξ₀.charpoly.coeff (2 * r + k + 1 - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inl j)))
      change WOp.symb (PV j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPVsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcV0 j)
    have hRF : ∀ j : Fin k, (cmp Ξ₀ Bs').charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      change WOp.symb (PR j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPRsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcR0 j)
    have hLF : ∀ j : Fin k, (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))
      change WOp.symb (PL j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPLsym j x hx ξ _ hΞ hcovL] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcL0 j)
    have hnil0 : IsNilpotent Ξ₀ :=
      hNil _ Ξ₀ (fin_shift (p := fun j => Ξ₀.charpoly.coeff (2 * r + k + 1 - j) = 0) hVF)
    have hUW' := h7 k r z' Bs' hz' hT' hBs' Ξ₀ hΞ₀ (fin_shift (p := fun j => (cmp Ξ₀ Bs').charpoly.coeff (k - j) = 0) hRF)
    have hUW := h7 k r z Bs hz hT hBs _ hΞ
      (fin_shift (p := fun j => (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - j) = 0) hLF)
    refine ⟨κ x * Ξ₀ * (κ x)⁻¹, hΞ, cNe Ξ₀ (hΞ₀0 hξ), cNil Ξ₀ hnil0, ?_, ?_⟩
    · intro X hX
      rcases hX with hX | hX
      · exact hUW X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span _ Xs a hNLz
    · intro X hX
      rw [cTr Ξ₀ X]
      rcases hX with hX | hX
      · exact hUW' X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span Ξ₀ Xs a hNRz

theorem chartEqs_of_J (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly) (hConj : ConjAlg)
    (hCovL : CovL) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords) (h5 : CapRWords) (h6 : CapLWords)
    (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField) (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_all (chartSysWOfParts_of hCV hCR hCL hNil hConj hCovL) h1 h2 h3 h4 h5 h6 h7 h8 hS s1 s2 s3

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
