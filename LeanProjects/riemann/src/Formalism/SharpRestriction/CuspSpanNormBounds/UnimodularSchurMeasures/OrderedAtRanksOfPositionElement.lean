import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem discrete_series_unitary_rep {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : CayleySignature.Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      σ (x * y) = (σ x).comp (σ y)) ∧ ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ v, ‖σ x v‖ = ‖v‖ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, -, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hback : ∀ x : CayleySignature.Mat k r, P⁻¹ * (P * x * P⁻¹) * P = x := fun x => by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPi, Matrix.one_mul, Matrix.mul_one]
  have hmem : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
    show (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) = Formalism.REAL.Jm ε
    have e1 : (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) =
        (P⁻¹)ᴴ * (xᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * x) * P⁻¹ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, hPJ, hx', ← hPJ]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPi']; simp
  refine ⟨?_, fun x hx y hy => ?_, fun x hx v => ?_⟩
  · have : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hPi] at this
  · have := hmul _ (hmem x hx) _ (hmem y hy)
    simp only [hback] at this
    have e : P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = x * y := by
      calc P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = (P⁻¹ * P) * x * (P⁻¹ * P) * y * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = x * y := by rw [hPi]; simp
    rwa [e] at this
  · have := hiso _ (hmem x hx) v
    simp only [hback] at this
    exact this

theorem deriv_clm_comp_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (L L' : H →L[ℂ] H)
    (hL : ∀ y, L' (L y) = y) (f : ℝ → H) : deriv (fun t => L (f t)) 0 = L (deriv f 0) := by
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd.hasDerivAt).deriv
  · have hd' : ¬ DifferentiableAt ℝ (fun t => L (f t)) 0 := fun h => hd (by
      have h2 := (L'.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) h
      have e : ((L'.restrictScalars ℝ : H →L[ℝ] H) : H → H) ∘ (fun t => L (f t)) = f := by
        funext t; exact hL (f t)
      rwa [e] at h2)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', map_zero]

section Pos

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem lie_algebra_conj_mem {a ai X : CayleySignature.Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hai : ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (h1 : a * ai = 1) (hX : InLieHpk k r X) :
    InLieHpk k r (a * X * ai) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hai' : aiᴴ * Formalism.QuantumDeterminants.Hpk k r * ai = Formalism.QuantumDeterminants.Hpk k r := hai
  have hX' : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  have e1 : aᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * ai := by
    calc aᴴ * Formalism.QuantumDeterminants.Hpk k r = aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * ai) := by rw [h1, Matrix.mul_one]
      _ = (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * ai := by simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r * ai := by rw [ha']
  have h2 : ai * a = 1 := mul_eq_one_comm.1 h1
  have e2 : Formalism.QuantumDeterminants.Hpk k r * a = aiᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * a = (aiᴴ * Formalism.QuantumDeterminants.Hpk k r * ai) * a := by rw [hai']
      _ = aiᴴ * Formalism.QuantumDeterminants.Hpk k r * (ai * a) := by simp only [Matrix.mul_assoc]
      _ = aiᴴ * Formalism.QuantumDeterminants.Hpk k r := by rw [h2, Matrix.mul_one]
  show (a * X * ai)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * (a * X * ai) = 0
  calc (a * X * ai)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * (a * X * ai)
      = aiᴴ * Xᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r) + (Formalism.QuantumDeterminants.Hpk k r * a) * X * ai := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = aiᴴ * (Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X) * ai := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

variable (σ : CayleySignature.Mat k r → (H →L[ℂ] H))
  (hmul : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (x * y) = (σ x).comp (σ y))
  (hone : σ 1 = 1)

include hmul in
theorem smooth_vectors_translate {ai : CayleySignature.Mat k r} (hai : ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) : σ ai v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨Uo, F, hO, hmem, hF, hEq⟩ := hv (g₀ * ai) (mat_mul_mem_UH_Hpk hg₀ hai)
  let L : CayleySignature.Mat k r →L[ℝ] CayleySignature.Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ ai)
  have hL : ∀ g, L g = g * ai := fun g => rfl
  refine ⟨L ⁻¹' Uo, fun g => F (L g), hO.preimage L.continuous, hmem, ?_, fun g hg hin => ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun g hg => hg)
  · have h1 : σ (g * ai) v = F (g * ai) := hEq (g * ai) hg (mat_mul_mem_UH_Hpk hin hai)
    show σ g (σ ai v) = F (L g)
    rw [hL, ← h1, hmul g hin ai hai]; rfl

include hmul hone in
theorem derivative_word_translate {a ai : CayleySignature.Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hai : ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (h1 : a * ai = 1)
    (w : List (CayleySignature.Mat k r)) (hw : ∀ X ∈ w, InLieHpk k r X) (v : H) :
    dsigW (k := k) (r := r) σ w (σ ai v) = σ ai (dsigW (k := k) (r := r) σ (w.map fun X => a * X * ai) v) := by
  have h2 : ai * a = 1 := mul_eq_one_comm.1 h1
  have hinv : ∀ y, σ a (σ ai y) = y := fun y => by
    have := hmul a ha ai hai
    rw [h1, hone] at this
    have e := congrArg (fun T : H →L[ℂ] H => T y) this
    exact e.symm
  induction w with
  | nil => rfl
  | cons X w ih =>
    have ihw := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    have hX := hw X List.mem_cons_self
    show dsig σ X (dsigW σ w (σ ai v)) = σ ai (dsig σ (a * X * ai) (dsigW σ (w.map fun X => a * X * ai) v))
    rw [ihw]
    unfold dsig
    rw [← deriv_clm_comp_zero (σ ai) (σ a) hinv]
    congr 1
    funext t
    have hu : IsUnit a := ⟨⟨a, ai, h1, h2⟩, rfl⟩
    have hainv : a⁻¹ = ai := Matrix.inv_eq_right_inv h1
    have e1 : NormedSpace.exp ((t : ℂ) • (a * X * ai)) = a * NormedSpace.exp ((t : ℂ) • X) * ai := by
      have := Matrix.exp_conj a ((t : ℂ) • X) hu
      rw [hainv] at this
      rw [← this]
      congr 1
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have hE := exp_lie_algebra_mem_unitary k r X hX t
    have e2 : NormedSpace.exp ((t : ℂ) • X) * ai = ai * (a * NormedSpace.exp ((t : ℂ) • X) * ai) := by
      calc NormedSpace.exp ((t : ℂ) • X) * ai = (ai * a) * NormedSpace.exp ((t : ℂ) • X) * ai := by
            rw [h2, Matrix.one_mul]
        _ = ai * (a * NormedSpace.exp ((t : ℂ) • X) * ai) := by simp only [Matrix.mul_assoc]
    set y := dsigW (k := k) (r := r) σ (w.map fun X => a * X * ai) v
    have e3 : σ (NormedSpace.exp ((t : ℂ) • X)) (σ ai y) = σ (NormedSpace.exp ((t : ℂ) • X) * ai) y := by
      rw [hmul _ hE _ hai]; rfl
    have e4 : σ ai (σ (a * NormedSpace.exp ((t : ℂ) • X) * ai) y) =
        σ (ai * (a * NormedSpace.exp ((t : ℂ) • X) * ai)) y := by
      rw [hmul _ hai _ (mat_mul_mem_UH_Hpk (mat_mul_mem_UH_Hpk ha hE) hai)]; rfl
    rw [e3, e1, e4, ← e2]

end Pos

def PositionElement : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → Formalism.QuantumDeterminants.inWb k r z' → 0 < Formalism.QuantumDeterminants.Tz k r z' → (∀ a, c' a ≠ 0) →
  ∀ g g' : CayleySignature.Mat k r, IsFrameW k r z g → IsFrameW k r z' g' →
  ∃ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∃ ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), a * ai = 1 ∧
    (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ai * m * a ∈ Formalism.QuantumDeterminants.Nset k r ∧ psiGen k r z' c' m = psiGen k r z c (ai * m * a)) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z', ai * h * a ∈ Formalism.QuantumDeterminants.UWset k r z) ∧
    ∃ g'', IsFrameW k r z' g'' ∧ ∀ h0 : Matrix (Fin k) (Fin k) ℂ,
      ai * (g'' * blockW k r h0 * g''⁻¹) * a = g * blockW k r h0 * g⁻¹

end Formalism.MainNotions.LeviCoordinates

end
