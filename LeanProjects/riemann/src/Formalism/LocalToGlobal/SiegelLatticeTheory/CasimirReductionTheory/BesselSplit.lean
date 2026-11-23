import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.SmoothTranslate

noncomputable section

namespace Formalism.L2.SG.BesselSplit

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory Finset
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Period

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def beInt (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ) (v v' : H)
    (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp →L[ℂ] Vp :=
  (⟪v', σ (Matrix.of p.1 * Matrix.of p.2) v⟫_ℂ * star (ψ (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def beOp (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp))
    (ψ : Mat k r → ℂ) (v v' : H) : Vp →L[ℂ] Vp :=
  ∫ p, beInt σ π ψ v v' p ∂(μW.prod μN)

end Period

def BesselBranching : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → IsHCTypeW k r z u π →
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∃ B : H → Vp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
    ∃ v ∈ smoothVecs (k := k) (r := r) σ, ∃ v' ∈ smoothVecs (k := k) (r := r) σ,
      beOp μW μN σ π (psiGen k r z c) v v' ≠ 0

def MemberHom : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) → InterlacingCondition k r u v b →
    HalfIntegralDifference k r u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∃ B : H → Vp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B ∧
    ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def PeriodCont : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    IsHCTypeW k r z u π → IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      Integrable (beInt σ π (psiGen k r z c) v v') (μW.prod μN)) ∧
    (∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      IsCWCont (k := k) (r := r) σ (fun v => beOp μW μN σ π (psiGen k r z c) v v')) ∧
    (∀ v ∈ smoothVecs (k := k) (r := r) σ,
      IsCWCont (k := k) (r := r) σ (fun v' => beOp μW μN σ π (psiGen k r z c) v v'))

def SmoothIrred : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ →
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 →
  ∀ (Wq : Type) [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (ℓ : H → Wq),
    (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ, ℓ (v + v') = ℓ v + ℓ v') →
    ((∀ (a : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, ℓ (a • v) = a • ℓ v) ∨
      (∀ (a : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, ℓ (a • v) = star a • ℓ v)) →
    IsCWCont (k := k) (r := r) σ ℓ →
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ℓ (σ x w) = 0) →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ℓ v = 0

section Chain

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

theorem beInt_add_left (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ)
    (v₁ v₂ v' : H) : beInt σ π ψ (v₁ + v₂) v' = beInt σ π ψ v₁ v' + beInt σ π ψ v₂ v' := by
  funext p
  simp only [beInt, Pi.add_apply, map_add, inner_add_right, add_mul, add_smul]

theorem beInt_smul_left (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ)
    (a : ℂ) (v v' : H) : beInt σ π ψ (a • v) v' = a • beInt σ π ψ v v' := by
  funext p
  simp only [beInt, Pi.smul_apply, map_smul, inner_smul_right, mul_assoc, smul_smul]

theorem beInt_add_right (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ)
    (v v₁' v₂' : H) : beInt σ π ψ v (v₁' + v₂') = beInt σ π ψ v v₁' + beInt σ π ψ v v₂' := by
  funext p
  simp only [beInt, Pi.add_apply, inner_add_left, add_mul, add_smul]

theorem beInt_smul_right (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ)
    (a : ℂ) (v v' : H) : beInt σ π ψ v (a • v') = star a • beInt σ π ψ v v' := by
  funext p
  simp only [beInt, Pi.smul_apply, inner_smul_left, mul_assoc, smul_smul]
  rfl

theorem beOp_add_left (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ) {v₁ v₂ v' : H}
    (h₁ : Integrable (beInt σ π ψ v₁ v') (μW.prod μN)) (h₂ : Integrable (beInt σ π ψ v₂ v') (μW.prod μN)) :
    beOp μW μN σ π ψ (v₁ + v₂) v' = beOp μW μN σ π ψ v₁ v' + beOp μW μN σ π ψ v₂ v' := by
  simp only [beOp, beInt_add_left]
  exact integral_add h₁ h₂

theorem beOp_smul_left (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ) (a : ℂ) (v v' : H) :
    beOp μW μN σ π ψ (a • v) v' = a • beOp μW μN σ π ψ v v' := by
  simp only [beOp, beInt_smul_left]
  exact integral_smul a _

theorem beOp_add_right (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ) {v v₁' v₂' : H}
    (h₁ : Integrable (beInt σ π ψ v v₁') (μW.prod μN)) (h₂ : Integrable (beInt σ π ψ v v₂') (μW.prod μN)) :
    beOp μW μN σ π ψ v (v₁' + v₂') = beOp μW μN σ π ψ v v₁' + beOp μW μN σ π ψ v v₂' := by
  simp only [beOp, beInt_add_right]
  exact integral_add h₁ h₂

theorem beOp_smul_right (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (ψ : Mat k r → ℂ) (a : ℂ) (v v' : H) :
    beOp μW μN σ π ψ v (a • v') = star a • beOp μW μN σ π ψ v v' := by
  simp only [beOp, beInt_smul_right]
  exact integral_smul (star a) _

theorem trans_of_steps (hP : PeriodCont) (hS : SmoothIrred) {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} [FiniteDimensional ℂ Vp]
    {π : Mat k r → (Vp →L[ℂ] Vp)} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : IsHCTypeW k r z u π) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) {w : H} (hw : w ∈ smoothVecs (k := k) (r := r) σ) (hw0 : w ≠ 0)
    (htr : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k := k) (r := r) σ)
    {v v' : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hv' : v' ∈ smoothVecs (k := k) (r := r) σ)
    (hne : beOp μW μN σ π (psiGen k r z c) v v' ≠ 0) :
    ∃ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∃ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      beOp μW μN σ π (psiGen k r z c) (σ x w) (σ x₀ w) ≠ 0 := by
  obtain ⟨hI, hCl, hCr⟩ := hP k r ε lam H σ z c u Vp π μW μN hlam hσ hz hT hπ hW hN
  by_contra hcon
  push_neg at hcon
  have step1 : ∀ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ smoothVecs (k := k) (r := r) σ,
      beOp μW μN σ π (psiGen k r z c) y (σ x₀ w) = 0 := by
    intro x₀ hx₀
    exact hS k r ε lam H σ hlam hσ w hw hw0 (Vp →L[ℂ] Vp)
      (fun y => beOp μW μN σ π (psiGen k r z c) y (σ x₀ w))
      (fun y hy y' hy' => beOp_add_left μW μN σ π _ (hI y hy _ (htr x₀ hx₀)) (hI y' hy' _ (htr x₀ hx₀)))
      (Or.inl fun a y _ => beOp_smul_left μW μN σ π _ a y _)
      (hCl (σ x₀ w) (htr x₀ hx₀))
      (fun x hx => hcon x hx x₀ hx₀)
  have step2 := hS k r ε lam H σ hlam hσ w hw hw0 (Vp →L[ℂ] Vp)
    (fun y' => beOp μW μN σ π (psiGen k r z c) v y')
    (fun y hy y' hy' => beOp_add_right μW μN σ π _ (hI v hv y hy) (hI v hv y' hy'))
    (Or.inr fun a y _ => beOp_smul_right μW μN σ π _ a v y)
    (hCr v hv)
    (fun x₀ hx₀ => step1 x₀ hx₀ v hv)
  exact hne (step2 v' hv')

end Chain

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem conjTranspose_conj_mul_Jm_mul_conj_eq_Jm_of_mem_UH {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hPu : IsUnit P) (hPJ : Matrix.conjTranspose P * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) {a : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Matrix.conjTranspose (P * a * P⁻¹) * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hJ : Formalism.REAL.Jm ε = Matrix.conjTranspose P⁻¹ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ := by
    rw [← hPJ]
    rw [show Matrix.conjTranspose P⁻¹ * (Matrix.conjTranspose P * Formalism.REAL.Jm ε * P) * P⁻¹ = Matrix.conjTranspose (P * P⁻¹) * Formalism.REAL.Jm ε * (P * P⁻¹) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hPP : Matrix.conjTranspose P * Matrix.conjTranspose P⁻¹ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have ha' : Matrix.conjTranspose a * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  calc Matrix.conjTranspose (P * a * P⁻¹) * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = Matrix.conjTranspose P⁻¹ * Matrix.conjTranspose a * (Matrix.conjTranspose P * Matrix.conjTranspose P⁻¹) * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * P) * a * P⁻¹ := by
        rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.conjTranspose P⁻¹ * (Matrix.conjTranspose a * Formalism.QuantumDeterminants.Hpk k r * a) * P⁻¹ := by
        rw [hPP, h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hJ]

theorem mulOnUH_of_dsHpk {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    PI.PhMeasCore.UnitaryGroupMassFormula.MulOnUH (Formalism.QuantumDeterminants.Hpk k r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  obtain ⟨⟨hone, hmul⟩, -, -⟩ := hDS.2.2.1
  have conj : ∀ a : Mat k r, P⁻¹ * (P * a * P⁻¹) * P = a := fun a => by
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have mem : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * a * P⁻¹ ∈ UJset ε := fun a ha => conjTranspose_conj_mul_Jm_mul_conj_eq_Jm_of_mem_UH hPu hPJ ha
  refine ⟨?_, fun a ha b hb => ?_⟩
  · simpa [h1] using hone
  · have e := hmul _ (mem a ha) _ (mem b hb)
    have e3 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, h1, Matrix.one_mul]
    simp only [e3, conj] at e
    exact e

theorem smooth_translate_ds {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {w : H} (hw : w ∈ smoothVecs (k := k) (r := r) σ)
    {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : σ x w ∈ smoothVecs (k := k) (r := r) σ := by
  exact PI.PhMeasCore.UnitaryGroupMassFormula.smooth_translate (mulOnUH_of_dsHpk hσ) hw hx

end Smooth

section GGP

def ggpM {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin m) : ℕ :=
  (univ.filter fun s : Fin n => a i + b s < 0).card

def ggpChi {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin m) : ℤ := (-1) ^ ggpM a b i

def ggpMij {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) (i j : Fin m) : ℕ :=
  (univ.filter fun s : Fin n => 0 < a i + b s ∧ a j + b s < 0).card

def ggpCompact {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) (i j : Fin m) : Prop :=
  ggpChi a b i * ggpChi a b j = (-1) ^ (i.val + j.val)

def aDual {k : ℕ} (u : Fin k → ℝ) : Fin k → ℝ := fun p => -u (Fin.rev p)

end GGP

end Formalism.L2.SG.BesselSplit
