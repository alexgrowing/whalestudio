import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStepStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ExchangeProof

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_mul_le_one (a : kˣ) (z : k) :
    valuation k (((a⁻¹ : kˣ) : k) * z) ≤ 1 ↔ valuation k z ≤ valuation k (a : k) := by
  have : 0 < valuation k (a : k) := by simp [zero_lt_iff]
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ this]

variable [MeasurableSpace k] [BorelSpace k]

open Classical in

theorem opE_step (ν : Measure k) (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t]
    [DecidableEq t] (hP : S.Pattern t) (j c : ℕ) (H : j + c = s) (q : Fin c) (hq : q.val + 1 ≤ S.ρ)
    (hqc : q.val + 2 ≤ c) : ∃ C : ℝ, 0 < C ∧
      opE S.ψ ν (q.val + 2) ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν (q.val + 1) ((S.T t).Phi j c H) := by
  haveI := hν.1
  have := secondCountable k
  have := t2Space k
  set Φ := (S.T t).Phi j c H with hΦ
  let I := (XIx (Fin κ) t (j + 1) ⊕ Fin c) × (XIx (Fin κ) t j ⊕ Fin (c + 1))
  let A : I → Prop := fun i => i.1 = Sum.inr q ∧ i.2.isLeft = true
  let B : I → Prop := fun i => i.2 = Sum.inr q.succ ∧ i.1.isLeft = true
  let R : I → Prop := fun i => Free (q.val + 1) i ∧ ¬ B i
  let a : kˣ := S.ϖ ^ (q.val + 1)
  let b : kˣ := S.ϖ ^ (q.val + 2)
  let sA : Set k := cball a
  let sB : Set k := (fun z => (b : k) * z) ⁻¹' {z | valuation k z < 1}
  have oB : IsOpen sB := IsOpen.preimage (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
  have sBc : sB ⊆ cball b⁻¹ := fun z hz => by
    have hz : valuation k ((b : k) * z) < 1 := hz
    have : 0 < valuation k (b : k) := by simp [zero_lt_iff]
    rw [map_mul] at hz
    change valuation k z ≤ valuation k ((b⁻¹ : kˣ) : k)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : valuation k z = (valuation k (b : k))⁻¹ * (valuation k (b : k) * valuation k z) := by
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
    rw [h1]; exact mul_le_of_le_one_right' hz.le
  have mA : MeasurableSet sA := (isOpen_cball a).measurableSet
  have mB : MeasurableSet sB := oB.measurableSet
  have fA : ν sA ≠ ⊤ := (isCompact_cball a).measure_lt_top.ne
  have fB : ν sB ≠ ⊤ := ((isCompact_cball b⁻¹).measure_lt_top.trans_le' (measure_mono sBc)).ne
  have pA : 0 < ν sA := (isOpen_cball a).measure_pos ν ⟨0, by simp [sA, cball]⟩
  have pB : 0 < ν sB := oB.measure_pos ν ⟨0, by simp [sB]⟩
  let G : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k → (I → k) → ℂ := fun x₀ m =>
    Φ (basePt c x₀ + Matrix.of fun r s' => m (r, s')) * (S.ψ (-ch (basePt c x₀ + Matrix.of fun r s' => m (r, s'))) : ℂ)
  have hR2 : ∀ i, R i ↔ Free (q.val + 2) i ∧ ¬ A i := by
    rintro ⟨r | r, s' | s'⟩ <;> simp [R, A, B, Free, Fin.ext_iff] <;> omega
  have hR1 : ∀ i, R i ↔ Free (q.val + 1) i ∧ ¬ B i := fun i => Iff.rfl
  have hA : ∀ i, A i → Free (q.val + 2) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [A, Free]
  have hB : ∀ i, B i → Free (q.val + 1) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [B, Free]
  have gA : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, A i → m i ∈ sA then (1 : ℂ) else 0) * G x₀ (fun i => if A i then 0 else m i) := by
    intro x₀ m
    let v : XIx (Fin κ) t j → k := fun s' => m (Sum.inr q, Sum.inl s')
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if A (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 := by
      ext (r | r) (s' | s')
      · simp [A]
      · simp [A]
      · by_cases h : r = q
        · subst h; simp [A, v, basePt]
        · simp [A, h]
      · simp [A]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) := by
      simp [ch, A]
    have row0 : ∀ s', (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) (Sum.inr q) (Sum.inl s') = 0 := by
      intro s'; simp [basePt, A]
    have hiff : (∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1) ↔ ∀ i, A i → m i ∈ sA := by
      constructor
      · rintro h ⟨r, s' | s'⟩ ⟨rfl, hs⟩
        · exact (val_inv_mul_le_one a _).1 (h s')
        · simp at hs
      · intro h s'; exact (val_inv_mul_le_one a _).2 (h (Sum.inr q, Sum.inl s') ⟨rfl, rfl⟩)
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.symLevelChain_testFunction_add_row k s κ S t hP j c H q hq _ row0 v]
    by_cases hc : ∀ i, A i → m i ∈ sA
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have gB : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, B i → m i ∈ sB then (1 : ℂ) else 0) * G x₀ (fun i => if B i then 0 else m i) := by
    intro x₀ m
    let w : XIx (Fin κ) t (j + 1) → k := fun r => m (Sum.inl r, Sum.inr q.succ)
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if B (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0 := by
      ext (r | r) (s' | s')
      · simp [B]
      · by_cases h : s' = q.succ
        · subst h; simp [B, w, basePt]
        · simp [B, h]
      · simp [B]
      · simp [B]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) := by
      simp [ch, B]
    have col0 : ∀ r, (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) (Sum.inl r) (Sum.inr q.succ) = 0 := by
      intro r; simp [basePt, B]
    have hiff : (∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1) ↔ ∀ i, B i → m i ∈ sB := by
      constructor
      · rintro h ⟨r | r, s'⟩ ⟨rfl, hs⟩
        · exact h r
        · simp at hs
      · intro h r; exact h (Sum.inl r, Sum.inr q.succ) ⟨rfl, rfl⟩
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.matrix_block_column_vanishing_step k s κ S t hP j c H q hq hqc _ col0 w]
    by_cases hc : ∀ i, B i → m i ∈ sB
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have e2 : ∀ x₀, opE S.ψ ν (q.val + 2) Φ x₀ = (((ν sA).toReal ^ Fintype.card {i // A i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 2)) A R hR2 hA sA mA fA (G x₀) (gA x₀)
  have e1 : ∀ x₀, opE S.ψ ν (q.val + 1) Φ x₀ = (((ν sB).toReal ^ Fintype.card {i // B i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 1)) B R hR1 hB sB mB fB (G x₀) (gB x₀)
  have tA : 0 < (ν sA).toReal := ENNReal.toReal_pos pA.ne' fA
  have tB : 0 < (ν sB).toReal := ENNReal.toReal_pos pB.ne' fB
  refine ⟨(ν sA).toReal ^ Fintype.card {i // A i} / (ν sB).toReal ^ Fintype.card {i // B i},
    div_pos (pow_pos tA _) (pow_pos tB _), funext fun x₀ => ?_⟩
  rw [Pi.smul_apply, e2, e1, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos tB _).ne']

end Step

theorem exchangeAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP j c H p hp1
  induction p, hp1 using Nat.le_induction with
  | base => intro _ _; exact ⟨1, one_pos, by simp⟩
  | succ p hp ih =>
    intro hpc hpρ
    obtain ⟨C, hC, e⟩ := ih (by omega) (by omega)
    obtain ⟨C', hC', e'⟩ := opE_step ν hν S t hP j c H ⟨p - 1, by omega⟩ (by simp; omega) (by simp; omega)
    have h2 : (p - 1) + 2 = p + 1 := by omega
    have h1 : (p - 1) + 1 = p := by omega
    simp only [h1, h2] at e'
    refine ⟨C' * C, mul_pos hC' hC, ?_⟩
    rw [e', e, smul_smul, Complex.ofReal_mul]

end GlobalTheory.SymChain.ExchangeProof
