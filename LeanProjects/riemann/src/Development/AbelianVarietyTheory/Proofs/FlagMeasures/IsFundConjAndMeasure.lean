import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector

noncomputable section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol.UnipConj
variable {k r : ℕ} {ι : Type}

theorem of_conjM (a : Mat k r) (x : Mt k r) : Matrix.of (conjM a x) = a * Matrix.of x * a⁻¹ := rfl

theorem conjM_lmulM {a : Mat k r} (ha : IsUnit a.det) (m x : Mt k r) :
    conjM a (lmulM (Matrix.of m) x) = lmulM (Matrix.of (conjM a m)) (conjM a x) := by
  apply Matrix.of.injective
  have hl : ∀ (b : Mat k r) (y : Mt k r), Matrix.of (lmulM b y) = b * Matrix.of y := fun _ _ => rfl
  rw [of_conjM, hl, hl, of_conjM, of_conjM]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.one_mul]

theorem mulVec_conj_iff (a M : Mat k r) (ha : IsUnit a.det) (w w' : Fin (2 * r + k + 1) → ℂ) :
    M *ᵥ (a *ᵥ w) = a *ᵥ w' ↔ (a⁻¹ * M * a) *ᵥ w = w' := by
  constructor
  · intro h
    have h' := congrArg (fun u => a⁻¹ *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec] at h'
    rw [← h', Matrix.mul_assoc]
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv a ha, Matrix.one_mul]

theorem mem_realPts_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n : ι → Mat k r)
    (hn : ∀ v, IsUnit (n v).det) (m : ι → Mt k r) :
    m ∈ realPts (fun v y => n v *ᵥ Φ v y) Γ ↔ (fun v => conjM (n v)⁻¹ (m v)) ∈ realPts Φ Γ := by
  have key : ∀ v (w w' : Fin (2 * r + k + 1) → ℂ),
      (Matrix.of (m v) *ᵥ (n v *ᵥ w) = n v *ᵥ w') ↔ Matrix.of (conjM (n v)⁻¹ (m v)) *ᵥ w = w' := by
    intro v w w'
    rw [mulVec_conj_iff _ _ (hn v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hn v)]
  simp only [realPts, Set.mem_ofPred_eq, key]

theorem mem_RP_iff (n₁ g n₂ : ι → Mat k r) (h₁ : ∀ v, n₁ v ∈ Nset k r) (h₂ : ∀ v, n₂ v ∈ Nset k r)
    (x : ι → Mt k r) :
    x ∈ RP k r g ↔ (fun v => conjM (n₂ v)⁻¹ (x v)) ∈ RP k r (fun v => n₁ v * g v * n₂ v) := by
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (h₂ v).1
  simp only [RP, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  rw [StabHaar.Rset_conj (g v) (h₁ v) (h₂ v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hu v)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu v), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (hu v)]

private theorem conjM_conjM_inv {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a (conjM a⁻¹ y) = y := by
  have h := congrFun (StabHaar.conj_conj a a⁻¹) y
  rw [Matrix.mul_nonsing_inv a ha, StabHaar.conj_one] at h
  exact h

private theorem conjM_inv_conjM' {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a⁻¹ (conjM a y) = y := by
  have h := congrFun (StabHaar.conj_conj a⁻¹ a) y
  rw [Matrix.nonsing_inv_mul a ha, StabHaar.conj_one] at h
  exact h

theorem isFund_conj_and_measure : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k r : ℕ) (ι : Type) [Fintype ι] (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n₁ g n₂ : ι → Mat k r) (Ω : Set (ι → Mt k r)) (lam : Measure (Mt k r)), SigmaFinite lam → (∀ v, n₁ v ∈ Nset k r ∧ n₂ v ∈ Nset k r ∧ IsUnit (g v).det) → IsFund (realPts Φ Γ) (RP k r (fun v => n₁ v * g v * n₂ v)) Ω → IsFund (realPts (fun v y => n₂ v *ᵥ Φ v y) Γ) (RP k r g) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) ∧ Measure.pi (fun v => lam.map (conjM (n₂ v)⁻¹)) Ω = Measure.pi (fun _ : ι => lam) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) := by
  intro K V _ _ _ k r ι _ Φ Γ n₁ g n₂ Ω lam hlam hN hF
  have := hlam
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (hN v).2.1.1
  have hui : ∀ v, IsUnit ((n₂ v)⁻¹).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hu v)
  let e : ∀ _ : ι, Mt k r ≃ᵐ Mt k r := fun v => StabHaar.conjE (n₂ v)⁻¹ (hui v)
  let E : (ι → Mt k r) ≃ᵐ (ι → Mt k r) := MeasurableEquiv.piCongrRight e
  let Cf : (ι → Mt k r) → (ι → Mt k r) := fun x v => conjM (n₂ v) (x v)
  have hEC : ∀ y, E (Cf y) = y := fun y => funext fun v => conjM_inv_conjM' (hu v) (y v)
  have hCE : ∀ y, Cf (E y) = y := fun y => funext fun v => conjM_conjM_inv (hu v) (y v)
  have hC : Cf '' Ω = E ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show E (Cf x) ∈ Ω
      rw [hEC]
      exact hx
    · intro hy
      exact ⟨E y, hy, hCE y⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show MeasurableSet (Cf '' Ω)
    rw [hC]
    exact E.measurable hF.1
  · intro x hx
    have hx' : E x ∈ RP k r (fun v => n₁ v * g v * n₂ v) :=
      (mem_RP_iff n₁ g n₂ (fun v => (hN v).1) (fun v => (hN v).2.1) x).1 hx
    obtain ⟨m', ⟨hm'Γ, hm'Ω⟩, huniq⟩ := hF.2 (E x) hx'
    have hR : ∀ m, m ∈ realPts (fun v y => n₂ v *ᵥ Φ v y) Γ ↔ E m ∈ realPts Φ Γ :=
      fun m => mem_realPts_iff Φ Γ n₂ hu m
    have hM : ∀ m, E (mulP m x) = mulP (E m) (E x) := fun m =>
      funext fun v => conjM_lmulM (hui v) (m v) (x v)
    refine ⟨Cf m', ⟨(hR _).2 (by rw [hEC]; exact hm'Γ), ?_⟩, ?_⟩
    · show mulP (Cf m') x ∈ Cf '' Ω
      rw [hC]
      show E (mulP (Cf m') x) ∈ Ω
      rw [hM, hEC]
      exact hm'Ω
    · rintro m ⟨hmΓ, hmΩ⟩
      have hmΩ' : E (mulP m x) ∈ Ω := by
        have h0 : mulP m x ∈ Cf '' Ω := hmΩ
        rw [hC] at h0
        exact h0
      have h1 : E m = m' := huniq (E m) ⟨(hR m).1 hmΓ, by rw [← hM]; exact hmΩ'⟩
      rw [← h1, hCE]
  · have hmp : MeasurePreserving E (Measure.pi fun _ : ι => lam)
        (Measure.pi fun v => lam.map (e v)) :=
      haveI : ∀ v, SigmaFinite (lam.map (e v)) := fun v => (e v).sigmaFinite_map
      measurePreserving_pi _ _ (fun v => ⟨(e v).measurable, rfl⟩)
    show _ = Measure.pi (fun _ : ι => lam) (Cf '' Ω)
    rw [hC, hmp.measure_preimage_equiv]
    rfl
end GlobalTheory.DegVol.UnipConj
