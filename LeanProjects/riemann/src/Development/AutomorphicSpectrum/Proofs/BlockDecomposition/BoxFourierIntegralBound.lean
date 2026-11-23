import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff.FinFT

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem measurableSet_boxL (L : AddSubgroup (Af E)) (hLo : IsOpen (L : Set (Af E)))
    (c : Fin k → Af E) : MeasurableSet (boxL (L : Set (Af E)) c) := by
  have e : boxL (L : Set (Af E)) c =
      Set.pi Set.univ fun i => (fun x : Af E => x - c i) ⁻¹' (L : Set (Af E)) := by
    ext f; simp [boxL, Set.mem_pi]
  rw [e]
  exact MeasurableSet.univ_pi fun i =>
    (hLo.preimage (continuous_id.sub continuous_const)).measurableSet

theorem boxL_add_single (L : AddSubgroup (Af E)) (c f : Fin k → Af E) (i : Fin k) {a : Af E}
    (ha : a ∈ L) : f + Pi.single i a ∈ boxL (L : Set (Af E)) c ↔ f ∈ boxL (L : Set (Af E)) c := by
  have hl : ∀ j, (Pi.single i a : Fin k → Af E) j ∈ L := fun j => by
    by_cases h : j = i
    · subst h; simpa using ha
    · simp [Pi.single_eq_of_ne h]
  have e : ∀ j, (f + Pi.single i a : Fin k → Af E) j - c j = (f j - c j) + (Pi.single i a : Fin k → Af E) j :=
    fun j => by simp only [Pi.add_apply]; ring
  constructor
  · intro h j
    have h1 : (f + Pi.single i a : Fin k → Af E) j - c j ∈ L := h j
    rw [e] at h1
    exact (L.add_mem_cancel_right (hl j)).1 h1
  · intro h j
    change (f + Pi.single i a : Fin k → Af E) j - c j ∈ L
    rw [e]
    exact L.add_mem (h j) (hl j)

theorem sum_add_single (f z : Fin k → Af E) (i : Fin k) (a : Af E) :
    ∑ j, (f + Pi.single i a : Fin k → Af E) j * z j = ∑ j, f j * z j + a * z i := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

variable [IsTotallyComplex E]

theorem box_fourier {ψ : AddChar (Ad E) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (_hc : Continuous ψ)
    (L : AddSubgroup (Af E)) (_hLc : IsCompact (L : Set (Af E))) (hLo : IsOpen (L : Set (Af E)))
    (c z : Fin k → Af E) :
    ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧
    (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 →
      ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  have hm := measurableSet_boxL L hLo c
  refine ⟨?_, ?_⟩
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    have e : (fun f : Fin k → Af E => ‖(((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i))‖) = (boxL (L : Set (Af E)) c).indicator 1 := by
      funext f
      by_cases hf : f ∈ boxL (L : Set (Af E)) c <;> simp [hf, hψ]
    rw [e, integral_indicator_one hm]
  · intro hI i a ha
    have hinv : (nuFin E k).IsAddRightInvariant := by
      unfold nuFin; infer_instance
    have key := integral_add_right_eq_self (μ := nuFin E k)
      (fun f => (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i))) (Pi.single i a : Fin k → Af E)
    have e : ∀ f : Fin k → Af E,
        (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) (f + Pi.single i a) : ℝ) : ℂ) *
          ψ (sFin E (∑ j, (f + Pi.single i a : Fin k → Af E) j * z j)) =
        ψ (sFin E (a * z i)) * ((((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
          ψ (sFin E (∑ j, f j * z j))) := fun f => by
      rw [sum_add_single, map_add, AddChar.map_add_eq_mul]
      by_cases hf : f ∈ boxL (L : Set (Af E)) c
      · rw [Set.indicator_of_mem ((boxL_add_single L c f i ha).2 hf), Set.indicator_of_mem hf]
        ring
      · rw [Set.indicator_of_notMem (fun h => hf ((boxL_add_single L c f i ha).1 h)),
          Set.indicator_of_notMem hf]
        simp
    simp only [e] at key
    rw [integral_const_mul] at key
    exact mul_right_cancel₀ hI (key.trans (one_mul _).symm)

theorem box_fourier_main : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) :=
  fun h1 h2 L h3 h4 c z => box_fourier h1 h2 L h3 h4 c z

end GlobalTheory.CompanionTheory.CutOff.FinFT
end
