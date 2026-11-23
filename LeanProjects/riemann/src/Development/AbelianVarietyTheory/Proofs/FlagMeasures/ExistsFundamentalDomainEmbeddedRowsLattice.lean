import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.RowDomain

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

noncomputable def rowLat (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule ℤ (VecInf E k) :=
  AddSubgroup.toIntSubmodule
  { carrier := {z | ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b)}
    zero_mem' := ⟨0, fun y _ => by simp only [zero_dotProduct]; exact Λ₀.zero_mem, by funext w b; simp⟩
    add_mem' := by
      rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
      refine ⟨σ + τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.add_mem (hσ y hy) (hτ y hy)
      convert this using 1
      funext _; simp
    neg_mem' := by
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨-τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.neg_mem (hτ y hy)
      convert this using 1
      funext _; simp }

theorem mem_rowLat {E : Type} [Field E] [NumberField E] {k : ℕ} {Λ₀ : Submodule (𝓞 E) (Fin 1 → E)}
    {Λ' : Submodule (𝓞 E) (Fin k → E)} {z : VecInf E k} : z ∈ rowLat E k Λ₀ Λ' ↔
    ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b) := by
  rfl

theorem hasCov_rowLat (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E) (k : ℕ)
    (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)) (h₀ : Submodule.IsLattice E Λ₀)
    (h' : Submodule.IsLattice E Λ') : GlobalTheory.HomCovolume.HasCov volume (rowLat E k Λ₀ Λ')
      (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) := by
  classical

  let e : VecInf E k ≃L[ℝ] (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (LinearEquiv.piCongrRight fun _ : InfinitePlace E =>
      (LinearEquiv.funUnique (Fin 1) ℝ (Fin k → ℂ)).symm).toContinuousLinearEquiv
  have hes : ∀ x w b, e.symm x w b = x w 0 b := fun _ _ _ => rfl
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_pi fun _ : InfinitePlace E =>
      MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) (Fin k → ℂ))
  let L' : Submodule ℤ (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (rowLat E k Λ₀ Λ').comap ((e.symm : _ →L[ℝ] VecInf E k).toLinearMap.restrictScalars ℤ)
  have hL' : ∀ z, z ∈ L' ↔ e.symm z ∈ rowLat E k Λ₀ Λ' := fun _ => Iff.rfl
  refine GlobalTheory.HomCovolume.HasCov.of_measurePreserving e hmp (L' := L')
    (fun x => by rw [hL', ContinuousLinearEquiv.symm_apply_apply]) ?_
  have hpos : ∀ j, 0 < detNorm E j (oneInf E j) := fun j => by rw [detNorm_oneInf]; exact one_pos
  obtain ⟨hd, hz, hc⟩ := GlobalTheory.HomCovolume.homCovolume E hE 1 k Λ₀ Λ' h₀ h' (oneInf E 1) (oneInf E k)
    (hpos 1) (hpos k) L' (by
      intro z
      rw [hL', mem_rowLat]
      simp only [of_oneInf, inv_one]
      constructor
      · rintro ⟨τ, hτ, hzτ⟩
        refine ⟨Matrix.of fun _ b => τ b, fun y hy => ?_, fun w => ?_⟩
        · exact hτ y hy
        · ext i b
          fin_cases i
          have := congrFun (congrFun hzτ w) b
          simpa [hes] using this
      · rintro ⟨T, hT, hTz⟩
        refine ⟨fun b => T 0 b, fun y hy => ?_, ?_⟩
        · convert hT y hy using 1
          funext i
          fin_cases i
          rfl
        · funext w b
          have := congrFun (congrFun (hTz w) 0) b
          simpa [hes] using this)
  exact ⟨hd, hz, by rw [hc, pow_one]⟩

theorem rowDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsLattice E Λ₀ → Submodule.IsLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  obtain ⟨hd, hz, hc⟩ := hasCov_rowLat E hE k Λ₀ Λ' h₀ h'

  let b := Module.Free.chooseBasis ℤ (rowLat E k Λ₀ Λ')
  have hspan := b.ofZLatticeBasis_span ℝ
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (VecInf E k))
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ?_, fun T => ?_, fun T τ hτ hT hT' => ?_⟩
  · rw [← hc, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF]
    have hfin : (volume : Measure (VecInf E k)) (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
    exact (ofReal_measureReal hfin).symm
  · obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T
    have hvL : (v : VecInf E k) ∈ rowLat E k Λ₀ Λ' := hspan.le v.2
    obtain ⟨τ, hτ, hvτ⟩ := mem_rowLat.1 hvL
    refine ⟨τ, hτ, ?_⟩
    convert hv using 1
    rw [Submodule.vadd_def, vadd_eq_add, hvτ]
    funext w b
    simp [add_comm]
  · have hzL : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) ∈
        Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) :=
      hspan.ge (mem_rowLat.2 ⟨τ, hτ, rfl⟩)
    have hu := (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T).unique
      (y₁ := ⟨_, hzL⟩) (y₂ := 0) (by
        rw [Submodule.vadd_def, vadd_eq_add]
        convert hT' using 1
        funext w b
        simp [add_comm]) (by simpa using hT)
    have h0 : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) = 0 :=
      congrArg Subtype.val hu
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    funext b
    have := congrFun (congrFun h0 w) b
    simpa using this

end GlobalTheory.RowDomain
