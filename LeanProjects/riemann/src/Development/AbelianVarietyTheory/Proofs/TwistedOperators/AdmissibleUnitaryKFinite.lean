import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCUnitary

variable {n : ℕ} {ε : Fin n → Bool}

theorem maxCpt_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.maxCpt (UJset ε) = Kset ε := by
  ext g
  refine ⟨fun hg => ⟨hg.2, ?_⟩, fun hg => ⟨mem_UJset_of_mem_Kset hg, hg.1⟩⟩
  have h1 : g * gᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hg.2
  have h2 : gᴴ * Jm ε * g = Jm ε := hg.1
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h2]
    _ = Jm ε * g := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, h1, Matrix.one_mul]

theorem isLinRed_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.IsLinRed (UJset ε) := by
  have hW : IsIsoFlag ε (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => (⊥ : Submodule ℂ (Fin n → ℂ))) :=
    ⟨rfl, monotone_const, fun i => i.elim0, fun x hx y _ => by
      rw [(Submodule.mem_bot ℂ).1 hx]; simp⟩
  have h := (GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε 0 _ _ hW (fun i => i.elim0)).1
  rwa [leviOne_zero hW, mats_top] at h

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isKStable_iff {S : Submodule ℂ H} : GlobalTheory.LinRed.IsKStable (UJset ε) π S ↔ IsKStableOn ε π S := by
  unfold GlobalTheory.LinRed.IsKStable IsKStableOn
  rw [maxCpt_UJset]

theorem isKTypeOf_map {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε π Λ S) (T : H →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ w ∈ S, T (π k w) = π k (T w)) : S.map T = ⊥ ∨ IsKTypeOf ε π Λ (S.map T) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hv⟩, hdom⟩ := hS
  have hpre : ∀ S' : Submodule ℂ H, IsKStableOn ε π S' → IsKStableOn ε π (S ⊓ S'.comap T) :=
    fun S' h k hk w hw => ⟨hst k hk w hw.1, by
      have : T (π k w) ∈ S' := by rw [hT k hk w hw.1]; exact h k hk _ hw.2
      exact this⟩
  have hbot : IsKStableOn ε π ⊥ := fun k _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _
  rcases hirr _ inf_le_left (hpre ⊥ hbot) with h0 | h1
  · right
    have hinj : ∀ w ∈ S, T w = 0 → w = 0 := fun w hw h => by
      have : w ∈ S ⊓ (⊥ : Submodule ℂ H).comap T := ⟨hw, h⟩
      rwa [h0, Submodule.mem_bot] at this
    refine ⟨inferInstance, ?_, fun S' hle hS' => ?_, ⟨T v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h),
      fun θ hθ => ?_⟩, ?_⟩
    · rintro k hk _ ⟨w, hw, rfl⟩
      exact ⟨π k w, hst k hk w hw, hT k hk w hw⟩
    · rcases hirr _ inf_le_left (hpre S' hS') with h | h
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := hle hx
        have : w ∈ S ⊓ S'.comap T := ⟨hw, hx⟩
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]; exact Submodule.zero_mem _
      · exact Or.inr (le_antisymm hle (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h)))
    · rw [← hT _ hθ v hvS, hv θ hθ, map_smul]
    · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
      refine hdom μ w hw (fun h => hw0 (by rw [h, map_zero])) fun θ hθ => ?_
      refine sub_eq_zero.1 (hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw)) ?_)
      rw [map_sub, map_smul, hT _ hθ w hw, hwt θ hθ, sub_self]
  · exact Or.inl (eq_bot_iff.2 (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h1)))

theorem isAdmOn_iff [CompleteSpace H] : GlobalTheory.LinRed.IsAdmOn (UJset ε) π ↔ IsAdmRep ε π := by
  unfold GlobalTheory.LinRed.IsAdmOn IsAdmRep
  simp only [isKStable_iff]
  rw [maxCpt_UJset]
  refine and_congr_right fun h1 => and_congr_right fun h2 => and_congr_right fun h3 => ?_
  obtain ⟨hA, hB⟩ := GlobalTheory.KTypeHighest.ktype_highest_weight n ε H π h1 h2 h3
  refine ⟨fun h Λ => ?_, fun h S hfin hst hirr => ?_⟩
  · by_cases he : ∃ S₀, IsKTypeOf ε π Λ S₀
    · obtain ⟨S₀, hS₀⟩ := he
      haveI := h S₀ hS₀.1 hS₀.2.1 hS₀.2.2.1
      refine Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S' | ∃ T : H →ₗ[ℂ] H, S' = S₀.map T ∧
        ∀ k ∈ Kset ε, ∀ w ∈ S₀, T (π k w) = π k (T w)}) fun S hS => ?_)
      obtain ⟨B, hB1, hB2⟩ := hB Λ S₀ S hS₀ hS.2
      exact ⟨B, hB2.symm, fun k hk w _ => hB1 k hk w⟩
    · exact Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le fun S hS => absurd ⟨S, hS.2⟩ he)
  · by_cases h0 : S = ⊥
    · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le ?_)
      rintro _ ⟨T, rfl, -⟩
      rw [h0, Submodule.map_bot]
    · obtain ⟨Λ, hΛ⟩ := hA S hfin h0 hst hirr
      haveI := h Λ
      refine Submodule.finiteDimensional_of_le (S₂ := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S}) (sSup_le ?_)
      rintro _ ⟨T, rfl, hT⟩
      rcases isKTypeOf_map hΛ T hT with hb | hk
      · rw [hb]; exact bot_le
      · exact le_sSup ⟨le_top, hk⟩

theorem admissible_and_analytic : (GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsAdmRep ε σ) ∧ (GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → ∀ v w : H, IsKFin ε π v → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ) := by
  refine ⟨fun h n ε H _ _ _ σ hU hI => isAdmOn_iff.1 (h n _ (isLinRed_UJset ε) H σ hU hI),
    fun h n ε H _ _ _ π hπ v w hv => h n _ (isLinRed_UJset ε) H π (isAdmOn_iff.2 hπ) v w ?_⟩
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, h2, isKStable_iff.2 h3⟩

end GlobalTheory.HCUnitary
