import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB
open GlobalTheory.WeilM GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.MultSupp

theorem vanish_of_mult_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ℓ : Fin a → k), ℓ ≠ 0 → ∀ (ψv : AddChar k ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →ₗ⋆[ℂ] ℂ,
      (∀ (z : Fin d → k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k)), Ψ'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ.1 Y) → L Ψ' = L Ψ) →
      ∀ Ψ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Matrix.vecMul ℓ Y = 0 → Ψ.1 Y = 0) → L Ψ = 0 := by
  intro k _ _ _ _ a d ℓ _ ψv hψc hψ1 L hinv Ψ hΨ
  have hlc : IsLocallyConstant ψv := SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.isLocallyConstant_addChar ψv hψc
  obtain ⟨t₀, ht₀⟩ : ∃ t, ψv t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ1 (by ext t; simpa using h t)
  have key : ∀ Y₀ : Matrix (Fin a) (Fin d) k, Matrix.vecMul ℓ Y₀ ≠ 0 → ∃ V : Set (Matrix (Fin a) (Fin d) k),
      IsOpen V ∧ Y₀ ∈ V ∧ ∀ g (hg : g ∈ SB (Matrix (Fin a) (Fin d) k)), (∀ Y, g Y ≠ 0 → Y ∈ V) → L ⟨g, hg⟩ = 0 := by
    intro Y₀ hY₀
    obtain ⟨j, hj⟩ : ∃ j, Matrix.vecMul ℓ Y₀ j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hY₀ (funext h)
    set z : Fin d → k := Pi.single j (t₀ / Matrix.vecMul ℓ Y₀ j) with hz
    set f : Matrix (Fin a) (Fin d) k → ℂ := fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) with hf
    have hfc : Continuous (fun Y : Matrix (Fin a) (Fin d) k => ℓ ⬝ᵥ (Y *ᵥ z)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    have hflc : IsLocallyConstant f := hlc.comp_continuous hfc
    have hf0 : f Y₀ = ψv t₀ := by
      simp only [hf, Matrix.dotProduct_mulVec, hz, dotProduct_single]
      rw [mul_div_cancel₀ _ hj]
    refine ⟨f ⁻¹' {ψv t₀}, hflc.isOpen_fiber _, hf0, ?_⟩
    intro g hg hsupp
    have hfg : (fun Y => f Y * g Y) = (ψv t₀) • g := by
      funext Y
      by_cases h : g Y = 0
      · simp [h]
      · have : f Y = ψv t₀ := hsupp Y h
        simp [this]
    have hmem : (fun Y => f Y * g Y) ∈ SB (Matrix (Fin a) (Fin d) k) := by
      rw [hfg]; exact Submodule.smul_mem _ _ hg
    have h1 := hinv z ⟨g, hg⟩ ⟨_, hmem⟩ rfl
    have e : (⟨fun Y => f Y * g Y, hmem⟩ : SB (Matrix (Fin a) (Fin d) k)) = (ψv t₀) • ⟨g, hg⟩ :=
      Subtype.ext hfg
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
    have hc : (starRingEnd ℂ) (ψv t₀) ≠ 1 := by
      intro h
      apply ht₀
      simpa using congrArg (starRingEnd ℂ) h
    have h2 : ((starRingEnd ℂ) (ψv t₀) - 1) * L ⟨g, hg⟩ = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc)
  have hΨ' : ∀ Y : Function.support Ψ.1, Matrix.vecMul ℓ (Y : Matrix (Fin a) (Fin d) k) ≠ 0 :=
    fun Y h => Y.2 (hΨ _ h)
  choose V hVo hYV hVL using fun Y : Function.support Ψ.1 => key Y (hΨ' Y)
  have hcl : IsClosed (Function.support Ψ.1) := by
    have : Function.support Ψ.1 = (Ψ.1 ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (Ψ.2.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support Ψ.1) := by
    have := Ψ.2.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun i : Function.support Ψ.1 => V i) hVo
    (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, hYV _⟩)
  have hspan := GlobalTheory.CoverSB.mem_span_of_cover k (Fin a) (Fin d) t (fun i => V i.1) (fun i => hVo _) Ψ.1 Ψ.2
    (fun Y hY => by
      obtain ⟨i, hi, hYi⟩ := Set.mem_iUnion₂.1 (ht hY)
      exact ⟨⟨i, hi⟩, hYi⟩)
  have hle : Submodule.span ℂ {g | g ∈ SB (Matrix (Fin a) (Fin d) k) ∧ ∃ i : t, ∀ Y, g Y ≠ 0 → Y ∈ V i.1} ≤
      (LinearMap.ker L).map (SB (Matrix (Fin a) (Fin d) k)).subtype := by
    rw [Submodule.span_le]
    rintro g ⟨hg, i, hi⟩
    exact ⟨⟨g, hg⟩, hVL i.1 g hg hi, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hle hspan
  have : x = Ψ := Subtype.ext hxe
  rw [← this]
  exact hx

end GlobalTheory.MultSupp
