import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

private theorem regInf_iff {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (π : CuspSub F n) :
    RegInf n π.HasInfChar ↔ (CG.mk π).IsRegAlg := by
  refine Iff.trans (forall_congr' fun τ => ⟨?_, fun h => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, h⟩⟩) (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm
  rintro ⟨m, hm, h⟩
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
  exact h

private theorem regInf_iff_real {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (π : TR.CuspSub F n) :
    RegInf n (fun τ : F →+* ℂ => π.HasInfChar (InfinitePlace.mk τ)) ↔ π.IsRegAlg := by
  refine ⟨fun h v => ?_, fun h τ => h _⟩
  have := h v.embedding
  simpa only [InfinitePlace.mk_embedding] using this

theorem UpperTheory.V.Af.autBridge :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.AutBridge := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hC : ∀ [IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (regInf_iff π).1 hr, ha⟩
      · exact (not_both F h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (regInf_iff π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (not_both F hF h).elim
      · exact ⟨π, (regInf_iff_real π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (regInf_iff_real π).2 hr, ha⟩
  · rintro _ ⟨π, hr, -, ha⟩
    exact hC.2 ⟨π, hr, ha⟩
