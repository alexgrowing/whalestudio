import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

noncomputable section

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult

namespace GlobalTheory.CompanionTheory.FactorIso

theorem stIso : StIso := by
  intro G G₁ H _ _ _ _ _ _ π hπ j p hj hpj hc W hW
  haveI := hπ.complete
  have hu : IsUnitaryRep (π.comp j) := isUnitaryRep_comp hπ.unitary hj
  refine ⟨⟨W, hW.1.rep, isIrrUnitary_rep hu hW⟩, ?_⟩
  show isoPart hW.1.rep (π.comp j) ⊤ = ⊤
  have hsub : IsSubrep (π.comp j) (isoPart hW.1.rep (π.comp j) ⊤) := isSubrep_isoPart
  have hker : ∀ k, p k = 1 → ∀ v ∈ isoPart hW.1.rep (π.comp j) ⊤,
      π k v ∈ isoPart hW.1.rep (π.comp j) ⊤ := by
    intro k hk v hv
    have hle : isoPart hW.1.rep (π.comp j) ⊤ ≤
        (isoPart hW.1.rep (π.comp j) ⊤).comap (π k : H →ₗ[ℂ] H) :=
      isoPart_le (hsub.1.preimage (π k).continuous) fun T hT x =>
        apply_mem_isoPart (T := (π k).comp T) (mem_homIn_top.2 fun g y => by
          have hcomm : π k * π (j g) = π (j g) * π k := by
            rw [← map_mul, ← map_mul, (hc g k hk).eq]
          have hT' := hT.2 g y
          simp only [ContinuousLinearMap.comp_apply, hT', MonoidHom.comp_apply]
          exact DFunLike.congr_fun hcomm (T y)) x
    exact hle hv
  have hinv : IsSubrep π (isoPart hW.1.rep (π.comp j) ⊤) := by
    refine ⟨hsub.1, fun g v hv => ?_⟩
    have hg : g = j (p g) * ((j (p g))⁻¹ * g) := by group
    have h1 := hsub.2 (p g) _ (hker ((j (p g))⁻¹ * g) (by simp [hpj]) v hv)
    rw [hg, map_mul]
    simpa using h1
  rcases hπ.irred.2 _ hinv with h | h
  · exfalso
    apply hW.2.1
    rw [eq_bot_iff]
    intro w hw
    have hm : W.subtypeL ∈ homIn hW.1.rep (π.comp j) ⊤ := mem_homIn_top.2 fun _ _ => rfl
    have := apply_mem_isoPart hm ⟨w, hw⟩
    rw [h] at this
    simpa using this
  · exact h

end GlobalTheory.CompanionTheory.FactorIso

end
