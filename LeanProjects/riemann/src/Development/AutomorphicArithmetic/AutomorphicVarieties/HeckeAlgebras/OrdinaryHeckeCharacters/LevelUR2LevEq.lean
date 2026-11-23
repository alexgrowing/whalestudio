import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevOut
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemHeckeLevelOfLocalComponentsMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem le_mem_under {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
  rw [map_natCast]

private theorem le_cmp_same {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w w' : Plc L}
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (g : Ga l L n)
    (hg : cmp n w g ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' g ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases h' : ((l : ℕ) : 𝓞 L) ∉ w'.asIdeal
  · have h0 : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
      rw [le_mem_under, ← h, ← le_mem_under]
      exact h'
    obtain ⟨_, x, rfl⟩ := g
    unfold CaseU.cmp at hg ⊢
    rw [dif_pos h0] at hg
    rw [dif_pos h']
    exact UpperTheory.mem_maximalCompact_of_under_eq L n x w w' h hg
  · unfold CaseU.cmp
    rw [dif_neg h']
    exact one_mem _

theorem UpperTheory.V.Hi.levelUR2LevEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ u : Ub n s, u ∈ (hset Q τ₀).lev K ↔ u ∈ (hset Q₀ τ₀).lev K₀ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ K₀ K h0 hK u
  have hem : ∀ q : Q₀.Q, False := fun q => by
    refine Q₀.notS q ?_
    rw [← h0, Q₀.range]
    exact Or.inr ⟨q, rfl⟩
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := levelUR2LevOut l L Ω s n hn V Q c m τ₀ K u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u (fun w hw => ?_) fun q => (hem q).elim
    by_cases hw' : w.under (𝓞 (Lp L)) ∈ V.S'
    · rw [Q.range] at hw'
      rcases hw' with hw' | ⟨q, hq⟩
      · exact (hw (h0 ▸ hw')).elim
      · refine le_cmp_same (w := Q.wq q) hq.symm _ ?_
        have h3 := h2 q
        rw [hK q] at h3
        exact h3
    · exact h1 w hw'
  · intro hu
    obtain ⟨h1, _⟩ := levelUR2LevOut l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K u (fun w hw => h1 w fun hw' => hw ?_) fun q => ?_
    · rw [Q.range]
      exact Or.inl (h0 ▸ hw')
    · rw [hK q]
      exact h1 _ (h0 ▸ Q.notS q)
