import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSSProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HarmFin
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem harmSS_fix {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} {ω : Co Ξ q} (h : IsLev U Ξ ω) {u : GL (Fin a) (Af E)} (hu : u ∈ U) :
    trans u ω = ω := by
  ext X
  have hle : Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v} ≤
      LinearMap.eqLocus ((act (.fin u) : Module.End ℂ (Sm E a)).rTensor (Fin Ξ.d → ℂ)) LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, v, hφ, rfl⟩
    show LinearMap.rTensor _ _ (φ ⊗ₜ[ℂ] v) = φ ⊗ₜ[ℂ] v
    rw [LinearMap.rTensor_tmul, hφ.2.1 u hu]
  exact hle (h.val X)

theorem UpperTheory.V.Cj.H.harmSS :
    UpperTheory.V.Cj.H.HarmSS := by
  intro E _ _ _ a ha Ξ r m q M hM hT N hNM hN
  obtain ⟨ρ, B, hρ, hpos, hc⟩ := UpperTheory.V.Cj.H.coForm E a ha Ξ r q
  have hsq : ∀ ω ∈ M, Val (sqSub E a r) ω := fun ω h => ((hM ω).1 h).sq
  obtain ⟨N', h1, h2, h3, h4⟩ := UpperTheory.V.Cj.H.absSS (GL (Fin a) (Af E)) (Co Ξ q) ρ M B (hpos M hsq)
    (fun g v hv => by rw [hρ]; exact hT g v hv)
    (fun g => by
      obtain ⟨c, h⟩ := hc g
      exact ⟨c, fun v hv w hw => by rw [hρ, hρ]; exact h v w (hsq v hv) (hsq w hw)⟩)
    (fun v hv => by
      obtain ⟨U, hUo, hUc, hU⟩ := ((hM v).1 hv).lev
      exact ⟨U, hUo, hUc, fun u hu => by rw [hρ]; exact harmSS_fix hU hu⟩)
    (fun U hU => by
      have h := UpperTheory.V.Cj.H.harmFin E a Ξ r m q U hU
      have e : {v : Co Ξ q | v ∈ M ∧ ∀ u ∈ U, ρ u v = v} = {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω} := by
        ext v
        simp only [Set.mem_setOf_eq, hM, hρ]
      rw [e]
      exact h)
    N hNM (fun g v hv => by rw [hρ]; exact hN g v hv)
  exact ⟨N', h1, fun x ω h => by rw [← hρ]; exact h2 x ω h, h3, h4⟩
