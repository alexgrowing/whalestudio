import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjVacuumNorm

theorem area_lamConj_pos (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M) :
    0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) := by
  have g1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hK | hK, hT, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc dl hc M ρ hD
  · obtain ⟨cc', δ', hc', -, hl⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc dl hc M ρ hK hD.2.1 hD.2.2 1 one_pos
    rw [hl]
    exact GlobalTheory.ConjJet.area_pos D g1 cc' δ' hc'
  · obtain ⟨cc', δ', hc', -, hl⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc dl hc M _ hK hD.2.1 hD.2.2 1 one_pos
    have hL : TaylorLogMetric.lamConj M (StandardLatticesGL3.rhoBar M ρ) (TaylorLogMetric.lamOf D cc dl) =
        (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg TaylorLogMetric.Tor.abelian₂ hT
    rw [← GlobalTheory.ConjJet.area_conj, ← hL, hl]
    exact GlobalTheory.ConjJet.area_pos D g1 cc' δ' hc'

theorem exists_extension_normSq_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (ρ : M →ₐ[ℚ] ℂ), TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → ∃ ρ' : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, (∀ x ∈ M, x ∈ TaylorLogMetric.Qbar ∧ StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ' x = StandardLatticesGL3.cj M ρ x) ∧ TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) ∧ 0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) ∧ ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (L₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L₀ → StandardLatticesGL3.SD D L₀' → Even (a * b) → ∀ F F₀ : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₀ L₀' F₀ → TaylorLogMetric.CoefIn D F₀ M → TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ' F) = TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) L₀ L₀') (TaylorLogMetric.fnConj D M ρ F₀) := by
  intro D cc dl t0 hc ht M _ ρ hD
  have g1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.ThetaConj.exists_cj_Qbar_eq M ρ
  have hle : ∀ x ∈ M, x ∈ TaylorLogMetric.Qbar := fun x hx =>
    mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : M)).algHom M.val)
  have he : ∀ x ∈ M, ρ' (TaylorLogMetric.liftM TaylorLogMetric.Qbar x) = ρ (TaylorLogMetric.liftM M x) := fun x hx =>
    (hρ' x (hle x hx) hx).symm
  have hl : TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) := by
    unfold TaylorLogMetric.lamConj
    rw [he (TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc dl)) hD.2.1, he (TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc dl)) hD.2.2]
  refine ⟨ρ', fun x hx => ⟨hle x hx, he x hx⟩, hl, area_lamConj_pos D cc dl hc M ρ hD, ?_⟩
  intro a b L L' L₀ L₀' h1 h2 h3 h4 hev F F₀ hF hF₀ hC
  obtain ⟨hQ, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D g1).2 cc dl hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc dl hc).2 M ρ hD.2.1 hD.2.2
  obtain ⟨n1, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc dl hc t0 ht a b L L' h1 h2 hev F hF
    TaylorLogMetric.Qbar ρ' hQ hA t' (hl ▸ ht')
  obtain ⟨n2, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc dl hc t0 ht a b L₀ L₀' h3 h4 hev F₀ hF₀
    M ρ hD hC t' ht'
  rw [n1, n2, hl]

end GlobalTheory.ConjVacuumNorm
