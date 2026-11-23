import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleOfCoproductCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRealizationMatrixStratifiedPhiModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasisStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem rel_gal_of_env {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l} {d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {s : Seed bk d ρ τ} (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A)
    (hε : ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)))
    (S : Strat bk d)
    (hSε : ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f)
    (g : ↥(GK K)) :
    ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
      ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA) := by
    obtain ⟨σ, ⟨h1, h2⟩, -⟩ := En.univ (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    have hn := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q (ainfObj K) En.inl En.inl En.inr bk.ι σ
      (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    obtain ⟨Fk, hFk⟩ := hn.1
    have hr := hn.2 Fk hFk
    have hr' : ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
        ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), ht.Rel (BK.hf bk.ι X) f₁ f₂
          ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) → f₁ = bk.ι → f₂ = (ainfHom K g).comp bk.ι →
          ht.Rel (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ hr h1 h2
    have e : S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), S.ε f₁ f₂ = ε.map σ.f → f₁ = bk.ι →
          f₂ = (ainfHom K g).comp bk.ι → S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ (hSε (ainfObj K) σ) h1 h2
    have hm : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk = (ε.map σ.f).map bk.iA :=
      Matrix.ext fun i j => hFk.ext (ε i j)
    have hM : (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA = (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk :=
      (congrArg (fun M => Matrix.map M bk.iA) e).trans hm.symm
    exact Eq.mpr (congrArg (ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)) hM) hr'

theorem exists_strat_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ),
    Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  intro l _ K bk τ hτ d ρ hρ s ht

  obtain ⟨En⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk bk.prism (bk.toP bk.E) (bk.toP X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk bk.prism (Hom.id bk.prism))

  obtain ⟨En₂⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)
  obtain ⟨⟨tb⟩, -⟩ := GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂

  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_comparison_matrix_prismCoproduct l K bk d ρ τ s ht hτ hρ En
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr (Digits l) tb 0 ε
    (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    ((congrArg (fun c => c • ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀))
      (pow_zero ((l : ℕ) : Disc l (BK.hf En.inl X) bk.ρ₀))).trans (one_smul _ _)).symm
  have hc := GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism l K bk d ρ τ s ht En ε hε
  obtain ⟨S, hSa, hSA, hSε⟩ := GlobalTheory.T.stratifiedPhiModule_of_coproduct_cocycle l K bk En d (ht.a + s.N) ht.b ht.A ht.A' ht.A_mul ε hφ hc
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_realization_matrix_stratifiedPhiModule l K bk d ρ τ s ht hτ S hSa hSA (rel_gal_of_env ht En ε hε S hSε)
  exact ⟨S, T, hT⟩

end GlobalTheory.BSP
