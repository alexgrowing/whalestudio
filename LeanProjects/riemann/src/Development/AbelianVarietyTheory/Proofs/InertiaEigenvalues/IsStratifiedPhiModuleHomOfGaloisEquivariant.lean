import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleEquivariantMatrixCommuteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelopeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixEquivariantHomCommFrobeniusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isStratHom_of_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d)
    (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) →
    ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → IsStratHom S S' Y := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY
  have hφ := GlobalTheory.T.stratPeriodMatrix_equivariant_hom_comm_frobenius l K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY
  have hgal := GlobalTheory.T.stratifiedPhiModule_equivariant_matrix_commute l K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY
  have hfr : IsFrame bk bk.prism (bk.toP bk.E) (bk.toP X) := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk bk.prism (Hom.id _)
  obtain ⟨En⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk bk.prism _ _ hfr
  have h1 := GlobalTheory.T.stratifiedHom_comparison_compatible_envelope l K bk En d d' S S' Y hφ hgal
  refine ⟨hφ, ?_⟩
  intro B f₁ g₁
  obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := En.univ B f₁ g₁
  subst hk1 hk2
  have e : ∀ {m n : Type} (M : Matrix m n bk.S) (h : Hom bk.prism En.Q),
      (M.map (BK.hf h)).map k.f = M.map (BK.hf (k.comp h)) := fun M h => rfl
  have h2 : (S'.ε En.inl En.inr * Y.map (BK.hf En.inr)).map k.f =
      (Y.map (BK.hf En.inl) * S.ε En.inl En.inr).map k.f := congrArg (fun M => M.map k.f) h1
  have m1 := Matrix.map_mul (f := k.f) (L := S'.ε En.inl En.inr) (M := Y.map (BK.hf En.inr))
  have m2 := Matrix.map_mul (f := k.f) (L := Y.map (BK.hf En.inl)) (M := S.ε En.inl En.inr)
  have n1 := S'.ε_nat k En.inl En.inr
  have n2 := S.ε_nat k En.inl En.inr
  exact (congrArg₂ (· * ·) n1.symm (e Y En.inr).symm).trans
    (m1.symm.trans (h2.trans (m2.trans (congrArg₂ (· * ·) (e Y En.inl) n2))))

end GlobalTheory
