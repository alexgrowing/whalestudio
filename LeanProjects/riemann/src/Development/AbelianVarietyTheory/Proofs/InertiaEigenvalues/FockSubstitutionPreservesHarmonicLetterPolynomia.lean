import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLettersHarmMemHHa
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.FockSubstHarm

theorem isLetters_unique {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) {lt lt' : LtN Dw n ≃ FVar D m n}
    (h : IsLetters Dw lt) (h' : IsLetters Dw lt') : lt = lt' := by
  refine Equiv.ext fun ℓ => ?_
  obtain ⟨hb, h1⟩ := h ℓ
  obtain ⟨hb', h1'⟩ := h' ℓ
  have hpsi : ∀ ρ, InPsi H (tauE D ρ) := fun ρ => (hΨ _).2 ⟨ρ, rfl⟩
  have hnot : ∀ ρ, ¬ InPsi H (ComplexEmbedding.conjugate (tauE D ρ)) := fun ρ hc =>
    (GlobalTheory.Harm.not_mem_hostType_iff H (ComplexEmbedding.conjugate (tauE D ρ))).2
      (by have e := ComplexEmbedding.involutive_conjugate _ (tauE D ρ); have := hpsi ρ; rw [← e] at this; exact this) hc
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h1' with ⟨e1', e2'⟩ | ⟨e1', e2'⟩
  · have hρ : (lt ℓ).1 = (lt' ℓ).1 := GlobalTheory.StdRat.tauE_injective D (e1.symm.trans e1')
    exact Prod.ext hρ (Prod.ext (Fin.ext (by omega)) (hb.trans hb'.symm))
  · exact absurd (e1 ▸ hpsi (lt ℓ).1 : InPsi H ℓ.1) (e1' ▸ hnot (lt' ℓ).1)
  · exact absurd (e1' ▸ hpsi (lt' ℓ).1 : InPsi H ℓ.1) (e1 ▸ hnot (lt ℓ).1)
  · have hρ : (lt ℓ).1 = (lt' ℓ).1 :=
      GlobalTheory.StdRat.tauE_injective D ((ComplexEmbedding.involutive_conjugate _).injective (e1.symm.trans e1'))
    exact Prod.ext hρ (Prod.ext (Fin.ext (by omega)) (hb.trans hb'.symm))

end GlobalTheory.FockSubstHarm

noncomputable section
namespace GlobalTheory.FockSubstHarm

theorem rename_comp_fockSubst {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (u : GlobalTheory.ExportSeries.GLR D n) :
    (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl)).comp
        (GlobalTheory.ExportSeries.fockSubst (m := Dw.p + Dw.q) (fun _ => Dw.p) u) =
      (GlobalTheory.Harm.colSubst (p := Dw.p) (q := Dw.q)
        (fun t => (((u ((GlobalTheory.FockLetters.tauPsi hΨ).symm t))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        (fun t => ((u ((GlobalTheory.FockLetters.tauPsi hΨ).symm t) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).comp
        (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl)) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨ρ, i, b⟩ := v
  induction i using Fin.addCases with
  | left i =>
    have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < (fun _ => Dw.p) ρ := by simp
    simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_pos hi, map_sum, map_mul,
      MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [GlobalTheory.FockLetters.fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans,
      Equiv.refl_apply, finSumFinEquiv_symm_apply_castAdd]
    erw [GlobalTheory.Harm.colSubst_X_xVar]
    simp [GlobalTheory.Harm.xForm_apply]
  | right j =>
    have hj : ¬ ((Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q)) : ℕ) < (fun _ => Dw.p) ρ := by simp
    simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_neg hj, map_sum, map_mul,
      MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [GlobalTheory.FockLetters.fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans,
      Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd]
    erw [GlobalTheory.Harm.colSubst_X_yVar]
    simp [GlobalTheory.Harm.yForm_apply]

theorem rename_fockSubst_mem_HHa : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (lt : LtN Dw n ≃ FVar D m n),
    m = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → IsLetters Dw lt →
    ∀ (u : GlobalTheory.ExportSeries.GLR D n) (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (Q : MvPolynomial (LtN Dw n) ℂ),
      Q ∈ HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) →
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := m) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)) ∈
        HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) := by
  intro D H Dw m n lt hm hΨ hlt u wa Q hQ
  subst hm
  obtain rfl : lt = GlobalTheory.FockLetters.letterEquiv Dw hΨ rfl :=
    isLetters_unique Dw hΨ hlt (GlobalTheory.FockLetters.isLetters_letterEquiv Dw hΨ rfl)
  rcases GlobalTheory.Harm.HHa_eq_zero_or_rowHighest (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate D.host.E)
      (GlobalTheory.Harm.not_mem_hostType_iff H) (fun _ => GlobalTheory.Harm.mult_of_mem Dw) (fun _ => GlobalTheory.Harm.mult_conjEmb_of_mem Dw)
      (n := n) (K := ℂ) (fun τ i => wa (τ, i)) with h0 | ⟨k, k', -, hiff⟩
  · have hQ0 := h0 Q hQ
    rw [hQ0] at hQ ⊢
    rw [map_zero, map_zero, map_zero]
    exact hQ
  · rw [hiff] at hQ ⊢
    change MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n) _ ∈ _ at hQ
    change MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n) _ ∈ _
    have e1 : ∀ P : MvPolynomial (FVar D (Dw.p + Dw.q) n) ℂ,
        MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n)
          (MvPolynomial.rename (GlobalTheory.FockLetters.letterEquiv Dw hΨ rfl).symm P) =
        MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl) P := fun P => by
      rw [MvPolynomial.rename_rename]
      refine congrArg (fun f => MvPolynomial.rename f P) (funext fun v => ?_)
      simp [GlobalTheory.FockLetters.letterEquiv]
    have e2 : MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ rfl)
        (MvPolynomial.rename (GlobalTheory.FockLetters.letterEquiv Dw hΨ rfl) Q) =
        MvPolynomial.rename (GlobalTheory.Harm.thetaLetterEquiv Dw n) Q := by
      rw [MvPolynomial.rename_rename]
      refine congrArg (fun f => MvPolynomial.rename f Q) (funext fun v => ?_)
      simp [GlobalTheory.FockLetters.letterEquiv]
    rw [e1, ← AlgHom.comp_apply, rename_comp_fockSubst, AlgHom.comp_apply, e2]
    exact GlobalTheory.Harm.colSubst_mem_rowHighest (fun t => Units.inv_mul _) hQ

end GlobalTheory.FockSubstHarm
