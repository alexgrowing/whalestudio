import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepRealPointFockVectorSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointActsOnThetaFockVacuaByDetPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealComponentEqConjInverseRationalMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionPreservesHarmonicLetterPolynomiaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionHomogeneousCoeffMemAfterScalingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanFiniteTranslatesVacuumThetaFockVacuaStatement
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

namespace GlobalTheory.LevelSeries.ArchAct

theorem det_pow_mem {n : ℕ} (O : Subring ℂ) (z : ℂ) (g : GL (Fin n) ℂ)
    (h1 : ∀ x y, z * (g : Matrix (Fin n) (Fin n) ℂ) x y ∈ O)
    (h2 : ∀ x y, z * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O) (k : ℤ) :
    z ^ (n * k.natAbs) * (g : Matrix (Fin n) (Fin n) ℂ).det ^ k ∈ O := by
  have hdet : ∀ A : Matrix (Fin n) (Fin n) ℂ, (∀ x y, z * A x y ∈ O) → z ^ n * A.det ∈ O := by
    intro A hA
    have e : z ^ n * A.det = (z • A).det := by rw [Matrix.det_smul, Fintype.card_fin]
    rw [e, Matrix.det_apply]
    refine Subring.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem (Subring.prod_mem _ fun i _ => ?_) _
    simpa [Matrix.smul_apply] using hA (σ i) i
  have hinv : ((g : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ = ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det := by
    rw [eq_comm]
    apply eq_inv_of_mul_eq_one_left
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [Int.natAbs_natCast, zpow_natCast, pow_mul, ← mul_pow]
    exact pow_mem (hdet _ h1) _
  · rw [Int.natAbs_neg, Int.natAbs_natCast, _root_.zpow_neg, zpow_natCast, ← inv_pow, hinv, pow_mul, ← mul_pow]
    exact pow_mem (hdet _ h2) _

theorem real_act_harm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (wa : (D.host.E →+* ℂ) × ℕ → ℕ), W.rank = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) Dw.p) → IsLetters Dw lt → ∀ l c : ℕ, ∃ c' : ℕ, ∀ (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E) (O : Subring ℂ), γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → (∀ (τ : D.host.E →+* ℂ) x y, (l : ℂ) ^ c * τ (γ'.val x y) ∈ O ∧ (l : ℂ) ^ c * τ (γ'⁻¹.val x y) ∈ O) → ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) → ∃ Q' ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q'.coeff mo ∈ O) ∧ ∀ (M : ℕ) (e : AE D) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁, ((l : ℂ) ^ c') • om (a, 1) (stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q)) = stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q') := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw BW lt wa hrk hΨ hON hlt l c
  obtain ⟨k, hk⟩ := GlobalTheory.T.realPoint_acts_on_thetaFockVacua_by_det_power D ψ θ V W χV χW om ΛV ΛW sW f₀ hP Dw.p BW hON
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∑ ρ, ∑ j : Fin (Dw.mult ρ), wa (ρ, j) := ⟨_, rfl⟩
  refine ⟨c * d + ∑ τ, c * (V.rank * (k τ).natAbs), ?_⟩
  intro γ a γ' O hγ hrat ha hγa hden Q hQ hQO
  have hθ : IsInfFam θ := hP.1.inf
  choose σ hσ using GlobalTheory.T.realComponent_eq_conj_inverse_rationalMatrix D θ hθ V γ a γ' hγ hrat ha hγa
  let u : GlobalTheory.ExportSeries.GLR D V.rank := fun τ => Matrix.GeneralLinearGroup.map (σ τ) γ'⁻¹
  have hu : ∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) := fun τ => by
    rw [hσ τ]; rfl
  have hui : ∀ τ, (((u τ)⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
      (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ τ) := fun τ => by
    simp only [u, map_inv, inv_inv]; rfl
  have hden' : ∀ τ x y, (l : ℂ) ^ c * (((u τ)⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) x y ∈ O ∧
      (l : ℂ) ^ c * ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) x y ∈ O := fun τ x y => by
    rw [hui τ, hu τ, hσ τ]
    exact ⟨(hden (σ τ) x y).1, (hden (σ τ) x y).2⟩
  have hQ2 := GlobalTheory.T.fockSubstitution_preserves_harmonicLetterPolynomials D H Dw W.rank V.rank lt hrk hΨ hlt u wa Q hQ
  refine ⟨((l : ℂ) ^ (c * d + ∑ τ, c * (V.rank * (k τ).natAbs)) *
      ∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) •
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := W.rank) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)),
    GlobalTheory.smul_mem_HHa _ hQ2, ?_, ?_⟩
  · intro mo
    obtain ⟨mo', rfl⟩ := Finsupp.mapDomain_surjective lt.symm.surjective mo
    rw [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_rename_mapDomain _ lt.symm.injective]
    have hhom : (MvPolynomial.rename lt Q).IsHomogeneous d := by
      rw [hd]
      exact (GlobalTheory.PtId.isHomogeneous_of_rowDeg Dw.mult V.rank ℂ (fun τ i => wa (τ, i)) hQ.2.2).rename_isHomogeneous
    have hcO : ∀ mo, (MvPolynomial.rename lt Q).coeff mo ∈ O := fun mo => by
      obtain ⟨mo, rfl⟩ := Finsupp.mapDomain_surjective lt.surjective mo
      rw [MvPolynomial.coeff_rename_mapDomain _ lt.injective]
      exact hQO mo
    have h1 := GlobalTheory.T.fockSubstitution_homogeneous_coeff_mem_after_scaling D W.rank V.rank (fun _ => Dw.p) u O ((l : ℂ) ^ c) hden' d _ hhom hcO mo'
    have h2 : (l : ℂ) ^ (∑ τ, c * (V.rank * (k τ).natAbs)) *
        ∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ ∈ O := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Subring.prod_mem _ fun τ _ => ?_
      rw [← hu τ, pow_mul]
      exact det_pow_mem O _ (u τ) (fun x y => (hden' τ x y).2) (fun x y => (hden' τ x y).1) (k τ)
    convert mul_mem h2 h1 using 1
    rw [pow_add, pow_mul]
    ring
  · intro M e O₁ hM f hf
    obtain ⟨hft, hff⟩ := GlobalTheory.T.span_finiteTranslates_vacuum_thetaFockVacua D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O₁ hM f hf
    rw [GlobalTheory.T.weilRep_real_point_fockVector_substitution D ψ θ V W χV χW om ΛV ΛW sW f₀ hP Dw.p BW hON a ha u hu f hft hff, hk a ha f hft hff, stdF,
      GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, map_smul, MvPolynomial.rename_rename, Equiv.self_comp_symm,
      MvPolynomial.rename_id_apply, smul_smul]

end GlobalTheory.LevelSeries.ArchAct
