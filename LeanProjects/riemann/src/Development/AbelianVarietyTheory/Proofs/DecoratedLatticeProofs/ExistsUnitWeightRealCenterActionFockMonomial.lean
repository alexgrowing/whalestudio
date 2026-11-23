import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergCombStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CenFockWt

theorem central_wt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  intro D ψ θ hθ S T x y hx hy k hk
  classical
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  have hvth : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_realCentre_character_on_definiteVacuum D ψ θ hθ S T x y hx hy k hk
  set ζ : GA D S → D.what₂.Tau → ℂ := fun z τ =>
    if h : 0 < S.rank then compAt θ τ (Formalism.L2.Theta.mt S z) ⟨0, h⟩ ⟨0, h⟩ else 1 with hζdef
  set μ : GA D S → D.what₂.Tau → ℂ := fun z τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ z τ)⁻¹ else ζ z τ with hμdef
  set deg : D.what₂.Tau → (FVar D T.rank S.rank →₀ ℕ) → ℕ := fun τ α => ∑ v ∈ α.support with v.1 = τ, α v with hdeg
  have hζ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ,
      ‖ζ z τ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ z τ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
    intro z hz hzc τ
    obtain ⟨ζ', h1, h2⟩ := GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar D θ hθ S x hx z hz hzc τ
    by_cases h : 0 < S.rank
    · have e : ζ z τ = ζ' := by
        simp only [hζdef, dif_pos h, h2, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [e]; exact ⟨h1, h2⟩
    · have e : ζ z τ = 1 := by simp only [hζdef, dif_neg h]
      refine ⟨by rw [e, norm_one], ?_⟩
      ext i
      exact absurd i.2 (by omega)
  have hμ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ, ‖μ z τ‖ = 1 := by
    intro z hz hzc τ
    simp only [hμdef]
    split_ifs
    · rw [norm_inv, (hζ z hz hzc τ).1, inv_one]
    · exact (hζ z hz hzc τ).1
  have hT1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have comb_smul : ∀ (cc : WO S T →₀ ℂ) (a : ℂ) (g : WO S T → ℂ), comb ψ S T cc (a • g) = a • comb ψ S T cc g := by
    intro cc a g
    unfold comb
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have : heisO ψ S T u (a • g) = a • heisO ψ S T u g := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, smul_comm]
  refine ⟨fun α z => c z * ∏ τ, μ z τ ^ deg τ α, ?_, ?_⟩
  · intro α z hz hzc
    refine ⟨?_, ?_⟩
    · rw [norm_mul, (hc z hz hzc).1, one_mul, norm_prod]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [norm_pow, hμ z hz hzc τ, one_pow]
    · intro cc hcc
      set F := pureTensorO ψ θ S T x.s y.s x.B y.B with hF
      have hcomb : ∀ g, comb ψ S T cc g = ∑ i : Fin cc.support.card,
          cc (cc.support.equivFin.symm i) • heisO ψ S T (cc.support.equivFin.symm i) g := by
        intro g
        unfold comb
        rw [← Finset.sum_coe_sort]
        exact (Equiv.sum_comp cc.support.equivFin.symm (fun u => cc u • heisO ψ S T u g)).symm
      have key1 : ∀ g, IsThetaFunO ψ S T g → ∀ P, F (comb ψ S T cc g) P = comb ψ S T cc (F g P) := by
        intro g hg P
        rw [hcomb, hcomb]
        exact (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hstd hθ x.s y.s x.B y.B g hg cc.support.card _ _
          (fun i => hcc _ (Finset.coe_mem _)) P).1.symm
      have hop := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B (fun τ => ζ z τ • x.B τ)
        y.s y.s y.B y.B z 1
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.smul_mul, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.one_mul]) k.vac hvth (MvPolynomial.monomial α 1)
      rw [key1 k.vac hvth, GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb D ψ S T χS χT k.om hW z hz cc hcc _ hop.1, hop.2, (hc z hz hzc).2,
        GlobalTheory.FiniteFock.pureTensorO_smul,
        GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial D ψ θ hstd hθ S T x y hx hy k.vac hvth (ζ z) (fun τ => (hζ z hz hzc τ).1) α,
        smul_smul, comb_smul]
  · intro χ
    by_cases hne : ∃ α₀, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → c z * ∏ τ, μ z τ ^ deg τ α₀ = χ z
    · obtain ⟨α₀, hα₀⟩ := hne
      refine (GlobalTheory.T.finite_monomials_with_prescribed_placeDegree D T.rank S.rank (fun τ => deg τ α₀)).subset fun α hα τ => ?_
      show deg τ α = deg τ α₀
      by_cases hr : 0 < S.rank ∧ 0 < T.rank
      · obtain ⟨z, hz, hzc, h1, h2⟩ := GlobalTheory.T.exists_central_realPoint_unit_scalar_single_place D θ hθ S τ (Complex.exp Complex.I) (by simpa using Complex.norm_exp_ofReal_mul_I 1)
        have e := (hα z hz hzc).trans (hα₀ z hz hzc).symm
        have hc0 : c z ≠ 0 := by
          intro h0
          have := (hc z hz hzc).1
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        have e2 := mul_left_cancel₀ hc0 e
        have hζρ : ∀ ρ, ρ ≠ τ → ζ z ρ = 1 := by
          intro ρ hρ
          simp only [hζdef, dif_pos hr.1, h2 ρ hρ, Matrix.one_apply_eq]
        have hζτ : ζ z τ = Complex.exp Complex.I := by
          simp only [hζdef, dif_pos hr.1, h1, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        have hμρ : ∀ ρ, ρ ≠ τ → μ z ρ = 1 := by
          intro ρ hρ
          simp only [hμdef, hζρ ρ hρ, inv_one, ite_self]
        rw [Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp),
          Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp)] at e2
        exact GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv _ _ (μ z τ) (by
          simp only [hμdef, hζτ]
          split_ifs
          exacts [Or.inr rfl, Or.inl rfl]) e2
      · have hE : IsEmpty (FVar D T.rank S.rank) :=
          ⟨fun v => hr ⟨by have := v.2.2.2; omega, by have := v.2.1.2; omega⟩⟩
        simp only [hdeg, Finset.eq_empty_of_isEmpty α.support, Finset.eq_empty_of_isEmpty α₀.support,
          Finset.filter_empty, Finset.sum_empty]
    · refine Set.Finite.subset Set.finite_empty fun α hα => hne ⟨α, hα⟩

end GlobalTheory.CenFockWt
