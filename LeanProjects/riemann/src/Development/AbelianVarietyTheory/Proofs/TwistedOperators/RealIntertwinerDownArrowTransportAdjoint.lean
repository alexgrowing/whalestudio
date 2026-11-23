import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

theorem isIntw_transport {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X Y P P' : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P'] [Module ℂ P'] (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (ω₀ : GA D V × GA D W →* Module.End ℂ (Y → ℂ))
    (pt : P → (X → ℂ)) (pt₀ : P' → (Y → ℂ)) (e : P ≃ₗ[ℂ] P') (b : Y → X) (It : P' →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (hpt : ∀ φ, pt₀ (e φ) = pt φ ∘ b) (hω : ∀ p F, ω₀ p (F ∘ b) = ω p F ∘ b) (h : IsIntw θ M M' ω₀ pt₀ It) :
    IsIntw θ M M' ω pt (It ∘ₗ e.toLinearMap) where
  ne h0 := h.ne (LinearMap.ext fun φ => by
    have := congrArg (fun L => L (e.symm φ)) h0
    simpa using this)
  bdd φ w := h.bdd (e φ) w
  eqK τ g hg φ φ' hφ v := h.eqK τ g hg (e φ) (e φ') (by rw [hpt, hpt, hφ, hω]) v
  eqg τ Y hY φ φ' hd v := h.eqg τ Y hY (e φ) (e φ') (fun z => by
    simp only [hpt, hω, Function.comp_apply]; exact hd (b z)) v
  invK τ k hk φ φ' v v' hφ hv := h.invK τ k hk (e φ) (e φ') v v' (by rw [hpt, hpt, hφ, hω]) hv
  invg τ Y hY φ φ' v v' hd hv := h.invg τ Y hY (e φ) (e φ') v v' (fun z => by
    simp only [hpt, hω, Function.comp_apply]; exact hd (b z)) hv

open GlobalTheory.FockAdjoint in

theorem ptOf_dag {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} {SV SW : D.what₂.Tau → SPar} (M : DSModel V SV) (M' : DSModel W SW) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) :
    ptOf ψ θ M' M (dag V W g) (jHom (Fr.ofModel M) (Fr.ofModel M') Q) = dag V W (ptOf ψ θ M M' g Q) := by
  set A := Fr.ofModel M
  set B := Fr.ofModel M'
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hψ V W
  have cA := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A
  have cB := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B
  have hd := L.theta g hg
  show ptF ψ θ B A (dag V W g) (jHom A B Q) = dag V W (ptF ψ θ A B g Q)
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [jHom_C, ← mul_one (MvPolynomial.C _), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one,
      dag_smul']
  | add p q hp hq => rw [map_add, ptF_add, ptF_add, hp, hq, dag_add]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, jHom_X, mul_comm (jHom A B p), mul_assoc, ptF_C, ptF_X_mul hψ hθ B A hd, hp, mul_comm p,
      ptF_X_mul hψ hθ A B hg]
    dsimp only
    rw [aPlus_dag hψ hθ L τ (cA τ) (cB τ) _ (ptF_theta hψ hθ A B hg p), cdag_unitMap,
      aPlus_real_smul hψ hθ (ptF_theta hψ hθ A B hg p), dag_smul', Complex.conj_ofReal, smul_smul]
    rw [show ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) = sgv A B τ i j from rfl, sgv_mul_self, one_smul]

open GlobalTheory.FockAdjoint in
theorem jHom_map_conj {S T : HSp D} (A : Fr S) (B : Fr T) (P : PolF D T.rank S.rank) :
    jHom A B (MvPolynomial.map (starRingEnd ℂ) P) = swapHom A B P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [jHom_C, swapHom]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.map_X, jHom_X, map_mul, swapHom_X]

theorem dag_cj {S T : HSp D} (F : WO S T → ℂ) : dag S T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = F ∘ adjO S T := by
  funext y; simp [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

end GlobalTheory.AdjTr

open GlobalTheory.AdjTr in

theorem GlobalTheory.AdjTr.downArrow_transport : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  intro D S T ψ θ χ ω f hθ hW hV
  set A := Fr.ofModel S.M
  set B := Fr.ofModel T.M
  have hstd : IsStdChar D ψ (-1) := hV.1
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hstd S.V T.V
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hV.2.theta
  have hvv := GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace S T ψ θ f hV
  refine ⟨adjRep ω, dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f), χ⁻¹, (swapEquiv A B).toLinearEquiv, ?_,
    fun τ a h => GlobalTheory.Mem.HeckeExp.hasInfExp_inv h, ⟨L.theta _ hvv.theta, ?_, fun τ => GlobalTheory.FockAdjoint.vac_dag hstd hθ L τ
      (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ) hvv.theta (hvv.vac τ)⟩,
    fun It hIt => ?_⟩
  · exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S.V T.V χ⁻¹ χ⁻¹ (conjRep ω) (GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace ψ S.V T.V χ χ ω hW)
  · intro h0
    apply hvv.ne
    funext x
    have := congrFun h0 (adjO T.V S.V x)
    simp only [dag, GlobalTheory.AdjLawPf.adj_invol, Pi.zero_apply, map_eq_zero] at this
    exact this
  · refine isIntw_transport θ T.M S.M ω.swap (adjRep ω) (GlobalTheory.Grid.fock ψ θ true S T f)
      (ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))) (swapEquiv A B).toLinearEquiv (adjO S.V T.V) It
      (fun φ => ?_) (fun p F => ?_) ((GlobalTheory.Grid.isIntw_iff θ T.M S.M _ _ It).2 hIt)
    · show ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (swapHom A B φ) = _
      rw [← jHom_map_conj, ptOf_dag hstd hθ S.M T.M hvv.theta, ← GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq S T ψ θ f hstd hθ hth, dag_cj]
    · obtain ⟨h, g⟩ := p
      rw [adjRep_apply, WRep.swap_apply]
      funext y
      simp only [Function.comp_apply, GlobalTheory.AdjLawPf.adj_invol]

end
