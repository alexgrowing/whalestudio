import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

def frOf {D : D7} (V : HSp D) (s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ)
    (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : Fr V where
  ε τ := sgB (p τ)
  fr τ := (B τ)⁻¹
  fr_unit τ := (isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (onb_facts (h τ)).1)
  fr_gram τ := by
    obtain ⟨u, g, -⟩ := onb_facts (h τ)
    rw [← g]
    have h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ u, conjTranspose_one]
    calc _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ u, Matrix.one_mul, Matrix.mul_one]

variable {D : D7} {V : HSp D} {s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {p : D.what₂.Tau → ℕ}

theorem frOf_onb (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).onb = B := by
  funext τ
  exact nonsing_inv_nonsing_inv _ (onb_facts (h τ)).1

theorem frOf_cart (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).cart = s := by
  funext τ
  obtain ⟨u, -, c⟩ := onb_facts (h τ)
  change ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (sgB (p τ)) * (B τ)⁻¹ = s τ
  rw [nonsing_inv_nonsing_inv _ u, ← c, mul_nonsing_inv_cancel_right _ _ u]

theorem pure_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (P : MvPolynomial ι ℂ) :
    pureTensorL A (0 : X → ℂ) P = 0 := by
  have h : ∀ l : List ι, l.foldr (fun i g => A i g) (0 : X → ℂ) = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih, hA]
  have hz : pureTensorL A (0 : X → ℂ) = 0 := (MvPolynomial.basisMonomials ι ℂ).ext fun k => by
    simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.zero_apply]
    exact h _
  rw [hz, LinearMap.zero_apply]

end GlobalTheory.WeilReal

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

theorem comb {R : Type} [AddCommGroup R] [Module ℂ R] (a b q P : R) (h c d : ℂ) (hq : a + b = q + h • P) :
    q + (h + c - d) • P = (a + (-d) • P) + (b + c • P) := by
  have e : q = a + b - h • P := eq_sub_of_add_eq hq.symm
  rw [e]
  module

theorem realAllO : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  intro D ψ S T χS χT om hd _ θ sS sT BS BT pS pT hp τ αS αT hαS hαT XS XT hXS hXT f hf hv P x
  obtain ⟨A, hA⟩ : ∃ A : Fr S, A = frOf S sS BS pS hp.onbS := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fr T, B = frOf T sT BT pT hp.onbT := ⟨_, rfl⟩
  have cA : A.cart = sS := hA ▸ frOf_cart hp.onbS
  have cB : B.cart = sT := hB ▸ frOf_cart hp.onbT
  have oA : A.onb = BS := hA ▸ frOf_onb hp.onbS
  have oB : B.onb = BT := hB ▸ frOf_onb hp.onbT
  have eA : A.ε τ = sgB (pS τ) := by rw [hA]; rfl
  have eB : B.ε τ = sgB (pT τ) := by rw [hB]; rfl
  have rA : A.fr τ = (BS τ)⁻¹ := by rw [hA]; rfl
  have rB : B.fr τ = (BT τ)⁻¹ := by rw [hB]; rfl
  have pt : pureTensorO ψ θ S T sS sT BS BT f = ptF ψ θ A B f := by
    rw [ptF, cA, cB, oA, oB]
  rw [pt]
  have lin : ∀ (g : WO S T → ℂ) (Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (Q + Q') = ptF ψ θ A B g Q + ptF ψ θ A B g Q' := fun g Q Q' =>
    map_add (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) Q Q'
  have lsm : ∀ (g : WO S T → ℂ) (c : ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (c • Q) = c • ptF ψ θ A B g Q := fun g c Q =>
    map_smul (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) c Q
  by_cases f0 : f = 0
  · subst f0
    have z0 : ∀ Q, ptF ψ θ A B 0 Q = 0 := fun Q => by
      refine pure_zero _ (fun k => ?_) Q
      funext y
      simp [aPlusAll, aPlus, crea, Datum.dRho, heisO]
    simp only [z0, map_zero]
    exact hasDerivAt_const _ _
  obtain ⟨f₀, hv0, hne⟩ := GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction D S T A B θ ψ hp.std hp.inf f hf f0
  obtain ⟨κS, κT, hκ⟩ := GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars D S T A B θ ψ χS χT om τ hp.inf hd
  have k0 := hκ f₀ hv0.1 (hv0.2 τ)
  have all := GlobalTheory.T.lieAction_fockOperators_scalars_trace D S T A B θ ψ χS χT om f₀ τ αS αT hp.inf hd hαS hαT hv0
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have hz' : f₀ z ≠ 0 := hz
  have one : ∀ c : ℂ, ptF ψ θ A B f₀ (c • (1 : MvPolynomial _ ℂ)) z = c * f₀ z := fun c => by
    rw [lsm]
    have e1 : ptF ψ θ A B f₀ 1 = f₀ := GlobalTheory.FockIndep.pure_one f₀
    rw [e1]
    rfl
  have eS : κS XS = -((αT : ℂ) * XS.trace) := by
    have e := (k0.1 XS hXS 1 z).unique (all.1 XS hXS 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have eT : κT XT = (αS : ℂ) * XT.trace := by
    have e := (k0.2 XT hXT 1 z).unique (all.2 XT hXT 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have kf := hκ f hf (by rw [cA, cB]; exact hv)
  have ht : IsThetaFunO ψ S T (ptF ψ θ A B f P) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hp.std hp.inf _ _ _ _ hf P
  have sm := GlobalTheory.T.weilDatum_realPlaceDerivatives_add D S T θ ψ χS χT om τ hp.inf hd XS hXS XT hXT _ _ _ ht (kf.1 XS hXS P) (kf.2 XT hXT P) x
  have uS := (onb_facts (hp.onbS τ)).1
  have uT := (onb_facts (hp.onbT τ)).1
  have frA : (A.fr τ * XS * (A.fr τ)⁻¹) = (BS τ)⁻¹ * XS * BS τ := by
    rw [rA, nonsing_inv_nonsing_inv _ uS]
  have frB : (B.fr τ * XT * (B.fr τ)⁻¹) = (BT τ)⁻¹ * XT * BT τ := by
    rw [rB, nonsing_inv_nonsing_inv _ uT]
  have q := fock_eq_quad τ (pS τ) (pT τ) (hp.onbS τ) (hp.onbT τ) hXS hXT P
  have e : ptF ψ θ A B f (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
      (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace - (αT : ℂ) * XS.trace) • P) x =
      ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * XS * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS XS • P) x +
      ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * XT * (B.fr τ)⁻¹) P + κT XT • P) x := by
    rw [← Pi.add_apply (ptF ψ θ A B f _), ← lin, frA, frB, eS, eT, eA, eB, comb _ _ _ _ _ _ _ q]
  rw [e]
  exact sm

end GlobalTheory.WeilReal

end
