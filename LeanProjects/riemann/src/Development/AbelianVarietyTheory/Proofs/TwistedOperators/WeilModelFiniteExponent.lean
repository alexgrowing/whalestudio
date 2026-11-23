import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryPrintHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThOInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.LineStab
theorem ptF_one' {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (f : WO V W → ℂ) : ptF ψ θ A B f 1 = f := by
  have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [h1]
  simp only [ptF, pureTensorO, pureTensorL]
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem thO_zero' {m k d : ℕ} {D : D7} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    GlobalTheory.TripleRead.thO Mo ψ G e 0 = 0 := by
  funext x
  simp only [GlobalTheory.TripleRead.thO, GlobalTheory.WeilM.thetaSum, Pi.zero_apply]
  refine (tsum_congr fun ξ => ?_).trans tsum_zero
  exact mul_zero _

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem det_sgn_gram {D : D7} (ε : Bool) (M : HSp D) (h : (GlobalTheory.RealDict.sgE (D := D) ε • M.gram).det ≠ 0) :
    ((sgn ε M).gram).det ≠ 0 := by
  have hg : (sgn ε M).gram = -(GlobalTheory.RealDict.sgE (D := D) ε • M.gram) := by
    cases ε <;> ext i j <;> simp [GlobalTheory.RealDict.sgE, sgn, HSpace.gram]
  rw [hg, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

theorem derivLine_mem_map : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
          f₁ ∈ N.map Φ := by
  intro hPr D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hΦi hΦr hF N hN γ hγ f hf f₁ hA
  obtain ⟨P, hPN, rfl⟩ := Submodule.mem_map.mp hf
  obtain ⟨f₀, r, hvac, hf₀, hΦ⟩ := hF
  obtain ⟨h, Y, hY, hγh, hD⟩ := GlobalTheory.T.skewSpaceLine_oneParam_fockDerivative D ψ θ ε M X A B χS χT ω eS eT hθ hW hE Ws hR.JW γ hγ
  have hP'N : (∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P) ∈ N :=
    Submodule.sum_mem _ (fun t _ => hN ⟨(t, Y t), hY t⟩ P hPN)
  have hr : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r x ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r = 0 := funext hc
    have h1 := (hΦ 1).2
    rw [h0, thO_zero', ptF_one'] at h1
    exact hf₀ h1.symm
  have hRest : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r :=
    GlobalTheory.Twist.RestrictionTransfer.rest_transfer D.host.F (Φ 1) r (hΦ 1).1 hr
  have hψ' := hR.psi
  subst hψ'
  have key : ∀ x, GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x =
      ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ (∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P) x := by
    intro x
    have d1 := GlobalTheory.T.real_dictionary_hypotheses hPr D Xs Ws Mo ψ' χX χW om τ hH hR.good γ hγ (Φ P) f₁ r (hRest _) (hRest _) hA
      (sgn ε M).gram (Equiv.refl (Fin X.rank)) x
    have d2 := hD f₀ hvac P x
    have hfun : (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r)) x) =
        fun t => ω (1, h t) (ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ P) x := by
      funext t
      have e1 := hR.transp _ (hRest (Φ P)).2 1 (h t)
      rw [conjU_one'] at e1
      rw [hγh t, e1, (hΦ P).2]
    rw [hfun] at d1
    exact d1.unique d2
  have hthO : GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) =
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ (∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P)) r) := by
    funext x
    rw [key x, (hΦ _).2]
  have hdet : ((sgn ε M).gram).det ≠ 0 := det_sgn_gram ε M (by rw [← hR.JX]; exact hH.2.2.2.1)
  have ht := GlobalTheory.ThetaTransformInj.thO_injective D Xs Ws Mo ψ' χX χW om τ hH hR.good (sgn ε M).gram
    (Equiv.refl (Fin X.rank)) hdet _ (hRest f₁).2 _ (hRest _).2 hthO
  have hr' : ∃ x, r x ≠ 0 := by
    obtain ⟨x, hx⟩ := hr
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens at hx
    exact ⟨x, right_ne_zero_of_mul hx⟩
  exact Submodule.mem_map.mpr ⟨_, hP'N, (GlobalTheory.ArchCancel.eq_of_tens_eq D.host.F r (hRest f₁).1 hr' f₁ _ ht).symm⟩
end GlobalTheory.RealDict.LineStab

end
