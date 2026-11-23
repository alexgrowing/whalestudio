import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ContDiff

namespace GlobalTheory.AdjointPair

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.mul_add, Matrix.add_mul]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp only [dagger, adj_zero, Matrix.zero_mul, Matrix.mul_zero]
  map_add' := dagger_add S T

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem map_dagger_zero {B : Type} [CommRing B] (p : AE D →+* B) (hp : ∀ z, p z = 0 → p (cA D z) = 0)
    (S T : HSp D) {x : WO S T} (hx : x.map p = 0) : (dagger S T x).map p = 0 := by
  have h1 : (adj x).map p = 0 := by
    funext i j
    have := congrFun (congrFun hx j) i
    simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply] at this ⊢
    exact hp _ this
  rw [dagger, Matrix.map_mul, Matrix.map_mul, h1, Matrix.zero_mul, Matrix.mul_zero]

theorem infPart_zero (z : AE D) (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  rw [infPart_cA, h, RingHom.map_zero]

theorem finPart_zero (z : AE D) (h : finPart D z = 0) : finPart D (cA D z) = 0 := by
  rw [finPart_cA, h, RingHom.map_zero]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  rw [hO_eq_trace, hO_eq_trace]
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, gA_giA_cancel, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_dagger (S T : HSp D) (x y : WO S T) :
    symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y := by
  have h := GlobalTheory.OrientedHeis.symplO_skew x y
  unfold symplO at h ⊢
  rw [hO_dagger]
  exact h

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_dagger, mul_neg]

theorem act_dagger (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    dagger S T (actO S T g h x) = actO T S h g (dagger S T x) := by
  simp only [dagger, actO_eq, adj_mul, mt_inv S g, mt_inv T h, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (hn a)).symm

theorem heis_dagger (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) : heisO ψ T S (dagger S T w) (cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (heisO ψ S T w f) := by
  funext y
  have hs : symplOH T S y (dagger S T w) = -symplOH S T (dagger T S y) w := by
    have := symplOH_dagger S T (dagger T S y) w
    rwa [dagger_dagger] at this
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, map_mul]
  rw [dagger_add, dagger_dagger, hs, conj_psi hn]

theorem theta_fwd (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (cj (dagger T S) f) where
  quasi γ w := by
    have hr : dagger T S (ratW S T γ) = ratW T S (T.gram⁻¹ * (γᴴ * S.gram)) := by
      rw [ratW_eq, ratW_eq]; exact dagger_rat T S γ
    have hq := hf.quasi (T.gram⁻¹ * (γᴴ * S.gram)) (dagger T S w)
    rw [← hr, symplOH_dagger, neg_neg] at hq
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [dagger_add, hq, map_mul, conj_psi hn]
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (daggerHom T S), hU.preimage (continuous_dagger T S), fun u hu hinf => ?_⟩
    have h1 := heis_dagger ψ hn S T (dagger T S u) f
    rw [dagger_dagger, hfix (dagger T S u) hu (map_dagger_zero (infPart D) infPart_zero T S hinf)] at h1
    exact h1
  cont := Complex.continuous_conj.comp (hf.cont.comp (continuous_dagger T S))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((daggerHom T S).comp L) ((continuous_dagger T S).comp hL)
      (fun t => map_dagger_zero (finPart D) finPart_zero T S (hfin t)) (dagger T S w)
    have e : (fun t => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f (w + L t)) =
        fun t => Complex.conjCLE (f (dagger T S w + (daggerHom T S).comp L t)) := by
      funext t
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, AddMonoidHom.comp_apply, Complex.conjCLE_apply]
      rw [dagger_add]; rfl
    rw [e]
    exact Complex.conjCLE.contDiff.comp h

theorem theta_iff (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (f : WO S T → ℂ) :
    IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f := by
  refine ⟨fun h => ?_, theta_fwd ψ hn S T⟩
  have := theta_fwd ψ hn T S h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at this

theorem adjoint_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ x y : WO S T, symplO T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T y) = -symplO S T x y) ∧ (∀ g h (x : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (actO S T g h x) = actO T S h g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x)) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) ↔ IsThetaFunO ψ S T f) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T w) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) (heisO ψ S T w f) := by
  intro D ψ hψ S T
  exact ⟨symplO_dagger S T, act_dagger S T, fun f => theta_iff ψ hψ.1.2.1 S T f, heis_dagger ψ hψ.1.2.1 S T⟩

end GlobalTheory.AdjointPair

end
