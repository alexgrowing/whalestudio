import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

open Matrix Formalism.IndefR.Datum

variable {D : D7}

theorem jX_dblDec_mulVec (V : HSp D) (y : Fin V.rank → AE D) :
    (dblDec V).jX *ᵥ y = pairVec finSumFinEquiv (GlobalTheory.MixModel.giA V *ᵥ y) (GlobalTheory.MixModel.giA V *ᵥ y) := by
  funext k
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
  · rw [pairVec_inl]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows]
    congr 1
    funext j
    simp only [GlobalTheory.MixModel.rat, GlobalTheory.MixModel.giA, map_apply, submatrix_apply, id, Equiv.symm_apply_apply,
      fromRows_apply_inl, fromRows_apply_inr]
  · rw [pairVec_inr]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows]
    congr 1
    funext j
    simp only [GlobalTheory.MixModel.rat, GlobalTheory.MixModel.giA, map_apply, submatrix_apply, id, Equiv.symm_apply_apply,
      fromRows_apply_inl, fromRows_apply_inr]

theorem mem_siegel_of_mem_stab (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ stab (dblDec V)) : p ∈ siegel V := by
  obtain ⟨α, hα⟩ := h
  refine mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => ?_)
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  have hx : pairVec finSumFinEquiv x x = (dblDec V).jX *ᵥ (GlobalTheory.MixModel.gA V *ᵥ x) := by
    rw [jX_dblDec_mulVec, mulVec_mulVec, GlobalTheory.MixModel.giA_mul_gA, one_mulVec]
  change mt (dblSp V) p *ᵥ _ ∈ _
  rw [hx, mulVec_mulVec, hα, ← mulVec_mulVec, jX_dblDec_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

theorem mul_jX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) :
    mt (dblSp V) p ⬝ (dblDec V).jX = (dblDec V).jX ⬝
      (GlobalTheory.MixModel.gA V * leviMat finSumFinEquiv (mt (dblSp V) p) * GlobalTheory.MixModel.giA V) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp V) p) := mem_siegelOf.1 h
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, jX_dblDec_mulVec, jX_dblDec_mulVec, hk.mulVec_diag, mulVec_mulVec,
    mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.giA_mul_gA, Matrix.one_mul]

def gramGL (V : HSp D) : GL (Fin V.rank) (AE D) :=
  ⟨GlobalTheory.MixModel.gA V, GlobalTheory.MixModel.giA V, GlobalTheory.MixModel.gA_mul_giA V, GlobalTheory.MixModel.giA_mul_gA V⟩

theorem mem_stab_of_mem_siegel (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) : p ∈ stab (dblDec V) :=
  ⟨gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹,
    mul_jX_dblDec V h⟩

theorem onX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)) :
    onX (dblDec V) ⟨p, h'⟩ =
      gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹ :=
  Units.ext ((eq_of_mul_jX _ (mul_jX (dblDec V) ⟨p, h'⟩)).trans (eq_of_mul_jX _ (mul_jX_dblDec V h)).symm)

theorem isAniso_zeroSp (D : D7) : IsAniso (zeroSp D) := by
  rintro r C ⟨hr, hC, -⟩
  exact hC.ne_zero ⟨0, hr⟩ (funext fun i => Fin.elim0 i)

theorem siegel_eq_stab_dblDec : ∀ (D : D7) (V : HSp D), siegel V = stab (dblDec V) ∧ (∀ (p : GA D (dblSp V)) (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)), aP V ⟨p, h⟩ = Matrix.GeneralLinearGroup.det (onX (dblDec V) ⟨p, h'⟩)) ∧ IsAniso (zeroSp D) ∧ ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → ∃ (L : Submodule (𝓞 D.host.E) (Fin (dblSp V).rank → D.host.E)) (b : GL (Fin (dblSp V).rank) (AE D)), IsLevel (dblSp V) L b ∧ Khat V a = lev (dblSp V) L b := by
  intro D V
  refine ⟨Subgroup.ext fun p => ⟨mem_stab_of_mem_siegel V, mem_siegel_of_mem_stab V⟩, fun p h h' => ?_,
    isAniso_zeroSp D, fun a ha => ⟨frameLat (dblSp V), blkGL finSumFinEquiv (a, a),
      ⟨isLattice_frameLat_host _, SelfDual.isSelfDualAt_frameLat D (dblSp V), ha.dbl⟩, Khat_eq V a⟩⟩
  rw [onX_dblDec V h h', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rfl

end GlobalTheory.EisCont

end
