import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitary

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharRat

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem symplOH_add_right {S T : HSp D} (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO, Matrix.add_apply, RingHom.map_add, mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplOH_isoPart_midPart (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (midPart V V' W B x) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  set M : Matrix (Fin V'.rank) (Fin V.rank) D.host.E := V'.gram⁻¹ * adj D B * V.gram with hMdef
  set Y : Mx D V'.rank V.rank := M.map (incA D) with hYdef
  have hM : Mᴴ = V.gram * B * V'.gram⁻¹ := by
    rw [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      GlobalTheory.MixModel.gramInv_conjTranspose]
    show V.gram * ((Bᴴ)ᴴ * V'.gram⁻¹) = _
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hX0 : X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj Y = 0 := by
    have e : GlobalTheory.MixModel.adj Y = GlobalTheory.MixModel.rat (V.gram * B * V'.gram⁻¹) := by
      rw [hYdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ GlobalTheory.MixModel.rat V.gram⁻¹ ⬝ GlobalTheory.MixModel.rat (V.gram * B * V'.gram⁻¹) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * B * V'.gram⁻¹) = adj D C * V.gram * B * V'.gram⁻¹ := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹, ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul, ← Matrix.mul_assoc]
    rw [this, hs.orth, Matrix.zero_mul]
    exact GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C (q₀.map (incA D)) = q₀.map (incA D) ⬝ X := rfl
  have e3 : midPart V V' W B x = x ⬝ Y := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj Y ⬝ GlobalTheory.MixModel.adj x ⬝ (GlobalTheory.MixModel.gA W ⬝ (q₀.map (incA D) ⬝ X)))
      = (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj Y ⬝ GlobalTheory.MixModel.adj x ⬝ GlobalTheory.MixModel.gA W ⬝ q₀.map (incA D)) ⬝ X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X ⬝ (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj Y ⬝ GlobalTheory.MixModel.adj x ⬝ GlobalTheory.MixModel.gA W ⬝ q₀.map (incA D))
      = (X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj Y) ⬝ (GlobalTheory.MixModel.adj x ⬝ GlobalTheory.MixModel.gA W ⬝ q₀.map (incA D)) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

set_option maxHeartbeats 1000000 in

theorem res_om_rat {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {γ : GA D W} (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    res V V' W C B μ 𝓨 (ω (1, γ) f) x = res V V' W C B μ 𝓨 f (Formalism.L2.Theta.mt W γ⁻¹ ⬝ x) := by
  have hrat := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω 1 (one_mem _) γ hγ f hf
  have hact : ∀ w : WO V W, actO V W 1 γ w = Formalism.L2.Theta.mt W γ ⬝ w := by
    intro w
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have hQP : Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ = 1 := GlobalTheory.MixModel.mt_mul_inv W γ
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have hpt : ∀ a, ω (1, γ) f (isoPart V W C a + midPart V V' W B x) =
      f (isoPart V W C (Formalism.L2.Theta.mt W γ⁻¹ ⬝ a) + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ ⬝ x)) := by
    intro a
    rw [← hrat, hact]
    refine congrArg (ω (1, γ) f) ?_
    show a ⬝ (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) +
        x ⬝ (((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) : Mx D V'.rank V.rank) =
      Formalism.L2.Theta.mt W γ ⬝ (Formalism.L2.Theta.mt W γ⁻¹ ⬝ a ⬝ (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) +
        Formalism.L2.Theta.mt W γ⁻¹ ⬝ x ⬝ (((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) : Mx D V'.rank V.rank))
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul, Matrix.one_mul]
  show ∫ a in 𝓨, ω (1, γ) f (isoPart V W C a + midPart V V' W B x) ∂μ =
    ∫ a in 𝓨, f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ ⬝ x)) ∂μ
  simp only [hpt]
  have hper : ∀ q ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (q + a) + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ ⬝ x)) =
        f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ ⬝ x)) := by
    intro q hq a
    obtain ⟨q₀, rfl⟩ := hq
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc, ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart, hf.quasi,
      GlobalTheory.TwistEquiRat.ratW_eq_isoPart, symplOH_add_right, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame,
      symplOH_isoPart_midPart V V' W C B hs, add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  exact GlobalTheory.TwistEquiRat.integral_mul_left μ 𝓨 hμ _ _ ((GlobalTheory.MixModel.mem_GQ_iff W γ⁻¹).1 (inv_mem hγ))
    ((GlobalTheory.MixModel.mem_GQ_iff W γ).1 hγ) hPQ hQP
    (fun a => f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ ⬝ x))) hper

theorem char_eq_one_of_rat : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ γ ∈ GQ W, c γ = 1 := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ c hc γ hγ
  obtain ⟨hall, f₀, hf₀, hne⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  obtain ⟨x, hx⟩ : ∃ x, res V V' W C B μ 𝓨 f₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hres : IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f₀) := ((hall f₀ hf₀).2.1)
  have h1 := congrFun (hc γ f₀ hf₀) (actO V' W 1 γ x)
  have hact : actO V' W 1 γ x = Formalism.L2.Theta.mt W γ ⬝ x := by
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have h2 := GlobalTheory.WeilRat.om_rat_actO D ψ hω'.std V' W χS' χT' ω' hω' 1 (one_mem _) γ hγ _ hres x
  rw [Pi.smul_apply, h2, res_om_rat hs hω hμ hγ hf₀, hact, ← Matrix.mul_assoc, hPQ, Matrix.one_mul,
    smul_eq_mul] at h1
  have h3 : (c γ : ℂ) = 1 := by
    have := mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)
    exact this
  exact Circle.ext (by simpa using h3)

end GlobalTheory.TwistCharRat

end
