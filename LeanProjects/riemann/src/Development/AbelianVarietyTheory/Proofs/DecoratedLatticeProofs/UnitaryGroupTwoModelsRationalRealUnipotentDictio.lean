import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst

noncomputable section

namespace GlobalTheory.BridgeDict

open NumberField Matrix Formalism.MainNotions.S
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF Ainf HA fstA sndA inclR)

theorem comp_eq_thetaV (I : AutInst) (v : InfinitePlace I.F) (θ : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ) :
    θ.comp (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)).toRingHom =
      Formalism.L2.SG.AdBridge.thetaV I v := by
  have key : (fun a : Ainf I.F => θ (a ⊗ₜ[I.F] (1 : I.E))) =
      fun a : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (a v) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hθ.2
      ((InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)) ?_
    funext x
    have e : (algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E) =
        (1 : Ainf I.F) ⊗ₜ[I.F] (algebraMap I.F I.E x) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    simp only [Function.comp_apply]
    rw [e, hθ.1, I.φ_over]
    exact (Formalism.L2.SG.AdBridge.evV_algebraMap I v x).symm
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul]
    have e : (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) (a ⊗ₜ[I.F] x) =
        (a.1 ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [e, map_mul, hθ.1, congrFun key a.1]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tauF_apply (I : AutInst) (z : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I z =
      Algebra.TensorProduct.comm I.F _ _ (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem fin_eq (I : AutInst) (h : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I h).map (Formalism.L2.SG.AdBridge.tauF I) =
      (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
  unfold Formalism.MainNotions.StandardLattice.finMat
  rw [Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  rw [tauF_apply]

theorem infMat_bridge (I : AutInst) (e : I.GA ≃ₜ* Formalism.L2.SG.AdBridge.HAd I) (he : Formalism.L2.SG.AdBridge.IsBridge I e)
    (v : InfinitePlace I.F) (θv : Ainf I.F ⊗[I.F] I.E →+* ℂ) (hθv : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θv) (x : I.GA) :
    Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θv (e x) = I.P v * uMat (x.1 v) * (I.P v)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [(he x).1 v, Formalism.L2.SG.AdBridge.ofHAInf, ← comp_eq_thetaV I v θv hθv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_map]
  rfl

end GlobalTheory.BridgeDict

namespace GlobalTheory.BridgeDict

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem bridge_dict : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  intro D θ hθ V fr
  have hb := Formalism.IndefR.Eqv.UI.brg_isBridge fr
  have hθv : ∀ v : InfinitePlace D.host.F,
      IsInfEmb (Formalism.IndefR.Eqv.UI.phiV D v) (θ ((Formalism.L2.Host.tauPl D).symm v)) := fun v => hθ _
  refine ⟨fun x => ?_, fun x τ A hA => ?_, fun W hW => ?_⟩
  · have h1 := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.Eqv.UI.instV fr)).2.1 (Formalism.IndefR.Eqv.UI.brg fr) hb
    have e : Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔
        Formalism.IndefR.Eqv.UI.brg fr x ∈ Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := Iff.rfl
    rw [e, ← h1]
    exact (Formalism.IndefR.Eqv.UI.brg fr).injective.mem_set_image
  · subst hA
    have h := infMat_bridge (Formalism.IndefR.Eqv.UI.instV fr) _ hb (Formalism.L2.Host.tauPl D τ) (θ τ)
      (by have h := hθv (Formalism.L2.Host.tauPl D τ); rwa [Equiv.symm_apply_apply] at h) x
    exact h
  · obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.CuspCompare.isIsot_iff (Formalism.IndefR.Eqv.UI.instV fr) W).1 hW
    refine ⟨r, C, hC, fun x hx => ?_⟩
    obtain ⟨L, R, hL, hR⟩ := GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E)
      (Formalism.IndefR.Eqv.UI.instV fr).J_det hC.2.1
    let T : GA D V ≃* (Formalism.IndefR.Eqv.UI.instV fr).GA := (Formalism.IndefR.Eqv.UI.brg fr).symm.toMulEquiv
    have hT : ∀ g, Formalism.IndefR.Eqv.UI.brg fr (T g) = g := fun g => (Formalism.IndefR.Eqv.UI.brg fr).apply_symm_apply g
    unfold NI at hx
    have := (GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (GlobalTheory.T.strong_approximation_unitaryUnipotentRadical _ _ hW).1 (fun g => ?_) _).1 hx
    · exact ((Formalism.IndefR.Eqv.UI.brg fr).symm_apply_apply x) ▸ this
    · rw [GlobalTheory.CuspCompare.mem_NA_iff (Formalism.IndefR.Eqv.UI.instV fr) _ hθv g (T g) ?_ ?_ hL hR]
      · exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)
      · rw [(hb (T g)).2, Formalism.L2.SG.AdBridge.ofHAFin, fin_eq]
        exact congrArg (fun h => (finMat _ _ h).map _) (hT g)
      · intro v
        rw [← infMat_bridge _ _ hb v _ (hθv v) (T g)]
        exact congrArg (infMat _ _ _) (hT g)

end GlobalTheory.BridgeDict
