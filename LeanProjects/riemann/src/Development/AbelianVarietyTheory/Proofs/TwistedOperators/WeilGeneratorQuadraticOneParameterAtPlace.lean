import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Classical

namespace GlobalTheory.ArchRec.Gen

theorem xOp_dOp {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (k l : ι) {f : B} (hd : ∀ v, GlobalTheory.RealWeil.Sm ρ (dH ρ v f)) :
    xOp ρ k (dOp ρ H l f) = ∑ b : Bool × Bool,
      (-(1 / (4 * Real.pi)) * (if b.1 then -Complex.I else 1) * (if b.2 then Complex.I else 1) : ℂ) •
        dH ρ ((if b.1 then Complex.I else 1) • Pi.single k 1)
          (dH ρ ((if b.2 then Complex.I else 1) • H⁻¹ *ᵥ Pi.single l 1) f) := by
  have hs : ∀ (a : ℂ) v, GlobalTheory.RealWeil.Sm ρ (a • dH ρ v f) := fun a v => (smS ρ).smul_mem a (hd v)
  have ha : ∀ (a : ℂ) u v, GlobalTheory.RealWeil.Sm ρ (dH ρ u f + a • dH ρ v f) := fun a u v => (smS ρ).add_mem (hd u) (hs a v)
  simp only [xOp, dOp, dH_smul _ _ (ha _ _ _), dH_add _ (hd _) (hs _ _), dH_smul _ _ (hd _), Fintype.sum_prod_type,
    Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_smul]
  module

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ}
  {S T : HSp D}

theorem coe_dH_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) (v : GlobalTheory.RealWeil.Ix S T → ℂ) (hv : ∀ k, k.2 ≠ τ → v k = 0) :
    ((dH (rhoV hψ σ S T) v F).1 : WO S T → ℂ) = Datum.dRho (heisO ψ S T) θ τ (cpt v τ) F.1 := by
  have e : v = vecL (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
    funext ⟨⟨a, a'⟩, t⟩
    change _ = (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) t a a'
    by_cases ht : t = τ
    · subst ht
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne ht]
      exact hv _ ht
  rw [← GlobalTheory.DefLift.Gen.coe_dH h hψ F hF, ← e]

open scoped ComplexOrder in

theorem HM_inv_apply (k l : GlobalTheory.RealWeil.Ix S T) (hkl : k.2 ≠ l.2) : (HM S T)⁻¹ k l = 0 := by
  have : HM S T * blk (fun τ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ)⁻¹ • (gramAt D T τ)⁻¹) (gramAt D S) = 1 := by
    unfold HM
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (two_im_pos τ).ne', one_smul,
        mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit T τ)]
    · rw [mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ)]
  rw [inv_eq_right_inv this, WeylAction.blk_apply, if_neg hkl]

theorem nOp_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (z z' : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ), ∀ F : BB ψ S T,
      IsThetaFunO ψ S T F.1 → ((nOp (rhoV hψ σ S T) (HM S T) X F).1 : WO S T → ℂ) =
        ∑ i, c i • Datum.dRho (heisO ψ S T) θ τ (z i) (Datum.dRho (heisO ψ S T) θ τ (z' i) F.1) := by
  let e := (Fintype.equivFin (GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool)).symm
  let c : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → ℂ := fun a => X a.1 a.2.1 *
    (-(1 / (4 * Real.pi)) * (if a.2.2.1 then -Complex.I else 1) * (if a.2.2.2 then Complex.I else 1))
  let u : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.1 then Complex.I else 1) • Pi.single a.1 1
  let u' : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.2 then Complex.I else 1) • (HM S T)⁻¹ *ᵥ Pi.single a.2.1 1
  refine ⟨_, c ∘ e, fun i => cpt (u (e i)) τ, fun i => cpt (u' (e i)) τ, fun F hF => ?_⟩
  have th := GlobalTheory.DefLift.Gen.theta_dH h hψ F hF
  have e1 : nOp (rhoV hψ σ S T) (HM S T) X F =
      ∑ a, c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F) := by
    rw [nOp, Fintype.sum_prod_type (f := fun a => c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type (f := fun a => c (k, a) • dH (rhoV hψ σ S T) (u (k, a))
      (dH (rhoV hψ σ S T) (u' (k, a)) F))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [xOp_dOp _ _ _ _ fun v => sm_of_theta h hψ _ (th v), Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
  let j : BB ψ S T →ₗ[ℂ] (WO S T → ℂ) := ⟨⟨fun G => G.1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  change j _ = _
  rw [e1, map_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Function.comp_apply]
  beta_reduce
  generalize e i = a
  by_cases ha : a.1.2 ≠ τ ∨ a.2.1.2 ≠ τ
  · have : c a = 0 := by simp only [c, hX _ _ ha, zero_mul]
    rw [this, zero_smul, zero_smul]
  · push Not at ha
    have h1 : ∀ k, k.2 ≠ τ → u a k = 0 := fun k hk => by
      have : k ≠ a.1 := fun e => hk (e ▸ ha.1)
      simp only [u, Pi.smul_apply, Pi.single_eq_of_ne this, smul_zero]
    have h2 : ∀ k, k.2 ≠ τ → u' a k = 0 := fun k hk => by
      simp only [u', Pi.smul_apply, mulVec_single_one, col_apply, HM_inv_apply k a.2.1 (ha.2 ▸ hk), smul_zero]
    rw [← coe_dH_at h hψ F hF τ _ h2, ← coe_dH_at h hψ _ (th _) τ _ h1]
    rfl

variable {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem quadGen_of_supp (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT ω) (τ : D.what₂.Tau)
    (γ : ℝ → GA D S × GA D T) (h1 : Continuous γ) (h2 : ∀ s t, γ (s + t) = γ s * γ t)
    (h3 : ∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ)
    (h4 : ∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    QuadGen ψ θ τ ω γ := by
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  obtain ⟨lam, hl⟩ := GenZero.exists_generator D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨lam', hl'⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨n, c, z, z', hq⟩ := nOp_at h hψ τ X hX
  refine ⟨n, c, z, z', lam, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f := ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨u, hu, hud⟩ := hl F hf
  rw [← hq F hf, GlobalTheory.DefLift.Gen.coe_add_smul]
  have hl2 := hl' F hf
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam • F = G at hud ⊢
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam' • F = G' at hl2
  have e : (G.1 : WO S T → ℂ) = G'.1 := funext fun w => by
    have a1 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud
    have a2 := hl2 1 w
    simp only [one_mul, map_one, Module.End.one_apply] at a2
    refine HasDerivAt.unique ?_ a2
    exact a1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (hu t) w).symm)
  refine ⟨fun g w => by rw [e]; exact hl2 g w, fun μ 𝓕 hμ h𝓕 E hE => ?_⟩
  obtain ⟨E, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = E := ⟨toB hψ E hE, coe_toB hψ E hE⟩
  obtain ⟨i1, i2, i3, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  let Φ : BB ψ S T →L[ℂ] ℂ := (innerSL ℂ (toL2 _ _ (μ.restrict 𝓕) E)).comp (toL2 _ _ (μ.restrict 𝓕))
  have hΦ : ∀ A : BB ψ S T, ipTh μ 𝓕 A.1 E.1 = Φ A := fun A =>
    (BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) E.1 A.1).symm
  simp only [← hu, hΦ]
  exact (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud

theorem quadGen_oneP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → (∀ X ∈ lieAt S τ, QuadGen ψ θ τ ω fun t => (oneP θ S τ X t, 1)) ∧ ∀ Y ∈ lieAt T τ, QuadGen ψ θ τ ω fun t => (1, oneP θ T τ Y t) := by
  intro D ψ θ S T χS χT ω τ hθ hω
  have supp : ∀ (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ t, t ≠ τ → b t = 0 ∨ a t = 0) →
      ∀ k l : GlobalTheory.RealWeil.Ix S T, k.2 ≠ τ ∨ l.2 ≠ τ → blk b a k l = 0 := by
    intro b a hab k l hkl
    rw [WeylAction.blk_apply]
    split_ifs with e
    · rcases hab k.2 (hkl.elim id fun h => e ▸ h) with h | h <;> simp [h]
    · rfl
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine quadGen_of_supp hθ hω τ _ ((continuous_oneP hθ hX).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X))) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inr (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  · refine quadGen_of_supp hθ hω τ _ (continuous_const.prodMk (continuous_oneP hθ hY))
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inl (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _

end GlobalTheory.ArchRec.Gen

end
