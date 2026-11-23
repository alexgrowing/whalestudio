import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWittTowerIntertwinesLeviWeilRepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicIndepCovolumeMeasureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryActsOnThetaRestrictionSmallerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedWeilFirstFactorApplyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LeviChar

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem detPow_pos' {D : D7} {r : ℕ} (a : GL (Fin r) (AE D)) (n : ℕ) : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  apply Real.rpow_pos_of_pos
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2
    ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero)

theorem detPow_mul' {D : D7} {r : ℕ} (a b : GL (Fin r) (AE D)) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (a * b) n = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow b n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  rw [map_mul, map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem detPow_one' {D : D7} {r : ℕ} (n : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (1 : GL (Fin r) (AE D)) n = 1 := by
  have h := detPow_mul' (1 : GL (Fin r) (AE D)) 1 n
  rw [mul_one] at h
  exact mul_left_cancel₀ (detPow_pos' 1 n).ne' (h.symm.trans (mul_one _).symm)

theorem continuous_detPow' {D : D7} {r : ℕ} (n : ℕ) :
    Continuous fun a : GL (Fin r) (AE D) => GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  have h1 : Continuous fun a : GL (Fin r) (AE D) => Matrix.GeneralLinearGroup.det a :=
    Matrix.GeneralLinearGroup.continuous_det
  have h2 := (GlobalTheory.Doubling.continuous_absE (F := D.host.F) (E := D.host.E))
  exact (NNReal.continuous_coe.comp (h2.comp h1)).rpow_const (fun _ => Or.inr (by positivity))

set_option maxHeartbeats 400000 in

open GlobalTheory.MixModel in

theorem levi_scalars_autChar : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∃ (μa : GL (Fin r) (AE D) →* Circle) (ξ : GA D V' →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharGL r μa ∧ GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharU V' ξ ∧ ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) = ((μa a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * (ξ g' : ℂ)) • ω' (g', 1) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω'
  obtain ⟨d, hdC, hdB, hker⟩ := GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent D V V' r C B hs
  obtain ⟨μ₀, 𝓨₀, h₀⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have hind := fun f hf μ 𝓨 (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) =>
    GlobalTheory.T.thetaRestrictIsotropic_indep_covolume_measure D V V' W r C B hs d hdC hdB ψ f hf μ₀ μ 𝓨₀ 𝓨 h₀ hμ

  let s : GL (Fin r) (AE D) → GA D V' → GA D V := fun a g' => d.levi a * d.emb0 g'
  have hsC : ∀ a g', HMul.hMul (mt V (s a g')) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val := by
    intro a g'
    subst hdC
    show mt V (d.levi a * d.emb0 g') ⬝ d.jX = d.jX ⬝ a.1
    rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]
  have hsB : ∀ a g', HMul.hMul (mt V (s a g')) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g') := by
    intro a g'
    subst hdB
    show mt V (d.levi a * d.emb0 g') ⬝ d.j0 = d.j0 ⬝ mt V' g'
    rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]
  have hsmul : ∀ a₁ g₁ a₂ g₂, s (a₁ * a₂) (g₁ * g₂) = s a₁ g₁ * s a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    show d.levi (a₁ * a₂) * d.emb0 (g₁ * g₂) = d.levi a₁ * d.emb0 g₁ * (d.levi a₂ * d.emb0 g₂)
    rw [map_mul, map_mul, show d.levi a₁ * d.emb0 g₁ * (d.levi a₂ * d.emb0 g₂) =
      d.levi a₁ * (d.emb0 g₁ * d.levi a₂) * d.emb0 g₂ by simp only [mul_assoc], d.wittHyperbolic_anisotropic_commute_levi]
    simp only [mul_assoc]
  have hs1 : s 1 1 = 1 := by simp [s]
  have hc := fun a g' => GlobalTheory.T.restriction_wittTower_intertwines_levi_weilRep D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω' μ₀ 𝓨₀ h₀ a g' (s a g')
    (hsC a g') (hsB a g') 1
  choose c hc using hc
  set R := res V V' W C B μ₀ 𝓨₀ with hR
  have dpos := fun a : GL (Fin r) (AE D) => detPow_pos' a W.rank
  have dmul := fun a b : GL (Fin r) (AE D) => detPow_mul' a b W.rank
  have d1 : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (1 : GL (Fin r) (AE D)) W.rank = 1 := detPow_one' W.rank
  have dcont : Continuous fun a : GL (Fin r) (AE D) => GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank := continuous_detPow' W.rank

  by_cases hz : ∃ f₀, IsThetaFunO ψ V W f₀ ∧ R f₀ ≠ 0
  swap
  · push_neg at hz
    refine ⟨1, 1, ⟨continuous_const, fun _ => rfl⟩, ⟨continuous_const, fun _ _ => rfl⟩, ?_⟩
    intro μ 𝓨 hμ a g' m _ _ f hf
    rw [hind _ (hω.om_pres _ f hf) μ 𝓨 hμ, hind f hf μ 𝓨 hμ, hz _ (hω.om_pres _ f hf), hz f hf, map_zero,
      smul_zero]
  obtain ⟨f₀, hf₀, hne⟩ := hz
  have hRth : IsThetaFunO ψ V' W (R f₀) := ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ₀ 𝓨₀ h₀).1 f₀ hf₀).2.1

  have hinj : ∀ (g' : GA D V') (v : WO V' W → ℂ), ω' (g', 1) v = 0 → v = 0 := by
    intro g' v hv
    have : ω' (g'⁻¹, 1) (ω' (g', 1) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, ← Prod.one_eq_mk, map_one,
        Module.End.one_apply]
    rw [← this, hv, map_zero]
  have huniq : ∀ (g' : GA D V') (k₁ k₂ : ℂ), k₁ • ω' (g', 1) (R f₀) = k₂ • ω' (g', 1) (R f₀) → k₁ = k₂ := by
    intro g' k₁ k₂ h
    have hw : ω' (g', 1) (R f₀) ≠ 0 := fun h0 => hne (hinj g' _ h0)
    exact smul_left_injective ℂ hw h
  let K : GL (Fin r) (AE D) → GA D V' → ℂ := fun a g' => (c a g' : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)
  have hK : ∀ a g' f, IsThetaFunO ψ V W f → R (ω (s a g', 1) f) = K a g' • ω' (g', 1) (R f) := fun a g' f hf =>
    hc a g' f hf
  have Kmul : ∀ a₁ g₁ a₂ g₂, K (a₁ * a₂) (g₁ * g₂) = K a₁ g₁ * K a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    apply huniq (g₁ * g₂)
    rw [← hK _ _ f₀ hf₀, hsmul, show ((s a₁ g₁ * s a₂ g₂, (1 : GA D W)) : GA D V × GA D W) = (s a₁ g₁, 1) * (s a₂ g₂, 1) by
      rw [Prod.mk_mul_mk, mul_one], map_mul, Module.End.mul_apply, hK _ _ _ (hω.om_pres _ f₀ hf₀), hK _ _ f₀ hf₀,
      map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have cmul : ∀ a₁ g₁ a₂ g₂, c (a₁ * a₂) (g₁ * g₂) = c a₁ g₁ * c a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    have h := Kmul a₁ g₁ a₂ g₂
    simp only [K, dmul] at h
    have hd : ((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a₁ W.rank * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a₂ W.rank : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (mul_pos (dpos a₁) (dpos a₂)).ne'
    apply Circle.coe_inj.1
    rw [Circle.coe_mul]
    apply mul_right_cancel₀ hd
    rw [h, Complex.ofReal_mul]; ring
  have c11 : c 1 1 = 1 := by
    have h := huniq 1 (K 1 1) 1 (by rw [← hK _ _ f₀ hf₀, hs1, ← Prod.one_eq_mk, ← Prod.one_eq_mk, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply, one_smul])
    simp only [K, d1, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [h, Circle.coe_one])
  let μa : GL (Fin r) (AE D) →* Circle :=
    { toFun := fun a => c a 1
      map_one' := c11
      map_mul' := fun a b => by rw [← cmul, mul_one] }
  let ξ : GA D V' →* Circle :=
    { toFun := fun g => c 1 g
      map_one' := c11
      map_mul' := fun g g' => by rw [← cmul, mul_one] }
  have csplit : ∀ a g', c a g' = μa a * ξ g' := by
    intro a g'
    have := cmul a 1 1 g'
    rwa [mul_one, one_mul] at this
  refine ⟨μa, ξ, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  ·
    obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hne
    have hΦ := GlobalTheory.T.continuous_restrictedWeilFirstFactor_apply D V V' W r C B ψ χS χT ω hω μ₀ 𝓨₀ h₀ f₀ hf₀ x₁
    have heq : ∀ a, ((μa a : Circle) : ℂ) = R (ω (d.levi a, 1) f₀) x₁ /
        ((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * R f₀ x₁) := by
      intro a
      have h := congrFun (hK a 1 f₀ hf₀) x₁
      rw [show s a 1 = d.levi a by simp [s], ← Prod.one_eq_mk, map_one, Module.End.one_apply, Pi.smul_apply,
        smul_eq_mul] at h
      rw [h, eq_div_iff (mul_ne_zero (Complex.ofReal_ne_zero.2 (dpos a).ne') hx₁)]
      simp only [K]; rw [← mul_assoc]; rfl
    refine continuous_induced_rng.2 ?_
    change Continuous fun a => ((μa a : Circle) : ℂ)
    simp only [heq]
    exact (hΦ.comp d.continuous_levi).div ((Complex.continuous_ofReal.comp dcont).mul continuous_const)
      fun a => mul_ne_zero (Complex.ofReal_ne_zero.2 (dpos a).ne') hx₁
  ·
    intro a₀
    have h := huniq 1 (K (Matrix.GeneralLinearGroup.map (incA D) a₀) 1) 1 (by
      rw [← hK _ _ f₀ hf₀, one_smul, ← Prod.one_eq_mk, map_one, Module.End.one_apply,
        show s (Matrix.GeneralLinearGroup.map (incA D) a₀) 1 = d.levi (Matrix.GeneralLinearGroup.map (incA D) a₀) by
          simp [s]]
      exact GlobalTheory.T.thetaRestriction_invariant_rationalLeviGL D V V' W r C B hs d hdC hdB ψ χS χT ω hω μ₀ 𝓨₀ h₀ a₀ f₀ hf₀)
    simp only [K] at h
    have hn := congrArg norm h
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg (dpos _).le, norm_one] at hn
    rw [hn, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [Circle.coe_one]; exact h)
  ·
    refine continuous_induced_rng.2 ?_
    change Continuous fun g => ((ξ g : Circle) : ℂ)
    rw [continuous_iff_continuousAt]
    intro g₀
    have hw : ω' (g₀, 1) (R f₀) ≠ 0 := fun h0 => hne (hinj g₀ _ h0)
    obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hw
    have hΦ := (GlobalTheory.T.continuous_restrictedWeilFirstFactor_apply D V V' W r C B ψ χS χT ω hω μ₀ 𝓨₀ h₀ f₀ hf₀ x₁).comp d.continuous_embed
    have hΨ : Continuous fun g : GA D V' => ω' (g, 1) (R f₀) x₁ :=
      (hω'.om_cont (R f₀) hRth x₁).comp (continuous_id.prodMk continuous_const)
    have heq : ∀ g, ω' (g, 1) (R f₀) x₁ ≠ 0 → ((ξ g : Circle) : ℂ) =
        R (ω (d.emb0 g, 1) f₀) x₁ / ω' (g, 1) (R f₀) x₁ := by
      intro g hg
      have h := congrFun (hK 1 g f₀ hf₀) x₁
      rw [show s 1 g = d.emb0 g by simp [s], Pi.smul_apply, smul_eq_mul] at h
      rw [h, eq_div_iff hg]
      simp only [K, d1, Complex.ofReal_one, mul_one]; rfl
    have hq : ContinuousAt (fun g => R (ω (d.emb0 g, 1) f₀) x₁ / ω' (g, 1) (R f₀) x₁) g₀ :=
      hΦ.continuousAt.div hΨ.continuousAt hx₁
    exact hq.congr ((hΨ.continuousAt.eventually_ne hx₁).mono fun g hg => (heq g hg).symm)
  ·
    intro γ hγ
    have h := huniq γ (K 1 γ) 1 (by
      rw [← hK _ _ f₀ hf₀, one_smul, show s 1 γ = d.emb0 γ by simp [s]]
      exact GlobalTheory.T.rational_unitary_acts_on_thetaRestriction_smaller D V V' W r C B hs d hdC hdB ψ χS χT ω hω χS' χT' ω' hω' μ₀ 𝓨₀ h₀ γ hγ f₀ hf₀)
    simp only [K, d1, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [Circle.coe_one]; exact h)
  ·
    intro μ 𝓨 hμ a g' m h1 h2 f hf
    obtain ⟨n, hn⟩ : ∃ n, n = (s a g')⁻¹ * m := ⟨_, rfl⟩
    have hmn : s a g' * n = m := by rw [hn, mul_inv_cancel_left]
    have hnC : HMul.hMul (mt V n) (C.map (incA D)) = C.map (incA D) := by
      rw [hn, mt_mul, Matrix.mul_assoc, h1, ← hsC a g', ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hnB : HMul.hMul (mt V n) (B.map (incA D)) = B.map (incA D) := by
      rw [hn, mt_mul, Matrix.mul_assoc, h2, ← hsB a g', ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hnI : n ∈ NI V C := hker n hnC hnB
    have hnf := hω.om_pres (n, 1) f hf
    have key : ω (m, 1) f = ω (s a g', 1) (ω (n, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, hmn]
    have hk : R (ω (n, 1) f) = R f := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ₀ 𝓨₀ h₀ ⟨n, hnI⟩ f hf
    rw [hind _ (hω.om_pres _ f hf) μ 𝓨 hμ, hind f hf μ 𝓨 hμ, key, hK a g' _ hnf, hk]
    simp only [K, csplit, Circle.coe_mul]
    congr 1
    ring

end GlobalTheory.LeviChar
