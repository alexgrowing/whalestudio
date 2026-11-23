import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefReal

open GlobalTheory.CoefModel

theorem vact_eq_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK g) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Pi.inv_apply, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem continuous_coeff_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {X : Type} [TopologicalSpace X]
    (A : X → ι → GL (Fin n) ℂ) (hA : ∀ τ, Continuous fun x => (A x τ : Matrix (Fin n) (Fin n) ℂ)) (F : Pol ℂ ι n)
    (m : ι × Fin n × Fin n →₀ ℕ) : Continuous fun x => MvPolynomial.coeff m (actP lam (A x) F) := by
  simp only [actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul, detTw_eq, AlgHom.toLinearMap_apply, trAct]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hA τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_coeff_blockAct _ (fun τ => (hA τ).matrix_transpose) _ m)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (A x τ).isUnit).ne_zero

theorem exists_scalarExt {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    {W : Type} [AddCommGroup W] [Module ℂ W] (c0 : VV K lam →ₛₗ[φ] W)
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] W, ∀ v, e (mapVV φ lam v) = c0 v := by
  let b1 := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  let b2 := Module.Basis.mk h1 h2.ge
  refine ⟨b1.equiv b2 (Equiv.refl _), fun v => ?_⟩
  have : (b1.equiv b2 (Equiv.refl _)).toLinearMap.comp (mapVV φ lam) = c0 := by
    refine (bVV K lam).ext fun i => ?_
    have h := b1.equiv_apply i b2 (Equiv.refl _)
    simpa [b1, b2] using h
  exact LinearMap.congr_fun this v

variable {D : D7}

theorem exists_real_model (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W) (hθ : IsInfFam θ) (hc : c.Is)
    (ht : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam)) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, (∀ v, e (mapVV D.what₂.embLL lam v) = c0 v) ∧
      ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (invTrK (realGL θ V u)) v) := by
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ v, e (mapVV D.what₂.embLL lam v) = c0 v :=
    exists_scalarExt D.what₂.embLL lam c0 ht.2.1 ht.2.2
  refine ⟨e, he, fun u hu v => ?_⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have hrat : ∀ (γ : GQ V) (v : VV ℂ lam), c.ρ γ.1 (e v) = e (rhoK lam (invTrK (realGL θ V γ.1)) v) := by
    intro γ v
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
      obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
      exact ⟨g, hg.symm⟩
    have e1 : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    have : (c.ρ γ).comp e.toLinearMap = e.toLinearMap.comp (rhoK lam (invTrK (realGL θ V γ))) := by
      refine LinearMap.ext_on_range (span_mapVV D.what₂.embLL lam) fun i => ?_
      show c.ρ γ (e _) = e (rhoK lam (invTrK (realGL θ V γ)) _)
      rw [← e1, ← mapVV_rhoK, he, he]
      exact (ht.1 γ γE hγ _).symm
    exact LinearMap.congr_fun this v
  have hfin : ∀ k ∈ GfC V, realGL θ V k = 1 := fun k hk => funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V k) = 1
    rw [show infHom V k = 1 from hk, map_one]
  rw [← e.symm_apply_eq]
  refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
  let L : c.W →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap
  have hf : Continuous fun h => L (c.ρ h (e v)) := L.continuous_of_finiteDimensional.comp (hc.2.2.1 _)
  have hg : Continuous fun h => MvPolynomial.coeff m (actP lam (invTrK (realGL θ V h)) v.1) := by
    refine continuous_coeff_actP lam _ (fun τ => ?_) _ m
    refine (((realGL_laws hθ V).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun hf hg) hne
  refine hU ?_
  show L (c.ρ (γ * k) (e v)) = MvPolynomial.coeff m (actP lam (invTrK (realGL θ V (γ * k))) v.1)
  rw [map_mul, map_mul (realGL θ V), hc.1 k hk, hfin k hk, mul_one, mul_one, hrat ⟨γ, hγ⟩ v]
  simp [L, rhoK_coe]

theorem exists_poly_model : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is → Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∀ BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (BS τ)) → ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
  intro D V θ c lam c0 hθ hc ht BS hBS
  obtain ⟨e, -, he⟩ := exists_real_model V θ c lam c0 hθ hc ht
  choose B hB using hBS
  refine ⟨(VV ℂ lam).subtype ∘ₗ rhoK lam (invTrK B⁻¹) ∘ₗ e.symm.toLinearMap, ?_, fun u hu w => ?_⟩
  · have hs : Function.Surjective (rhoK lam (invTrK B⁻¹)) := fun x => ⟨rhoK lam (invTrK B) x, by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]⟩
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearMap.range_eq_top.2 hs, Submodule.map_top,
      Submodule.range_subtype]
  · obtain ⟨v, rfl⟩ := e.surjective w
    have e1 : (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) =
        fun τ => (((B⁻¹ * realGL θ V u * B) τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      rw [← hB τ, ← Matrix.coe_units_inv]
      rfl
    rw [e1, vact_eq_actP, he u hu v]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
    rw [← rhoK_coe, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      mul_inv_cancel_right]

end GlobalTheory.CoefReal

end
