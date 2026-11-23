import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedWeights

section Relabel

variable {ι : Type} {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P]

theorem mulSingle_relabel (l : ι ≃ ι) (τ : ι) (g : Matrix (Fin n) (Fin n) ℂ) :
    (fun ρ => (Pi.mulSingle τ g : ι → Matrix (Fin n) (Fin n) ℂ) (l.symm ρ)) = Pi.mulSingle (l τ) g := by
  funext ρ
  by_cases h : ρ = l τ
  · subst h; rw [Equiv.symm_apply_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne fun h' => h (by rw [← h', Equiv.apply_symm_apply])]

theorem isHolFam_relabel (l : ι ≃ ι) {ε : Fin n → Bool} {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} (h : IsHolFam (fun _ => ε) B ϖ) :
    IsHolFam (fun _ => ε) B fun u => ϖ fun ρ => u (l.symm ρ) := by
  refine ⟨h.1, h.2.1, fun a b ha hb => h.2.2.1 _ _ (fun _ => ha _) (fun _ => hb _), fun τ => ?_⟩
  simp only [mulSingle_relabel]
  exact h.2.2.2 (l τ)

theorem isBotFam_relabel (l : ι ≃ ι) {ε : Fin n → Bool} {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P}
    {μ : ι → Fin n → ℝ} {x : P} (h : IsBotFam (fun _ => ε) ϖ μ x) :
    IsBotFam (fun _ => ε) (fun u => ϖ fun ρ => u (l.symm ρ)) (fun τ => μ (l τ)) x := by
  intro τ
  simp only [mulSingle_relabel]
  exact h (l τ)

end Relabel

section Coef

open GlobalTheory.CoefModel GlobalTheory.CoefReal

variable {D : D7}

theorem exists_real_model (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (σ : D.what₂.LL →+* ℂ) (l : D.what₂.Tau ≃ D.what₂.Tau) (hl : ∀ ρ, labE σ (l ρ) = tauE D ρ)
    (c0 : VV D.what₂.LL lam →ₛₗ[σ] c.W) (hθ : IsInfFam θ) (hc : c.Is)
    (h1 : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, c0 (rhoVr (labLL D) lam γE v) = c.ρ (γ : GA D V) (c0 v))
    (h2 : LinearIndependent ℂ fun a => c0 (bVV D.what₂.LL lam a))
    (h3 : Submodule.span ℂ (Set.range fun a => c0 (bVV D.what₂.LL lam a)) = ⊤) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W,
      ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (invTrK fun τ => realGL θ V u (l.symm τ)) v) := by
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ v, e (mapVV σ lam v) = c0 v := exists_scalarExt σ lam c0 h2 h3
  refine ⟨e, fun u hu v => ?_⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hlab : ∀ τ x, σ (labLL D τ x) = tauE D (l.symm τ) x := fun τ x => by
    have := DFunLike.congr_fun (hl (l.symm τ)) x
    rwa [Equiv.apply_symm_apply] at this
  have hrat : ∀ (γ : GQ V) (v : VV ℂ lam),
      c.ρ γ.1 (e v) = e (rhoK lam (invTrK fun τ => realGL θ V γ.1 (l.symm τ)) v) := by
    intro γ v
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
      obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
      exact ⟨g, hg.symm⟩
    have e1 : (fun τ => Formalism.UG.bc σ (invTrK (embGL (labLL D) γE) τ)) =
        invTrK fun τ => realGL θ V γ (l.symm τ) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    have : (c.ρ γ).comp e.toLinearMap =
        e.toLinearMap.comp (rhoK lam (invTrK fun τ => realGL θ V γ (l.symm τ))) := by
      refine LinearMap.ext_on_range (span_mapVV σ lam) fun i => ?_
      show c.ρ γ (e _) = e (rhoK lam (invTrK fun τ => realGL θ V γ (l.symm τ)) _)
      rw [← e1, ← mapVV_rhoK, he, he]
      exact (h1 γ γE hγ _).symm
    exact LinearMap.congr_fun this v
  have hfin : ∀ k ∈ GfC V, realGL θ V k = 1 := fun k hk => funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V k) = 1
    rw [show infHom V k = 1 from hk, map_one]
  rw [← e.symm_apply_eq]
  refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
  let L : c.W →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap
  have hf : Continuous fun h => L (c.ρ h (e v)) := L.continuous_of_finiteDimensional.comp (hc.2.2.1 _)
  have hg : Continuous fun h => MvPolynomial.coeff m (actP lam (invTrK fun τ => realGL θ V h (l.symm τ)) v.1) := by
    refine continuous_coeff_actP lam _ (fun τ => ?_) _ m
    refine (((realGL_laws hθ V).1 (l.symm τ)).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ (l.symm τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun hf hg) hne
  refine hU ?_
  show L (c.ρ (γ * k) (e v)) = MvPolynomial.coeff m (actP lam (invTrK fun τ => realGL θ V (γ * k) (l.symm τ)) v.1)
  rw [map_mul, map_mul (realGL θ V), hc.1 k hk, hfin k hk, mul_one, mul_one, hrat ⟨γ, hγ⟩ v]
  simp [L, rhoK_coe]

theorem exists_poly_model (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (σ : D.what₂.LL →+* ℂ) (l : D.what₂.Tau ≃ D.what₂.Tau) (hl : ∀ ρ, labE σ (l ρ) = tauE D ρ)
    (c0 : VV D.what₂.LL lam →ₛₗ[σ] c.W) (hθ : IsInfFam θ) (hc : c.Is)
    (h1 : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, c0 (rhoVr (labLL D) lam γE v) = c.ρ (γ : GA D V) (c0 v))
    (h2 : LinearIndependent ℂ fun a => c0 (bVV D.what₂.LL lam a))
    (h3 : Submodule.span ℂ (Set.range fun a => c0 (bVV D.what₂.LL lam a)) = ⊤)
    (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hBS : ∀ τ, IsUnit (BS τ)) :
    ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w,
      j (c.ρ u w) = vact lam
        (fun τ => (BS (l.symm τ))⁻¹ * compAt θ (l.symm τ) (Formalism.L2.Theta.mt V u) * BS (l.symm τ)) (j w) := by
  obtain ⟨e, he⟩ := exists_real_model V θ c lam σ l hl c0 hθ hc h1 h2 h3
  choose B hB using fun τ => hBS (l.symm τ)
  refine ⟨(VV ℂ lam).subtype ∘ₗ rhoK lam (invTrK B⁻¹) ∘ₗ e.symm.toLinearMap, ?_, fun u hu w => ?_⟩
  · have hs : Function.Surjective (rhoK lam (invTrK B⁻¹)) := fun x => ⟨rhoK lam (invTrK B) x, by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]⟩
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearMap.range_eq_top.2 hs, Submodule.map_top,
      Submodule.range_subtype]
  · obtain ⟨v, rfl⟩ := e.surjective w
    have e1 : (fun τ => (BS (l.symm τ))⁻¹ * compAt θ (l.symm τ) (Formalism.L2.Theta.mt V u) * BS (l.symm τ)) =
        fun τ => (((B⁻¹ * (fun τ => realGL θ V u (l.symm τ)) * B) τ : GL (Fin V.rank) ℂ) :
          Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      rw [← hB τ, ← Matrix.coe_units_inv]
      rfl
    rw [e1, vact_eq_actP, he u hu v]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
    rw [← rhoK_coe, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      mul_inv_cancel_right]

end Coef

theorem exists_io_poly (D : D7) (V W : HSp D) (θ : InfFam D) (Sp : D.what₂.Tau → SPar) (M : DSModel W Sp)
    (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (l : D.what₂.Tau ≃ D.what₂.Tau)
    (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank) (hj1 : LinearMap.range j = VV ℂ lam)
    (hj2 : ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam
      (fun τ => (BS (l.symm τ))⁻¹ * compAt θ (l.symm τ) (Formalism.L2.Theta.mt V u) * BS (l.symm τ)) (j w))
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hr : W.rank ≤ V.rank)
    (hpq : ∀ τ, p τ + q τ = W.rank) (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ))
    (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a)
    (hK : ∀ τ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ))
    (hU : ∀ τ j, wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j = -(lam (l τ)).w j)
    (k₀ : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (hk₀ : ∀ τ, k₀ τ ∈ Formalism.REAL.Kset (M.ε τ)) :
    ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      (∀ u ∈ GinfC V, (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) →
        ∀ x w, fact M.ε x₁ x₂ x₃ 1 (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (io x w) =
          io x (c.ρ u w)) ∧
      (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
        ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ w,
          fact M.ε x₁ x₂ x₃ (Pi.mulSingle τ k) 1 (io (PiTensorProduct.tprod ℂ v) w) =
            io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w) ∧
      ∃ (v : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, ‖((v ρ : M.sm ρ) : M.H ρ)‖ = 1) ∧ ‖w‖ = 1 ∧
        io (PiTensorProduct.tprod ℂ v) w = fact M.ε x₁ x₂ x₃ k₀ 1 (delta p q ap am) := by
  obtain ⟨hhK, hhU⟩ := GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily D W.rank V.rank M.ε x₁ x₂ x₃
  obtain ⟨κ, Δ', hκ, hΔ, hbK, hbU⟩ := GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight D W.rank V.rank M.ε p q ap am x₁ x₂ x₃ hr hpq hε hap ham
  obtain ⟨m, hm1, hm2, hm3⟩ := GlobalTheory.T.holomorphic_family_low_lie_action D W Sp M _ _ _ hhK
  obtain ⟨hv1', hv2', hv3, hv4⟩ := GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest D.what₂.Tau V.rank lam
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) → Module.End ℂ (Pol ℂ D.what₂.Tau V.rank),
      ϖ = fun u => vact lam fun ρ => u (l.symm ρ) := ⟨_, rfl⟩
  have hv1 := isHolFam_relabel l hv1'
  have hv2 := isBotFam_relabel l hv2'
  rw [← hϖ] at hv1 hv2
  have eK : (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) =
      fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) := by
    funext τ a; rw [Pi.neg_apply, hK]
  have eU : (fun τ (j : Fin V.rank) => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) =
      fun τ j => -((lam (l τ)).w j : ℝ) := by
    funext τ j; rw [hU]; push_cast; rfl
  rw [eK] at hbK
  rw [eU] at hbU
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.lowest_weight_vector_transfer _ _ _ _ _ _ _ _ _ _ _ _ hhU hv1 hbU hv2 hv3
  have key : ∀ F ∈ VV ℂ lam,
      ψ F ∈ botSub M.ε (factK V.rank M.ε x₁ x₂ x₃) (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) ∧
      ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos V.rank)) →
        ψ (ϖ u F) = factU M.ε x₁ x₂ x₃ u (ψ F) := by
    intro F hF
    have hF' := GlobalTheory.T.coefficientSpace_le_span_unitary_orbit_extremal D.what₂.Tau V.rank lam hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem F h =>
      obtain ⟨u₀, hu₀, rfl⟩ := h
      obtain ⟨u, hu, e⟩ : ∃ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ,
          (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos V.rank)) ∧ vact lam u₀ = ϖ u :=
        ⟨fun τ => u₀ (l τ), fun τ => hu₀ _, by simp only [hϖ, Equiv.apply_symm_apply]⟩
      rw [e]
      refine ⟨?_, fun u' hu' => ?_⟩
      · rw [hψ u hu]
        exact hbK.map_of_commute fun g hg => commute_factU_factK _ _ _ _ (fun τ => (mem_KC_of_K (hu τ)).1) hg
      · rw [← Module.End.mul_apply, ← hv1.2.2.1 u' u (fun τ => mem_KC_of_K (hu' τ)) (fun τ => mem_KC_of_K (hu τ)),
          hψ (u' * u) (fun τ => K_mul (hu' τ) (hu τ)), hψ u hu,
          hhU.2.2.1 u' u (fun τ => mem_KC_of_K (hu' τ)) (fun τ => mem_KC_of_K (hu τ)), Module.End.mul_apply]
    | zero => exact ⟨by rw [map_zero]; exact zero_mem _, fun u _ => by simp only [map_zero]⟩
    | add a b _ _ ha hb =>
      exact ⟨by rw [map_add]; exact add_mem ha.1 hb.1, fun u hu => by simp only [map_add, ha.2 u hu, hb.2 u hu]⟩
    | smul s a _ ha =>
      exact ⟨by rw [map_smul]; exact Submodule.smul_mem _ _ ha.1, fun u hu => by simp only [map_smul, ha.2 u hu]⟩
  have hjm : ∀ w, j w ∈ VV ℂ lam := fun w => hj1 ▸ LinearMap.mem_range_self j w
  have hκ' : ∀ τ, (k₀ * κ) τ ∈ Formalism.REAL.Kset (M.ε τ) := fun τ => K_mul (hk₀ τ) (hκ τ)
  obtain ⟨v0, hv0, hmv⟩ := hm2 (k₀ * κ) hκ'
  obtain ⟨w0, hw0⟩ : (ten fun τ => extremal ℂ V.rank (lam τ)) ∈ LinearMap.range j := hj1 ▸ hv4
  have hw0' : w0 ≠ 0 := by
    rintro rfl
    exact hv3 (by rw [← hw0, map_zero])
  have hψ0 : ψ (j w0) = Δ' := by
    have := hψ 1 fun _ => one_mem_K
    rwa [hv1.2.1, hhU.2.1, Module.End.one_apply, Module.End.one_apply, ← hw0] at this
  let N : D.what₂.Tau → ℂ := fun ρ => (‖((v0 ρ : M.sm ρ) : M.H ρ)‖ : ℂ)
  have hN : ∀ ρ, ‖((v0 ρ : M.sm ρ) : M.H ρ)‖ ≠ 0 := fun ρ h =>
    hv0 ρ (Subtype.ext (Subtype.ext (norm_eq_zero.1 h)))
  have hN' : ∀ ρ, N ρ ≠ 0 := fun ρ => Complex.ofReal_ne_zero.2 (hN ρ)
  have hw1 : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw0'
  have hw2 : (‖w0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw1
  obtain ⟨io, hio⟩ : ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      ∀ x w, io x w = ((∏ ρ, N ρ) * (‖w0‖ : ℂ)) • m x (ψ (j w)) :=
    ⟨((∏ ρ, N ρ) * (‖w0‖ : ℂ)) • LinearMap.compl₂ m (ψ ∘ₗ j), fun _ _ => rfl⟩
  refine ⟨io, fun u hu hun x w => ?_, fun τ k hk v u hu w => ?_,
    fun ρ => (N ρ)⁻¹ • v0 ρ, (‖w0‖ : ℂ)⁻¹ • w0, fun ρ => ?_, ?_, ?_⟩
  · rw [hio, hio, map_smul]
    refine congrArg (HSMul.hSMul _) ?_
    have hcm := hm1 (factU M.ε x₁ x₂ x₃ fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ)
      (fun k hk => commute_factU_factK _ _ _ _ (fun τ => (mem_KC_of_K (mem_K_allPos (hun τ))).1)
        fun τ => mem_KC_of_K (hk τ)) x
    have h2 : j (c.ρ u w) = ϖ (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
      rw [hϖ]; exact hj2 u hu w
    rw [h2, (key _ (hjm w)).2 _ fun τ => mem_K_allPos (hun τ)]
    exact LinearMap.congr_fun hcm.eq _
  · rw [hio, hio, map_smul]
    refine congrArg (HSMul.hSMul _) ?_
    rw [hm3 _ (key _ (hjm w)).1 τ k hk v u hu]
    have : (fun ρ => (((Pi.mulSingle τ (k.map star) : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) ρ)⁻¹)ᵀ) =
        Pi.mulSingle τ k := by
      funext ρ
      by_cases h : ρ = τ
      · subst h; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, invT_conj hk.1]
      · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, inv_one, Matrix.transpose_one]
    rw [factK, this]
  · show ‖(N ρ)⁻¹ • ((v0 ρ : M.sm ρ) : M.H ρ)‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (hN ρ)]
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hw1]
  · rw [MultilinearMap.map_smul_univ]
    rw [map_smul, map_smul, LinearMap.smul_apply, hio, smul_smul, smul_smul, hψ0, hmv _ hbK, factK]
    have : (fun τ => ((((k₀ * κ) τ).map star)⁻¹)ᵀ) = k₀ * κ := funext fun τ => invT_conj (hκ' τ).1
    have hm := (GlobalTheory.T.fockPolynomialAction_one_mul_adjoint D W.rank V.rank M.ε x₁ x₂ x₃).2.1 k₀ κ 1 1 (fun τ => mem_KC_of_K (hk₀ τ))
      (fun τ => mem_KC_of_K (hκ τ)) (fun _ => isUnit_one) (fun _ => isUnit_one)
    rw [mul_one] at hm
    rw [this, hm, Module.End.mul_apply, hΔ, Finset.prod_inv_distrib]
    have hP : (∏ ρ, N ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hN' ρ
    convert one_smul ℂ _ using 2
    field_simp

open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in

theorem weights_label (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p q : ℕ) (hp : p = pS D i τ) (hq : q = qS D i τ)
    (lam : Fin (Wc D i).rank → ℝ) (ε : Fin (Wc D i).rank → Bool)
    (hen : IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (D.hc τ) p q)) lam ε) :
    ∃ x₁ x₂ x₃ : ℤ, (x₁ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧
      (x₂ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧
      (x₃ : ℚ) = -(((p : ℚ) - q) / 2 + (-(D.hc τ).e i + -(1 / 2))) ∧
      (∀ a, Formalism.QuantumDeterminants.lowK ε lam a = (wtK p (aPl D i p τ) (aMi D i p q τ) x₁ x₂ a : ℝ)) ∧
      (∀ j : Fin (Vc D i).rank, wtU p q (aPl D i p τ) (aMi D i p q τ) x₃ j =
        -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j) ∧
      p + q = (Wc D i).rank ∧ (∀ a, ε a = decide ((a : ℕ) < p)) ∧
      (∀ a b, a ≤ b → b < p → aPl D i p τ b ≤ aPl D i p τ a) ∧
      ∀ a b, a ≤ b → b < q → aMi D i p q τ b ≤ aMi D i p q τ a := by
  subst hp hq
  have hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s := by
    obtain ⟨a, ha⟩ := Formalism.L2.NTheta.odd_r D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    exact ⟨a + b + 1, by omega⟩
  obtain ⟨s, hs⟩ := hnr
  have hsq : (D.R.r : ℚ) + D.R.t = 2 * s := by exact_mod_cast hs
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  have A := GlobalTheory.PairWeightArith.arithAt D i τ
  obtain ⟨d, hd⟩ := A.d_int
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = 2 * s := by rw [hV, hs]; push_cast; rfl
  have hok := Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq
  obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.lowK_holPar hok hen
  obtain ⟨hn', hy⟩ := GlobalTheory.HolDS.enum_holPar hok hen
  refine ⟨-e + s, -e - s, -d, ?_, ?_, ?_, ?_, ?_, hn, ?_, A.aPlus_antitone, A.aM_anti⟩
  · rw [he, hVq]; push_cast; ring
  · rw [he, hVq]; push_cast; ring
  · have := hd
    unfold dShift at this
    push_cast
    rw [← this]
    ring
  · intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [hx x]
    congr 1
    rcases x with c | c
    · have h1 := A.kap_plus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e + s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) =
            (((aP D i τ c : ℤ) + (-e + s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_pos (by simp)]
      simp
    · have h1 := A.kap_minus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
          -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e - s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) =
            ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e - s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_neg (by simp)]
      have h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) =
          qS D i τ - 1 - c := by
        simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
        omega
      rw [h3]
  · intro j
    have h1 := A.coef_eq j
    rw [hd] at h1
    have h2 : (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d := by
      exact_mod_cast h1
    rw [h2]
    have hj := j.2
    unfold wtU thetaWt
    by_cases c1 : (j : ℕ) < pS D i τ
    · have ht := D.R.three_m_lt_t
      rw [if_pos c1, if_pos c1, if_neg (by omega)]
      ring
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : (j : ℕ) < pS D i τ + D.R.t
      · rw [if_pos c2, if_neg (by omega)]
        ring
      · rw [if_neg c2, if_pos (by omega)]
        have h3 : (Vc D i).rank - 1 - (j : ℕ) = qS D i τ - 1 - (j - (pS D i τ + D.R.t)) := by
          omega
        rw [h3]
        ring
  · intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [(hy x).2]
    rcases x with c | c <;> simp

theorem frame_mul_mem_K {m p : ℕ} {ε : Fin m → Bool} (hε : ∀ a, ε a = decide ((a : ℕ) < p))
    {F B : Matrix (Fin m) (Fin m) ℂ} (hF : IsUnit F)
    (h : IsONBasis (Fᴴ * Formalism.REAL.Jm ε * F) (F⁻¹ * Formalism.REAL.Jm ε * F) B p) : F * B ∈ Formalism.REAL.Kset ε := by
  obtain ⟨_inst⟩ := hF.nonempty_invertible
  obtain ⟨e, he, h1, h2⟩ := h
  have hJ : (Matrix.diagonal fun a => (e a : ℂ)) = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    rcases he a with h | h
    · simp [hε, h.1, h.2]
    · simp [hε, h.1, not_lt.2 h.2]
  rw [hJ] at h1 h2
  have hc : F * B * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (F * B) := by
    rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.one_mul, Matrix.mul_assoc]
  refine ⟨?_, hc⟩
  have h3 : (F * B)ᴴ * (F * B) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε := by
    rw [Matrix.mul_assoc, hc, Matrix.conjTranspose_mul]
    refine Eq.trans ?_ h1
    simp only [Matrix.mul_assoc]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h4 := congrArg (· * Formalism.REAL.Jm ε) h3
  simp only [Matrix.mul_assoc _ (Formalism.REAL.Jm ε), GlobalTheory.JointHarm.FMul.Jm_mul_Jm, Matrix.mul_one] at h4
  exact h4

theorem star_mem_K {m : ℕ} {ε : Fin m → Bool} {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    star k ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have a := Unitary.star_mul_self_of_mem hk.1
  have b := Unitary.mul_star_self_of_mem hk.1
  calc star k * Formalism.REAL.Jm ε = star k * Formalism.REAL.Jm ε * (k * star k) := by rw [b, Matrix.mul_one]
    _ = star k * (k * Formalism.REAL.Jm ε) * star k := by rw [hk.2]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.mul_assoc, a, Matrix.one_mul]

theorem fact_zero {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (P : PolF D m n) : fact ε 0 0 0 k u P = fsub ε k u P := by
  simp [fact, fchar]

theorem fact_mul_cancel {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    {k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ} (hk : ∀ τ, k τ ∈ Formalism.REAL.Kset (ε τ))
    (hk' : ∀ τ, k' τ ∈ Formalism.REAL.Kset (ε τ)) (h : k * k' = 1) (P : PolF D m n) :
    fact ε x₁ x₂ x₃ k 1 (fact ε x₁ x₂ x₃ k' 1 P) = P := by
  have H := GlobalTheory.T.fockPolynomialAction_one_mul_adjoint D m n ε x₁ x₂ x₃
  have hm := H.2.1 k k' 1 1 (fun τ => mem_KC_of_K (hk τ))
    (fun τ => mem_KC_of_K (hk' τ)) (fun _ => isUnit_one) (fun _ => isUnit_one)
  rw [mul_one, h, H.1] at hm
  rw [← Module.End.mul_apply, ← hm, Module.End.one_apply]

theorem isIoW_comp {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel W S'} {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt pt' : PolF D W.rank V.rank → (WO V W → ℂ)}
    {Δ Δ' : PolF D W.rank V.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank}
    (h : IsIoW θ M c ω pt Δ io) (L : Module.End ℂ (PolF D W.rank V.rank)) (a : ℂ) (hL : ∀ P, pt' (L P) = a • pt P)
    (hΔ : L Δ = Δ') : IsIoW θ M c ω pt' Δ' (io.compr₂ L) := by
  obtain ⟨h1, h2, v, w, hv, hw, h3⟩ := h
  refine ⟨fun u hu x w => ?_, fun τ k hk v u hu w => ?_, v, w, hv, hw, ?_⟩
  · rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, hL, hL, map_smul, h1 u hu]
  · rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, hL, hL, map_smul, h2 τ k hk v u hu]
  · rw [LinearMap.compr₂_apply, h3, hΔ]

theorem isIoW_of_fact {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} {θ : InfFam D} (hθ : IsInfFam θ)
    {M : DSModel W S'} {c : CoefA V} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {pt : PolF D W.rank V.rank → (WO V W → ℂ)} {Δ : PolF D W.rank V.rank}
    {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} {x₁ x₂ x₃ : D.what₂.Tau → ℤ}
    {BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hBu : ∀ τ, IsUnit (BS τ))
    (hact : ∀ g ∈ GinfC V, ∀ h ∈ GinfC W,
      (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt W h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) →
      (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V g) * BS τ ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) ∧
      ∀ P : PolF D W.rank V.rank, ω (g, h) (pt P) =
        pt (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt W h) * (M.fr τ)⁻¹)
          (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V g) * BS τ) P))
    (h1 : ∀ u ∈ GinfC V, (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) →
        ∀ x w, fact M.ε x₁ x₂ x₃ 1 (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (io x w) =
          io x (c.ρ u w))
    (h2 : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
        ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ w,
          fact M.ε x₁ x₂ x₃ (Pi.mulSingle τ k) 1 (io (PiTensorProduct.tprod ℂ v) w) =
            io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w)
    (h3 : ∃ (v : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, ‖((v ρ : M.sm ρ) : M.H ρ)‖ = 1) ∧ ‖w‖ = 1 ∧
        io (PiTensorProduct.tprod ℂ v) w = Δ) : IsIoW θ M c ω pt Δ io := by
  have hfr : ∀ τ, M.fr τ * (M.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  refine ⟨fun u hu x w => ?_, fun τ k hk v u hu w => ?_, h3⟩
  · have e : (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt W 1) * (M.fr τ)⁻¹) = 1 := by
      funext τ; rw [compAt_mt_one', Matrix.mul_one, hfr]; rfl
    obtain ⟨a, b⟩ := hact u hu 1 (one_mem _) fun τ => by rw [congrFun e τ]; exact one_mem_K
    rw [← h1 u hu a x w]
    have := b (io x w)
    rw [e] at this
    exact this
  · have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ W τ (conj_mem_UH M τ hk)
    have e : (fun ρ => M.fr ρ * compAt θ ρ (Formalism.L2.Theta.mt W (atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ))) *
        (M.fr ρ)⁻¹) = Pi.mulSingle τ k := by
      funext ρ
      rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
      by_cases h : ρ = τ
      · subst h
        rw [hs.2.1, Pi.mulSingle_eq_same]
        calc _ = (M.fr ρ * (M.fr ρ)⁻¹) * k * (M.fr ρ * (M.fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
      · rw [hs.2.2 ρ h, Pi.mulSingle_eq_of_ne h, Matrix.mul_one, hfr]
    have e' : (fun ρ => (BS ρ)⁻¹ * compAt θ ρ (Formalism.L2.Theta.mt V 1) * BS ρ) = 1 := by
      funext ρ
      rw [compAt_mt_one', Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]; rfl
    obtain ⟨-, b⟩ := hact 1 (one_mem _) _ hs.1 fun ρ => by
      rw [congrFun e ρ]
      by_cases h : ρ = τ
      · subst h; rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_K
    rw [← h2 τ k hk v u hu w]
    have := b (io (PiTensorProduct.tprod ℂ v) w)
    rw [e, e'] at this
    exact this

theorem exists_isIoW (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (Sp : D.what₂.Tau → SPar)
    (M : DSModel W Sp) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (l : D.what₂.Tau ≃ D.what₂.Tau)
    (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank) (hj1 : LinearMap.range j = VV ℂ lam)
    (hj2 : ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam
      (fun τ => (BS (l.symm τ))⁻¹ * compAt θ (l.symm τ) (Formalism.L2.Theta.mt V u) * BS (l.symm τ)) (j w))
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hr : W.rank ≤ V.rank)
    (hpq : ∀ τ, p τ + q τ = W.rank) (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ))
    (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a)
    (hK : ∀ τ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ))
    (hU : ∀ τ j, wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j = -(lam (l τ)).w j)
    (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (hω : IsWeilDatumO ψ V W χS χT ω) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.SigOK) (hW : W.SigOK)
    (hBS : ∀ τ, (BS τ)ᴴ * gramAt D V τ * BS τ = 1) (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D χS τ (a τ)) (hb : ∀ τ, HasInfExp D χT τ (b τ))
    (hx₁ : ∀ τ, (x₁ τ : ℚ) = a τ + (V.rank : ℚ) / 2) (hx₂ : ∀ τ, (x₂ τ : ℚ) = a τ - (V.rank : ℚ) / 2)
    (hx₃ : ∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) (f : WO V W → ℂ) (hth : IsThetaFunO ψ V W f)
    (hvac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f) :
    ∃ io, IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BS B f) (delta p q ap am) io := by
  have hBu : ∀ τ, IsUnit (BS τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  have hk : ∀ τ, M.fr τ * B τ ∈ Formalism.REAL.Kset (M.ε τ) := fun τ =>
    frame_mul_mem_K (hε τ) (M.fr_unit τ) (by rw [M.fr_gram τ]; exact hB τ)
  obtain ⟨k, hkd⟩ : ∃ k : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, ∀ τ, k τ = M.fr τ * B τ := ⟨_, fun _ => rfl⟩
  simp only [← hkd] at hk
  have hBk : B = fun τ => onb M τ * k τ := by
    funext τ
    rw [hkd, onb, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), Matrix.one_mul]
  have hk' : ∀ τ, (fun τ => star (k τ)) τ ∈ Formalism.REAL.Kset (M.ε τ) := fun τ => star_mem_K (hk τ)
  have hkk : k * (fun τ => star (k τ)) = 1 := funext fun τ => Unitary.mul_star_self_of_mem (hk τ).1
  have hkk' : (fun τ => star (k τ)) * k = 1 := funext fun τ => Unitary.star_mul_self_of_mem (hk τ).1
  obtain ⟨io, h1, h2, h3⟩ := exists_io_poly D V W θ _ M c lam l BS j hj1 hj2 _ _ _ _ x₁ x₂ x₃ hr hpq hε hap ham hK hU k hk
  have hact := GlobalTheory.T.weil_maximalCompact_fock_substitution_character D ψ θ V W _ _ ω _ M BS hω hθ hV hW hBS _ _ hpq hε _ _ ha hb x₁ x₂ x₃ hx₁ hx₂ hx₃ f hth hvac
  have hio := isIoW_of_fact hθ hBu hact h1 h2 h3
  refine ⟨_, isIoW_comp hio (fact M.ε x₁ x₂ x₃ (fun τ => star (k τ)) 1)
    (fchar (n := V.rank) M.ε x₁ x₂ x₃ (fun τ => star (k τ)) 1) (fun P => ?_)
    (fact_mul_cancel _ _ _ _ hk' hk hkk' _)⟩
  have hb := GlobalTheory.FockBasis.pureTensorO_basis D ψ θ V W _ M BS hψ hθ hBS k 1 hk
    (fun _ => one_mem _) f hth (fsub M.ε (fun τ => star (k τ)) 1 P)
  have hcan := fact_mul_cancel M.ε 0 0 0 hk hk' hkk P
  rw [fact_zero, fact_zero] at hcan
  have e1 : (fun τ => BS τ * (1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ) = BS :=
    funext fun τ => Matrix.mul_one _
  rw [hcan, e1, ← hBk] at hb
  rw [← hb, ← map_smul]
  rfl

end GlobalTheory.MovedWeights

end
