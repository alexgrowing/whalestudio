import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearStableRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThKFunInf

theorem integral_translate (hB : ThetaBasic) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') (g : UA σ X.J)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin n × Fin d)) : M.I om (om (g, 1) Φ) = M.I om Φ := by
  funext y
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, theta om Φ (γ * x) y = theta om Φ x y := by
    intro γ hγ x
    have := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x y
    rwa [one_mul] at this
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := GlobalTheory.ThetaRightTranslate.isMulRightInvariant σ hp.base.cm X.J hp.herm.herm
    (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ
  haveI := GlobalTheory.ThetaRightTranslate.countable_ratU σ X.J
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : M.I om (om (g, 1) Φ) y = ∫ x in M.dom, theta om Φ (x * g) y ∂M.μ := by
    unfold Model.I theta
    congr 1
    funext x
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hmp := measurePreserving_mul_right M.μ g
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g) (fun x => theta om Φ x y)
    ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd'.setIntegral_eq hp.good.dom (f := fun x => theta om Φ x y) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl

theorem rest_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    Rest (evI F) (⇑f) (fun x : κ → AF F => g fun i => (x i).2) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have h0 : ∀ i, (z i).2 = 0 := fun i => by
      have e := congrFun (GlobalTheory.ThK.partInf_of_at hz) i
      rw [← e]
      show ((realAd F 1 • z) i).2 = 0
      simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul]
      show (realAd F 1).2 * (z i).2 = 0
      rw [show (realAd F 1).2 = 0 from rfl, zero_mul]
    have e : (fun i => ((x + z) i).2) = fun i => (x i).2 := funext fun i => by
      show (x i + z i).2 = _
      calc (x i + z i).2 = (x i).2 + (z i).2 := rfl
        _ = (x i).2 := by rw [h0 i, add_zero]
    exact congrArg g e
  · exact Submodule.subset_span ⟨f, g, hg, rfl⟩

end GlobalTheory.ThKFunInf

namespace GlobalTheory.ThKFunInf

theorem funInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) (h : UA σ G.W.J),
      (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = G.M.vac w) →
      ∃ l : SInf F (Fin a × Fin (a + a')) →L[ℂ] ℂ, (∀ f, l f = G.M.I om (pure f φ) h) ∧
        ∀ g ∈ UAt σ G.V (evI F), ∀ f f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, 1)) f f₁ → l f₁ = l f := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT φ h hφ hvac
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    left
    have h1 := hT.geo.eBig
    have h3 := hT.geo.lt
    omega
  have hWC := GlobalTheory.T.weil_convergence_of_kernel hKP
  have hlin := GlobalTheory.ThKLin.I_linear hWC F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond h
  let A : (Fin a × Fin (a + a') → Af F) → ℂ := fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : A ∈ SB (Fin a × Fin (a + a') → Af F) :=
    GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hφ ((hvac.and hP.good.std).mono fun v hv => hv.1.trans hv.2)
  have hcont := (hWC F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond).2 A hA h
  have hpure : ∀ f : SInf F (Fin a × Fin (a + a')), pureA F f A ∈ schA F (Fin a × Fin (a + a')) :=
    fun f => Submodule.subset_span ⟨f, A, hA, rfl⟩
  have hzero : G.M.I om 0 h = 0 := by
    have := hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  let T : SInf F (Fin a × Fin (a + a')) →L[ℂ] ℂ :=
    { toFun := fun f => G.M.I om (pureA F f A) h
      map_add' := fun f f' => by
        have e : pureA F (⇑(f + f')) A = (1 : ℂ) • pureA F f A + pureA F f' A := by
          funext x; simp [pureA, add_mul]
        simp only [e]
        rw [hlin _ (hpure f) _ (hpure f'), one_mul]
      map_smul' := fun c f => by
        have e : pureA F (⇑(c • f)) A = c • pureA F f A + 0 := by
          funext x; simp [pureA, mul_assoc]
        simp only [e, RingHom.id_apply, smul_eq_mul]
        rw [hlin _ (hpure f) _ (Submodule.zero_mem _), hzero, add_zero]
      cont := hcont }
  refine ⟨T, fun f => rfl, fun g _ f f₁ hact => ?_⟩
  have e : om (g, 1) (pureA F f A) = pureA F f₁ A := hact _ (rest_pureA f hA)
  change G.M.I om (pureA F f₁ A) h = G.M.I om (pureA F f A) h
  rw [← e, integral_translate (GlobalTheory.T.theta_basic_properties hKP.base) hP g _ (hpure f)]

end GlobalTheory.ThKFunInf
