import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CtInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_ht {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous fun x : UA σ J => (ht x : ℝ) := by
  have h : Continuous fun x : UA σ J => heightGL F (x : GL (Fin n) (AE F E)) :=
    (GlobalTheory.Grow.continuous_heightGL (F := F) (E := E) (n := Fin n)).comp continuous_subtype_val
  exact NNReal.continuous_coe.comp h

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : UA σ J) : (1 : ℝ) ≤ ht x := by
  have := GlobalTheory.AdelicU.one_le_heightGL F (x : GL (Fin n) (AE F E))
  exact_mod_cast this

theorem ht_mul_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) : (ht (x * y) : ℝ) ≤ ht x * ht y := by
  have := GlobalTheory.AdelicU.heightGL_mul_le (F := F) (x : GL (Fin n) (AE F E)) (y : GL (Fin n) (AE F E))
  exact_mod_cast this

theorem stronglyMeasurable_I {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d)
    (hc : Continuous fun x : UA σ X.J × UA σ W.J => theta om Φ x.1 x.2) (hμ : M.μ.IsHaarMeasure) :
    StronglyMeasurable (M.I om Φ) := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := hμ
  haveI : SigmaCompactSpace (UA σ X.J) := inferInstance
  haveI : IsFiniteMeasureOnCompacts M.μ := inferInstance
  haveI : SigmaFinite M.μ := inferInstance
  haveI : SigmaFinite (M.μ.restrict M.dom) := Restrict.sigmaFinite _ _
  haveI : SFinite (M.μ.restrict M.dom) := instSFiniteOfSigmaFinite
  have h2 : StronglyMeasurable (Function.uncurry fun (x : UA σ W.J) (g : UA σ X.J) => theta om Φ g x) :=
    (hc.comp continuous_swap).stronglyMeasurable
  exact h2.integral_prod_right (ν := M.μ.restrict M.dom)

end GlobalTheory.CtInt

namespace GlobalTheory.CtInt

theorem integrableOn_ct : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), ∀ h : UA σ G.W.J, IntegrableOn (fun u : unip σ G.W H' => G.M.I om Ψ (u.1 * h)) 𝓕 μ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH μ 𝓕 _ _ h1 Ψ hΨ h
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  obtain ⟨hcont, hinv, -⟩ := (hTB F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hV).1 Ψ hΨ
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have := hT.geo.eBig
    have := hT.geo.lt
    omega
  obtain ⟨-, C, k, hC⟩ := (GlobalTheory.T.weil_convergence_of_kernel hK F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hV hcond).1 Ψ hΨ
  have hbd : ∀ x, ‖G.M.I om Ψ x‖ ≤ C * (ht x : ℝ) ^ k := fun x =>
    (norm_integral_le_integral_norm _).trans (hC x)
  have hC0 : 0 ≤ C := by
    have h0 : 0 ≤ C * (ht (1 : UA σ G.W.J) : ℝ) ^ k := (norm_nonneg _).trans (hbd 1)
    exact nonneg_of_mul_nonneg_left h0 (pow_pos (zero_lt_one.trans_le (one_le_ht _)) k)
  have hrat : ∀ γ ∈ ratU σ G.W.J, ∀ x, G.M.I om Ψ (γ * x) = G.M.I om Ψ x := by
    intro γ hγ x
    unfold Model.I
    congr 1
    funext g
    simpa using hinv 1 (one_mem _) γ hγ g x
  have hcoc : GlobalTheory.Cusp.Cocompact (ratU σ G.W.J) (unip σ G.W H') :=
    GlobalTheory.UnipCocompact.cocompact_unip F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨Kc, hKc, hcov⟩ := hcoc
  obtain ⟨Bd, hBd⟩ := hKc.exists_bound_of_continuousOn
    (((continuous_ht (σ := σ) G.W.J).comp continuous_subtype_val).continuousOn (s := Kc))
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hmeas : StronglyMeasurable (G.M.I om Ψ) := stronglyMeasurable_I G.M om Ψ hcont hT.geo.hM.haar
  have hm2 : Measurable fun u : unip σ G.W H' => u.1 * h :=
    (continuous_subtype_val.mul continuous_const).measurable
  refine Measure.integrableOn_of_bounded (M := C * (Bd * ht h) ^ k) (by rw [h1]; exact ENNReal.one_ne_top)
    (hmeas.comp_measurable hm2).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  obtain ⟨γ, hγ, hk⟩ := hcov u
  have e : G.M.I om Ψ (u.1 * h) = G.M.I om Ψ ((γ * u).1 * h) := by
    rw [Subgroup.coe_mul, mul_assoc, hrat _ (Subgroup.mem_subgroupOf.1 hγ)]
  have hB : (ht (γ * u).1 : ℝ) ≤ Bd := by
    have := hBd _ hk
    simp only [Function.comp_apply, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hle : (ht ((γ * u).1 * h) : ℝ) ≤ Bd * ht h :=
    (ht_mul_le _ _).trans (mul_le_mul_of_nonneg_right hB (NNReal.coe_nonneg _))
  show ‖G.M.I om Ψ (u.1 * h)‖ ≤ C * (Bd * ht h) ^ k
  rw [e]
  exact (hbd _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hle k) hC0)

end GlobalTheory.CtInt
