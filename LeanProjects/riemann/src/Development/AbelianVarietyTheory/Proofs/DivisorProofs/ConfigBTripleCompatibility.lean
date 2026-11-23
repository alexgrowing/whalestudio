import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBConstantTermThetaLiftStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.StepBAn

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hasSig_pos_aniso {n r : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r 0) (y : Fin n → ℂ)
    (hy : y ⬝ᵥ M *ᵥ star y = 0) : y = 0 := by
  obtain ⟨hs, A, hA⟩ := h
  let e : (Fin r ⊕ Fin 0) ≃ Fin n := (Equiv.sumEmpty (Fin r) (Fin 0)).trans (finCongr (by omega))
  set D : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have h1 : Aᵀ * (M * A.map star * D) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
  have h2 : (M * A.map star * D) * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  have h3 : A * (M * A.map star * D)ᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  set w := (M * A.map star * D)ᵀ *ᵥ y
  have hyw : y = A *ᵥ w := by rw [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  have hst : star (A *ᵥ w) = A.map star *ᵥ star w := by
    ext i; simp [Matrix.mulVec, dotProduct, star_sum]
  have key : y ⬝ᵥ M *ᵥ star y = w ⬝ᵥ D *ᵥ star w := by
    rw [← hA, hyw, hst, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have h0 : w ⬝ᵥ D *ᵥ star w = 0 := key.symm.trans hy
  have hsum : ∑ i : Fin r, w (Sum.inl i) * star (w (Sum.inl i)) = 0 := by
    simp [hD, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type] at h0
    simpa [Matrix.one_apply] using h0
  have hz : ∀ i, w (Sum.inl i) = 0 := by
    have hr : ∑ i : Fin r, Complex.normSq (w (Sum.inl i)) = 0 := by
      have : ((∑ i : Fin r, Complex.normSq (w (Sum.inl i)) : ℝ) : ℂ) = 0 := by
        rw [← hsum]; push_cast; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def, Complex.mul_conj]
      exact_mod_cast this
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (w (Sum.inl j)))).mp hr i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  have hw : w = 0 := by
    funext i; rcases i with i | i
    · exact hz i
    · exact i.elim0
  rw [hyw, hw, Matrix.mulVec_zero]

theorem aniso_of_herm_pos {n r : ℕ} (B : Base F E) (hB : B.IsGood σ) (X : Spc F E n) (h : X.IsHerm σ B r 0) :
    ∀ x, form σ X.J x x = 0 → x = 0 := by
  intro x hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let τ : E →+* ℂ := (B.emb w).1
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  have hy : (fun i => τ (x i)) ⬝ᵥ (X.J.map τ) *ᵥ star (fun i => τ (x i)) = 0 := by
    have := congrArg τ hx
    rw [map_zero] at this
    have hs : (star fun i => τ (x i)) = τ ∘ fun i => σ (x i) := by
      ext i; simp [hcm]
    rw [← this, hs, form, RingHom.map_dotProduct]
    show (τ ∘ x) ⬝ᵥ _ = (τ ∘ x) ⬝ᵥ _
    congr 1
    ext i
    exact (RingHom.map_mulVec τ X.J _ i).symm
  have := hasSig_pos_aniso (h.sig w) _ hy
  funext i
  exact τ.injective (by simpa using congrFun this i)

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.mpr ?_
  rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v h => h.1.trans h.2)

end GlobalTheory.ThK.StepBAn

noncomputable section

namespace GlobalTheory.ThK.StepBAn

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem setIntegral_fd_smul {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (Γ : Subgroup N) [Countable Γ]
    (g : N → ℂ) (hg : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x)
    (μ μ₀ : Measure N) [μ.IsHaarMeasure] [μ₀.IsHaarMeasure] (𝓕 𝓕₀ : Set N)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕₀ : IsFundamentalDomain Γ 𝓕₀ μ₀) :
    ∫ x in 𝓕, g x ∂μ = (Measure.haarScalarFactor μ μ₀ : ℝ) • ∫ x in 𝓕₀, g x ∂μ₀ := by
  letI : MeasurableSpace Γ := ⊤
  haveI : MeasurableSMul Γ N :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : N)
      measurable_smul_const := fun _ => measurable_from_top }
  have hs := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : Measure.haarScalarFactor μ μ₀ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ₀ := by
    refine h𝓕.mono ?_
    rw [hs]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have e1 := h𝓕'.setIntegral_eq h𝓕₀ (fun γ x => hg γ γ.2 x)
  conv_lhs => rw [hs]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, e1, NNReal.smul_def]

theorem setIntegral_fd_unitary {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (μ μ₀ : Measure (UA σ J)) [μ.IsHaarMeasure]
    [μ₀.IsHaarMeasure] (𝓕 𝓕₀ : Set (UA σ J)) (h𝓕 : IsFundamentalDomain (ratU σ J) 𝓕 μ)
    (h𝓕₀ : IsFundamentalDomain (ratU σ J) 𝓕₀ μ₀) (g : UA σ J → ℂ) (hg : ∀ γ ∈ ratU σ J, ∀ x, g (γ * x) = g x) :
    ∃ c : ℝ, ∫ x in 𝓕, g x ∂μ = c • ∫ x in 𝓕₀, g x ∂μ₀ := by
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ J
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) (F := F) J
  exact ⟨_, setIntegral_fd_smul (ratU σ J) g hg μ μ₀ 𝓕 𝓕₀ h𝓕 h𝓕₀⟩

end GlobalTheory.ThK.StepBAn

open GlobalTheory.ThK.StepBAn in

theorem GlobalTheory.ThK.stepB_anisotropic : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)) (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → G.p = 0 →
    ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∀ Φ ∈ PolData B G.M, G.M.I om Φ = 0 → G₁.M.I om₁ (e Φ) = 0 := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ hp e he Φ hΦ hI
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain rfl : V₁ = G.V := hC.eV
  have hp₁ : p₁ = G.p := hC.ep
  have hH' : H'.IsAdapted σ B G.W W₁ a (a + b + 1) := hC.hH'
  have hP := (Check.isPair_of_isTriple hT).1
  have hP₁ := (Check.isPair_of_isTriple hT₁).1
  simp only at hP₁
  rw [hp₁] at hP₁
  have hΦs : Φ ∈ schA F _ := polData_le_schA B G.M hT.geo.hM hΦ
  have hV := hT.geo.hV
  rw [hp, Nat.sub_zero] at hV
  have han := aniso_of_herm_pos B hT.base G.V hV
  obtain ⟨C₀, hC₀, h1, -⟩ := GlobalTheory.T.adapted_plane_evaluation_constant hKP F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ G.M M₁ H' a (a + b + 1) hH'
    hT₁.geo.hM e he
  have hct : ∀ g, IsCT H' (theta om Φ g) (fun h => C₀ * thetaSum F (e (om (g, h) Φ))) :=
    fun g => h1 han _ _ _ _ _ _ _ hP Φ hΦs g
  have hfub := GlobalTheory.T.config_b_constant_term_theta_lift hKP F E σ B a b G ⟨p₁, q₁, G.V, V₁', W₁, M₁, M₁'⟩ H H' hC X om om' hT Φ hΦ _ hct
  funext h₁
  obtain ⟨m, hm⟩ := exists_isLevi_unitary_smaller F E σ B _ _ G.W W₁ H' a (a + b + 1) _ _ _ _ hT.base hT.geo.hW
    hT₁.geo.hW hH' h₁
  obtain ⟨μ, 𝓕, hμ, h𝓕, hμ1⟩ := GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a (b + 2) G X om om' hT (a + b) W₁ H' a (a + b + 1) hH'
  have k := hfub μ 𝓕 hμ h𝓕 hμ1 m
  simp only [hI, Pi.zero_apply, integral_zero] at k
  have hlaw : ∀ g, e (om (g, m) Φ) = om₁ (g, h₁) (e Φ) := by
    intro g
    have := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP (a + b) W₁ H' a
      (a + b + 1) M₁ om₁ _ _ hH' hP₁ e he g 1 h₁ m hm 1 (one_mem _) Φ hΦs
    simpa using this
  simp only [hlaw, integral_const_mul] at k
  have k2 : ∫ g in G.M.dom, theta om₁ (e Φ) g h₁ ∂G.M.μ = 0 := by
    rcases mul_eq_zero.1 k with h | h
    · exact absurd h hC₀
    · exact h
  obtain ⟨-, hinv, -⟩ := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B a (a + b) G.V W₁ M₁ X.β (X.β / X.α) om₁ _ _ _ _ hP₁).1 (e Φ)
    (he.maps Φ hΦs)
  haveI := hT.geo.hM.haar
  haveI := hT₁.geo.hM.haar
  show ∫ g in M₁.dom, theta om₁ (e Φ) g h₁ ∂M₁.μ = 0
  obtain ⟨c, hc⟩ := setIntegral_fd_unitary G.V.J M₁.μ G.M.μ M₁.dom G.M.dom hT₁.geo.hM.dom hT.geo.hM.dom
    (fun g => theta om₁ (e Φ) g h₁)
    (fun γ hγ x => by simpa using hinv γ hγ 1 (one_mem _) x h₁)
  rw [hc, k2, smul_zero]
