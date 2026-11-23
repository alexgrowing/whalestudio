import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ThK.ZFinDerPol

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_smul_add {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • Z) = NormedSpace.exp (s • Z) * NormedSpace.exp (t • Z) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left s).smul_right t)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem continuous_exp_smul {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
  NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem archMat_inj (hcm : IsCMExt F E σ) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F}
    (τ : EmbOver E w) {g g' : GArch σ J w} (h : GlobalTheory.Orb.archMat σ J τ g = GlobalTheory.Orb.archMat σ J τ g') : g = g' := by
  apply (archEquiv J hcm τ).injective
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm] at h
  exact Subtype.ext (Units.ext h)

theorem smul_tensNU_inl (u : AF F) (hu : evI F u = 0) (z : Ainf F ⊗[F] E) :
    u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (E := E) (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm) z = 0 := by
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  | tmul a e =>
    have key : ∀ b : AF F, b.2 = 0 → ∀ e : E, u • (b ⊗ₜ[F] e) = 0 := fun b hb e => by
      rw [TensorProduct.smul_tmul']
      have : u • b = 0 := Prod.ext (show fstA F u * b.1 = 0 by rw [h1, zero_mul]) (show u.2 * b.2 = 0 by rw [hb, mul_zero])
      rw [this, TensorProduct.zero_tmul]
    exact key (LinearMap.inl F (Ainf F) (Af F) a) rfl e

theorem at_embArch {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (y : GArch σ J w) :
    At (evI F) (((HA.mat (AF F) σ J (embArch σ J w y) : GL (Fin m) (AF F ⊗[F] E)) : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) - 1) := by
  intro u hu
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  have e := GlobalTheory.AutFunCompare.mat_extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F))
    (fun _ _ => Prod.ext rfl (mul_zero _).symm) (embArchInf σ J w y) r s
  change u • ((HA.mat (AF F) σ J (ofInf σ J (embArchInf σ J w y))).1 r s - (1 : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) r s) = 0
  rw [show ofInf σ J = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F))
    (fun _ _ => Prod.ext rfl (mul_zero _).symm) from rfl, e]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, mul_one, sub_add_cancel_left, add_sub_cancel_left]
    have hab : ∀ a b : AF F ⊗[F] E, 1 - a + b - 1 = b - a := fun a b => by ring
    rw [hab, smul_sub, smul_tensNU_inl u hu, smul_tensNU_inl u hu, sub_zero]
  · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero]
    exact smul_tensNU_inl u hu _

theorem line_back (hσ : ∀ x, σ (σ x) = x) (hcm : IsCMExt F E σ) {d : ℕ} (W : Spc F E d) {c : E} (hc : c ≠ 0)
    (γ : ℝ → GAd σ (c • W.J.map σ)) (hγ : IsRealLine σ (c • W.J.map σ) γ) :
    ∃ γ₀ ∈ Lines σ W, ∀ t, back hσ W.J hc γ t = γ₀ (Multiplicative.ofAdd t) := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  choose y hy1 hy2 using hy
  have hyadd : ∀ s t, y (s + t) = y s * y t := fun s t =>
    archMat_inj hcm _ τ (by rw [map_mul, hy2, hy2, hy2, exp_smul_add])
  have hγadd : ∀ s t, γ (s + t) = γ s * γ t := fun s t => by rw [hy1, hy1, hy1, hyadd, map_mul]
  have hγ0 : γ 0 = 1 := by
    have := hγadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hyc : Continuous y := (GlobalTheory.Orb.isEmbedding_archMat _ hcm τ).continuous_iff.2 (by
    change Continuous fun t => fun i j => GlobalTheory.Orb.archMat σ _ τ (y t) i j
    simp only [hy2]
    exact continuous_pi fun i => continuous_pi fun j => (continuous_exp_smul Z).matrix_elem i j)
  have hγc : Continuous γ := by
    rw [show γ = fun t => embArch σ _ w (y t) from funext hy1]
    exact (continuous_embArch σ _ w).comp hyc
  have hs : Continuous (toGAd hσ W.J hc).symm := continuous_induced_rng.2 continuous_subtype_val
  refine ⟨{ toFun := fun m => back hσ W.J hc γ (Multiplicative.toAdd m), map_one' := ?_, map_mul' := ?_ }, ⟨?_, ?_⟩,
    fun t => rfl⟩
  · simp [back, hγ0]
  · intro a b
    simp only [back, toAdd_mul, hγadd, map_mul]
  · exact (hs.comp hγc).comp continuous_toAdd
  · intro m
    show At (evI F) (mat ((toGAd hσ W.J hc).symm (γ (Multiplicative.toAdd m))) - 1)
    have e := toGAd_mat hσ W.J hc ((toGAd hσ W.J hc).symm (γ (Multiplicative.toAdd m)))
    rw [MulEquiv.apply_symm_apply] at e
    have e2 : mat ((toGAd hσ W.J hc).symm (γ (Multiplicative.toAdd m))) =
        ((HA.mat (AF F) σ (c • W.J.map σ) (γ (Multiplicative.toAdd m)) : GL (Fin d) (AF F ⊗[F] E)) : Matrix _ _ _) := by
      rw [e]; rfl
    rw [e2, hy1]
    exact at_embArch _ _

theorem derR_mem_polData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∀ γ : ℝ → GAd σ (c • G.W.J.map σ), IsRealLine σ (c • G.W.J.map σ) γ →
      derR om (back hσ G.W.J hc γ) Φ ∈ GlobalTheory.ThK.PolData B G.M := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' _ hT c hc _ Φ hΦ γ hγ
  obtain ⟨γ₀, hγ₀, hb⟩ := line_back hσ hT.base.cm G.W hc γ hγ
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw B G X om om' hT γ₀ hγ₀
  have key : ∃ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ y,
      HasDerivAt (fun t => om (1, back hσ G.W.J hc γ t) Φ y) (Ψ y) 0 := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := h
      refine ⟨pure (δ f) φ, Submodule.subset_span ⟨δ f, (hδ f hf).1, φ, hSB, hev, rfl⟩, fun y => ?_⟩
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
      have hR := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd
      have := (hδ f hf).2 _ hR y
      simp only [hb]
      exact this
    | zero => exact ⟨0, zero_mem _, fun y => by simpa using hasDerivAt_const (0:ℝ) (0:ℂ)⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨Ψ₁, m₁, d₁⟩ := h₁
      obtain ⟨Ψ₂, m₂, d₂⟩ := h₂
      refine ⟨Ψ₁ + Ψ₂, add_mem m₁ m₂, fun y => ?_⟩
      have h := (d₁ y).add (d₂ y)
      simp only [map_add, Pi.add_apply]
      exact h
    | smul r Φ₁ _ h₁ =>
      obtain ⟨Ψ₁, m₁, d₁⟩ := h₁
      refine ⟨r • Ψ₁, Submodule.smul_mem _ r m₁, fun y => ?_⟩
      simpa [map_smul] using (d₁ y).const_mul r
  obtain ⟨Ψ, hΨ, hd⟩ := key
  have : derR om (back hσ G.W.J hc γ) Φ = Ψ := funext fun y => (hd y).deriv
  rw [this]; exact hΨ

end GlobalTheory.ThK.ZFinDerPol
