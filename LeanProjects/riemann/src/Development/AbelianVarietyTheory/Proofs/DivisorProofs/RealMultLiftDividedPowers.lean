import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralSmoothAlongRealLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLaplacianPolDataStatement

noncomputable section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ThKSmoothDer

theorem lieA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (τ : EmbOver E w)
    (Z : Matrix (Fin n) (Fin n) ℂ) (y : ℝ → GArch σ J w),
    (∀ t : ℝ, GlobalTheory.Orb.archMat σ J τ (y t) = NormedSpace.exp (t • Z)) →
    Z.conjTranspose * J.map τ.1 + J.map τ.1 * Z = 0 := GlobalTheory.T.one_parameter_skew_hermitian

theorem fockD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ Δ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ (SInf F (Fin a × Fin (a + a'))),
        (∀ Z, ∀ f ∈ G.M.Pol B.ψ B.emb, Δ Z f ∈ G.M.Pol B.ψ B.emb) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ f ∈ G.M.Pol B.ψ B.emb,
            ActsD (evI F) (fun t => om (1, (toGAd hσ G.W.J hc).symm (γ t))) f (Δ Z f) := GlobalTheory.T.archimedean_laplacian_pol_data

section Assembly
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasDerivAt_pure {κ : Type} [Fintype κ] (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f f₁ : SInf F κ}
    (h : ActsD (evI F) (fun t => T t) f f₁) (φ : (v : Pl F) → (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (hvac : ∀ᶠ v : Pl F in Filter.cofinite,
      φ v = {x | ∀ (i : κ), x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}.indicator 1)
    (y : κ → AF F) : HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) y) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ y) 0 := by
  rw [GlobalTheory.EvZeroInf.pure_eq_tens, GlobalTheory.EvZeroInf.pure_eq_tens]
  exact h _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hvac) y

theorem pure_add {κ : Type} [Fintype κ] (f g : SInf F κ) (φ : (v : Pl F) → (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_rsmul {κ : Type} [Fintype κ] (r : ℝ) (f : SInf F κ) (φ : (v : Pl F) → (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (r • f) φ = r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_zero {κ : Type} [Fintype κ] (φ : (v : Pl F) → (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

end Assembly

theorem hasDerivAt_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ D : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ),
        (∀ Z, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, D Z Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ x, HasDerivAt (fun s : ℝ => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (x * γ s)))
            (G.M.I om (D Z Φ) ((toGAd hσ G.W.J hc).symm x)) 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcσ w τ
  classical
  obtain ⟨Δ, hΔpol, hΔ⟩ := fockD F E σ hσ B a a' G X om om' hKP hT c hc hcσ w τ
  have hM := hT.geo.hM
  have hle := GlobalTheory.ThKDer.polData_le (B := B) hM
  let Good : Matrix (Fin (a + a')) (Fin (a + a')) ℂ → (ℝ → GAd σ (c • G.W.J.map σ)) → Prop := fun Z γ =>
    (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) ∧
    (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z))
  let S : Set (Matrix (Fin (a + a')) (Fin (a + a')) ℂ) := {Z | ∃ γ, Good Z γ}
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  let U := Submodule.span ℝ (Set.range ((↑) : b → Matrix (Fin (a + a')) (Fin (a + a')) ℂ))
  have hSU : ∀ Z ∈ S, Z ∈ U := by
    intro Z hZ
    show Z ∈ Submodule.span ℝ (Set.range ((↑) : b → Matrix (Fin (a + a')) (Fin (a + a')) ℂ))
    rw [Subtype.range_coe, hbspan]; exact Submodule.subset_span hZ
  let bb : Module.Basis b ℝ U := Module.Basis.span hbli
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl U
  let π := Submodule.linearProjOfIsCompl U q hq
  obtain ⟨qP, hqP⟩ := Submodule.exists_isCompl (GlobalTheory.ThK.PolData B G.M)
  let P := Submodule.linearProjOfIsCompl (GlobalTheory.ThK.PolData B G.M) qP hqP
  choose γb hγb using fun i : b => hbS i.2
  let T : b → ℝ → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun i t => om (1, (toGAd hσ G.W.J hc).symm (γb i t))
  have hvacI : ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
      ∀ᶠ v : Pl F in Filter.cofinite, φ v = {x | ∀ (i : Fin a × Fin (a + a')), x i ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}.indicator 1 :=
    fun φ hvac => (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hder : ∀ i : b, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∃ Ψ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ y,
      HasDerivAt (fun t => T i t Ψ y) (Ψ₁ y) 0 := by
    intro i Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
      exact ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Δ i f) φ, Submodule.subset_span ⟨Δ i f, hΔpol _ f hf, φ, hSB, hvac, rfl⟩,
        hasDerivAt_pure (T i) (hΔ i (γb i) (hγb i).1 (hγb i).2 f hf) φ hSB (hvacI φ hvac)⟩
    | zero => exact ⟨0, zero_mem _, fun y => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨x₁, hx₁, ex⟩ := ihx
      obtain ⟨y₁, hy₁, ey⟩ := ihy
      refine ⟨x₁ + y₁, add_mem hx₁ hy₁, fun z => ?_⟩
      simp only [map_add, Pi.add_apply]
      exact (ex z).add (ey z)
    | smul r x hx ihx =>
      obtain ⟨x₁, hx₁, ex⟩ := ihx
      refine ⟨r • x₁, Submodule.smul_mem _ r hx₁, fun z => ?_⟩
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (ex z).const_mul r
  have hderv : ∀ i : b, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ y,
      HasDerivAt (fun t => T i t Ψ y) (deriv (fun t => T i t Ψ y) 0) 0 := fun i Ψ hΨ y => by
    obtain ⟨Ψ₁, -, h⟩ := hder i Ψ hΨ
    exact (h y).differentiableAt.hasDerivAt
  let dL : b → (GlobalTheory.ThK.PolData B G.M →ₗ[ℂ] ((Fin a × Fin (a + a') → AF F) → ℂ)) := fun i =>
    { toFun := fun Ψ y => deriv (fun t => T i t Ψ y) 0
      map_add' := fun Ψ₁ Ψ₂ => by
        funext y
        have e := ((hderv i _ Ψ₁.2 y).add (hderv i _ Ψ₂.2 y)).deriv
        simp only [Submodule.coe_add, map_add, Pi.add_apply]
        exact e
      map_smul' := fun r Ψ => by
        funext y
        simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact deriv_const_mul _ (hderv i _ Ψ.2 y).differentiableAt }
  have hdL_mem : ∀ i Ψ, dL i Ψ ∈ GlobalTheory.ThK.PolData B G.M := fun i Ψ => by
    obtain ⟨Ψ₁, h1, h⟩ := hder i Ψ Ψ.2
    have e : dL i Ψ = Ψ₁ := funext fun y => (h y).deriv
    rw [e]; exact h1
  have hmemP : ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.ThK.PolData B G.M := fun f hf φ hSB hvac =>
    Submodule.subset_span ⟨f, hf, φ, hSB, hvac, rfl⟩
  let Ei : b → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun i => dL i ∘ₗ P
  have hEi_mem : ∀ i Ψ, Ei i Ψ ∈ GlobalTheory.ThK.PolData B G.M := fun i Ψ => hdL_mem i _
  have hEi_pure : ∀ (i : b), ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
      Ei i (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Δ i f) φ := by
    intro i f hf φ hSB hvac
    have hP : P (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = ⟨_, hmemP f hf φ hSB hvac⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hqP ⟨_, hmemP f hf φ hSB hvac⟩
    show dL i (P _) = _
    rw [hP]
    funext y
    exact (hasDerivAt_pure (T i) (hΔ i (γb i) (hγb i).1 (hγb i).2 f hf) φ hSB (hvacI φ hvac) y).deriv
  let D₀ : U →ₗ[ℝ] Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := bb.constr ℝ Ei
  have hD₀_mem : ∀ u Ψ, D₀ u Ψ ∈ GlobalTheory.ThK.PolData B G.M := fun u Ψ => by
    rw [Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => by
      rw [LinearMap.smul_apply]; exact Submodule.smul_of_tower_mem _ _ (hEi_mem i _)
  have hD₀_pure : ∀ (x) (hx : x ∈ U), ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
      D₀ ⟨x, hx⟩ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Δ x f) φ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro f hf φ hSB hvac
      have e : (⟨(i : Matrix (Fin (a + a')) (Fin (a + a')) ℂ), Submodule.subset_span ⟨i, rfl⟩⟩ : U) = bb i :=
        (Module.Basis.span_apply hbli i).symm
      rw [e, Module.Basis.constr_basis]
      exact hEi_pure i f hf φ hSB hvac
    | zero =>
      intro f hf φ hSB hvac
      have e : (⟨0, zero_mem _⟩ : U) = 0 := rfl
      rw [e, map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, pure_zero]
    | add x y hx hy ihx ihy =>
      intro f hf φ hSB hvac
      have e : (⟨x + y, add_mem hx hy⟩ : U) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add, LinearMap.add_apply, ihx f hf φ hSB hvac, ihy f hf φ hSB hvac, map_add, LinearMap.add_apply,
        pure_add]
    | smul r x hx ihx =>
      intro f hf φ hSB hvac
      have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : U) = r • ⟨x, hx⟩ := rfl
      rw [e, map_smul, LinearMap.smul_apply, ihx f hf φ hSB hvac, map_smul, LinearMap.smul_apply, pure_rsmul]
  refine ⟨D₀ ∘ₗ π, fun Z Φ _ => hD₀_mem _ _, ?_⟩
  intro Z γ h1 h2 Φ hΦ x
  have hZS : Z ∈ S := ⟨γ, h1, h2⟩
  have hπ : π Z = ⟨Z, hSU Z hZS⟩ := Submodule.linearProjOfIsCompl_apply_left hq ⟨Z, hSU Z hZS⟩
  set DZ := D₀ ⟨Z, hSU Z hZS⟩ with hDZdef
  have hDZ : (D₀ ∘ₗ π) Z = DZ := by rw [LinearMap.comp_apply, hπ]
  have hRL : IsRealLine σ (c • G.W.J.map σ) γ :=
    ⟨w, τ, Z, lieA F E σ hT.base.cm _ _ w τ Z (fun t => projArch σ (c • G.W.J.map σ) w (γ t)) h2,
      fun t => ⟨projArch σ (c • G.W.J.map σ) w (γ t), (h1 t).symm, h2 t⟩⟩
  obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.ThKDer.lineA F E σ hσ hT.base.cm G.W c hc γ hRL
  have hk : ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ g h,
      HasDerivAt (fun s : ℝ => theta om Φ g (h * γL (Multiplicative.ofAdd s))) (theta om (DZ Φ) g h) 0 := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
      intro g h
      have hact := hΔ Z γ h1 h2 f hf
      simp only [eγ] at hact
      rw [hDZdef, hD₀_pure Z _ f hf φ hSB hvac]
      exact GlobalTheory.ThKDer.kerDer F E σ B a a' G X om om' hKP hT γL hγL f hf (Δ Z f) hact φ hSB hvac g h
    | zero =>
      intro g h
      simpa [GlobalTheory.ThKDer.theta_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    | add x y hx hy ihx ihy =>
      intro g h
      rw [map_add, GlobalTheory.ThKDer.theta_add hT (hle (hD₀_mem _ _)) (hle (hD₀_mem _ _))]
      simp only [GlobalTheory.ThKDer.theta_add hT (hle hx) (hle hy)]
      exact (ihx g h).add (ihy g h)
    | smul r x hx ihx =>
      intro g h
      rw [map_smul, GlobalTheory.ThKDer.theta_smul]
      simp only [GlobalTheory.ThKDer.theta_smul]
      exact (ihx g h).const_mul r
  have key := GlobalTheory.ThKDer.hasDerivAt_I hKP hT hγL hΦ (hD₀_mem _ Φ) (hD₀_mem _ (DZ Φ)) (hk Φ hΦ) (hk _ (hD₀_mem _ Φ))
    ((toGAd hσ G.W.J hc).symm x)
  rw [hDZ]
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show G.M.I om Φ ((toGAd hσ G.W.J hc).symm (x * γ s)) = _
  rw [map_mul, eγ]

end GlobalTheory.ThKSmoothDer
