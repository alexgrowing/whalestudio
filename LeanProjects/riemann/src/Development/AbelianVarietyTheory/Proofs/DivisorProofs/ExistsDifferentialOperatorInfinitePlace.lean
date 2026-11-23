import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLaplacianPolData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftAlongRealLineBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement

noncomputable section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ThKSmoothDerSmall

open Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.RealLift GlobalTheory.RealLift.Main GlobalTheory.ThKFockDer
open scoped Classical

theorem exists_fockDer_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ Δ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ (SInf F (Fin a' × Fin (a + a'))),
        (∀ Z, ∀ f ∈ G.M'.Pol B.ψ B.emb, Δ Z f ∈ G.M'.Pol B.ψ B.emb) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ f ∈ G.M'.Pol B.ψ B.emb,
            ActsD (evI F) (fun t => om' (1, (toGAd hσ G.W.J hc).symm (γ t))) f (Δ Z f) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ w τ
  obtain ⟨hb, hg, hch, -, hw⟩ := hT
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)
  choose C hC hCθ using fun w => frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hKP.base i_derex hfe hvl (i_liescalar hKP.base i_derex hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange actsLaws i_derex hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A C Φ _ X.α B.mα hb.cm hb.std fr hΦ hwp.1 hch.expα
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ.1)
  obtain ⟨C', hCC', hC'C⟩ := frame_inv (hC w)
  obtain ⟨κ, hκ⟩ := exists_transfer hb.cm (c • G.W.J.map σ) τ (B.emb w)
  let D : Mat _ _ →ₗ[ℂ] Module.End ℂ (SInf F (Fin a' × Fin (a + a'))) :=
    { toFun := fun Y => Φ ∘ₗ atPl w (fockAct2 _ _ _ _ Y + ((B.mα w : ℂ) / 2 * Y.trace) • 1) ∘ₗ Ψ
      map_add' := fun Y Y' => by
        rw [← LinearMap.comp_add, ← LinearMap.add_comp, ← atPl_add, map_add, Matrix.trace_add, mul_add, add_smul]
        congr 3
        abel
      map_smul' := fun r Y => by
        rw [RingHom.id_apply, ← LinearMap.comp_smul, ← LinearMap.smul_comp, ← atPl_smul, map_smul, Matrix.trace_smul,
          smul_add, smul_smul, smul_eq_mul, mul_left_comm] }
  let L : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Mat _ _ :=
    { toFun := fun Z => C' * Z * C w
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r X => by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  refine ⟨D.restrictScalars ℝ ∘ₗ L ∘ₗ κ, fun Z f _ => ?_, fun Z γ h1 h2 f hf => ?_⟩
  · rw [← hr]
    exact LinearMap.mem_range_self Φ _
  have hRL : IsRealLine σ (c • G.W.J.map σ) γ :=
    ⟨w, τ, Z, GlobalTheory.T.one_parameter_skew_hermitian F E σ hb.cm _ _ w τ Z (fun t => projArch σ (c • G.W.J.map σ) w (γ t)) h2,
      fun t => ⟨projArch σ (c • G.W.J.map σ) w (γ t), (h1 t).symm, h2 t⟩⟩
  obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.T.real_line_corresponds_to_line F E σ hσ hb.cm G.W c hc γ hRL
  let Yg : InfinitePlace F → Mat _ _ := Function.update (fun _ => 0) w (L (κ Z))
  have hgen : IsGen B.emb C γL Yg := by
    intro t u
    have e0 : ((γL (Multiplicative.ofAdd t)).1 : Matrix _ _ (AE F E)).map (piInf (B.emb u)) =
        GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) (B.emb u) (projArch σ (c • G.W.J.map σ) u (γ t)) := by
      rw [← eγ]; rfl
    rw [e0]
    by_cases hu : u = w
    · subst hu
      rw [hκ _ _ (h2 t), exp_mul_frame _ _ hCC' hC'C, map_smul]
      simp only [Yg, Function.update_self]
      rw [← L.map_smul]
      rfl
    · rw [← h1 t, projArch_embArch_ne _ _ hu, map_one]
      simp [Yg, Function.update_of_ne hu]
  obtain ⟨T, rfl⟩ := pol_eq B G.M' Φ hr hf
  have hsd := hW2 γL hγL Yg hgen T
  have hact := (actsLaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd
  have hsum : sumPl (fun w' => fockAct2 _ _ _ _ (Yg w') + ((B.mα w' : ℂ) / 2 * (Yg w').trace) • 1) =
      atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol G.q (a' - G.q) _ _) w (fockAct2 _ _ _ _ (L (κ Z)) + ((B.mα w : ℂ) / 2 * (L (κ Z)).trace) • 1) := by
    unfold sumPl
    rw [Finset.sum_eq_single w]
    · simp only [Yg, Function.update_self]
    · intro w' _ h
      simp [Yg, Function.update_of_ne h, atPl_zero]
    · simp
  rw [hsum] at hact
  simp only [eγ]
  have hΨT : Ψ (Φ T) = T := LinearMap.congr_fun hΨ T
  change ActsD _ _ _ (Φ (atPl w _ (Ψ (Φ T))))
  rw [hΨT]
  exact hact

theorem hasDerivAt_thetaIntegral_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ D : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
        (∀ Z, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, D Z Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ x, HasDerivAt (fun s : ℝ => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm (x * γ s)))
            (G.M'.I om' (D Z Φ) ((toGAd hσ G.W.J hc).symm x)) 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcσ w τ
  classical
  obtain ⟨Δ, hΔpol, hΔ⟩ := exists_fockDer_small F E σ hσ B a a' G X om om' hKP hT c hc hcσ w τ
  have hM := hT.geo.hM'
  let Good : Matrix (Fin (a + a')) (Fin (a + a')) ℂ → (ℝ → GAd σ (c • G.W.J.map σ)) → Prop := fun Z γ =>
    (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) ∧
    (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z))
  have hRLof : ∀ Z γ, Good Z γ → IsRealLine σ (c • G.W.J.map σ) γ := fun Z γ h =>
    ⟨w, τ, Z, GlobalTheory.T.one_parameter_skew_hermitian F E σ hT.base.cm _ _ w τ Z (fun t => projArch σ (c • G.W.J.map σ) w (γ t)) h.2,
      fun t => ⟨projArch σ (c • G.W.J.map σ) w (γ t), (h.1 t).symm, h.2 t⟩⟩
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
  obtain ⟨qP, hqP⟩ := Submodule.exists_isCompl (GlobalTheory.ThK.PolData B G.M')
  let P := Submodule.linearProjOfIsCompl (GlobalTheory.ThK.PolData B G.M') qP hqP
  choose γb hγb using fun i : b => hbS i.2
  let T : b → ℝ → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun i t => om' (1, (toGAd hσ G.W.J hc).symm (γb i t))
  have hvacI : ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
      ∀ᶠ v : Pl F in Filter.cofinite, φ v = {x | ∀ (i : Fin a' × Fin (a + a')), x i ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}.indicator 1 :=
    fun φ hvac => (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hder : ∀ i : b, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∃ Ψ₁ ∈ GlobalTheory.ThK.PolData B G.M', ∀ y,
      HasDerivAt (fun t => T i t Ψ y) (Ψ₁ y) 0 := by
    intro i Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
      exact ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Δ i f) φ, Submodule.subset_span ⟨Δ i f, hΔpol _ f hf, φ, hSB, hvac, rfl⟩,
        GlobalTheory.ThKSmoothDer.hasDerivAt_pure (T i) (hΔ i (γb i) (hγb i).1 (hγb i).2 f hf) φ hSB (hvacI φ hvac)⟩
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
  have hderv : ∀ i : b, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∀ y,
      HasDerivAt (fun t => T i t Ψ y) (deriv (fun t => T i t Ψ y) 0) 0 := fun i Ψ hΨ y => by
    obtain ⟨Ψ₁, -, h⟩ := hder i Ψ hΨ
    exact (h y).differentiableAt.hasDerivAt
  let dL : b → (GlobalTheory.ThK.PolData B G.M' →ₗ[ℂ] ((Fin a' × Fin (a + a') → AF F) → ℂ)) := fun i =>
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
  have hdL_mem : ∀ i Ψ, dL i Ψ ∈ GlobalTheory.ThK.PolData B G.M' := fun i Ψ => by
    obtain ⟨Ψ₁, h1, h⟩ := hder i Ψ Ψ.2
    have e : dL i Ψ = Ψ₁ := funext fun y => (h y).deriv
    rw [e]; exact h1
  have hmemP : ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.ThK.PolData B G.M' := fun f hf φ hSB hvac =>
    Submodule.subset_span ⟨f, hf, φ, hSB, hvac, rfl⟩
  let Ei : b → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun i => dL i ∘ₗ P
  have hEi_mem : ∀ i Ψ, Ei i Ψ ∈ GlobalTheory.ThK.PolData B G.M' := fun i Ψ => hdL_mem i _
  have hEi_pure : ∀ (i : b), ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
      Ei i (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Δ i f) φ := by
    intro i f hf φ hSB hvac
    have hP : P (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = ⟨_, hmemP f hf φ hSB hvac⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hqP ⟨_, hmemP f hf φ hSB hvac⟩
    show dL i (P _) = _
    rw [hP]
    funext y
    exact (GlobalTheory.ThKSmoothDer.hasDerivAt_pure (T i) (hΔ i (γb i) (hγb i).1 (hγb i).2 f hf) φ hSB (hvacI φ hvac) y).deriv
  have hEi_so : ∀ i : b, ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), Ei i Ψ ∈ G.M'.So B.ψ B.τ₁ := by
    intro i Ψ hΨ
    obtain ⟨hP, hS⟩ := Submodule.mem_inf.1 hΨ
    obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.ThKDerSmall.lineA F E σ hσ hT.base.cm G.W c hc (γb i) (hRLof _ _ (hγb i))
    obtain ⟨Ψ₁, h1, d⟩ := GlobalTheory.ThKDerSmall.exists_der_so hKP hT hγL Ψ hS
    have hPΨ : P Ψ = ⟨Ψ, hP⟩ := Submodule.linearProjOfIsCompl_apply_left hqP ⟨Ψ, hP⟩
    have e : Ei i Ψ = Ψ₁ := by
      show dL i (P Ψ) = Ψ₁
      rw [hPΨ]
      funext y
      show deriv (fun t => T i t Ψ y) 0 = Ψ₁ y
      have e2 : (fun t => T i t Ψ y) = fun t => om' (1, γL (Multiplicative.ofAdd t)) Ψ y :=
        funext fun t => by simp only [T, eγ]
      rw [e2]
      exact (d y).deriv
    rw [e]; exact h1
  let D₀ : U →ₗ[ℝ] Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := bb.constr ℝ Ei
  have hD₀_Q : ∀ u, ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), D₀ u Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := fun u Ψ hΨ => by
    rw [Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => by
      rw [LinearMap.smul_apply]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_inf.2 ⟨hEi_mem i _, hEi_so i Ψ hΨ⟩)
  have hD₀_pure : ∀ (x) (hx : x ∈ U), ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
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
      rw [e, map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, GlobalTheory.ThKSmoothDer.pure_zero]
    | add x y hx hy ihx ihy =>
      intro f hf φ hSB hvac
      have e : (⟨x + y, add_mem hx hy⟩ : U) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add, LinearMap.add_apply, ihx f hf φ hSB hvac, ihy f hf φ hSB hvac, map_add, LinearMap.add_apply,
        GlobalTheory.ThKSmoothDer.pure_add]
    | smul r x hx ihx =>
      intro f hf φ hSB hvac
      have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : U) = r • ⟨x, hx⟩ := rfl
      rw [e, map_smul, LinearMap.smul_apply, ihx f hf φ hSB hvac, map_smul, LinearMap.smul_apply,
        GlobalTheory.ThKSmoothDer.pure_rsmul]
  refine ⟨D₀ ∘ₗ π, fun Z Φ hΦ => hD₀_Q _ _ hΦ, ?_⟩
  intro Z γ h1 h2 Φ hΦ x
  have hZS : Z ∈ S := ⟨γ, h1, h2⟩
  have hπ : π Z = ⟨Z, hSU Z hZS⟩ := Submodule.linearProjOfIsCompl_apply_left hq ⟨Z, hSU Z hZS⟩
  set DZ := D₀ ⟨Z, hSU Z hZS⟩ with hDZdef
  have hDZ : (D₀ ∘ₗ π) Z = DZ := by rw [LinearMap.comp_apply, hπ]
  obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.ThKDerSmall.lineA F E σ hσ hT.base.cm G.W c hc γ (hRLof Z γ ⟨h1, h2⟩)
  have hpt : ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∀ y,
      HasDerivAt (fun t : ℝ => om' (1, γL (Multiplicative.ofAdd t)) Ψ y) (DZ Ψ y) 0 := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
      intro y
      have hact := hΔ Z γ h1 h2 f hf
      simp only [eγ] at hact
      rw [hDZdef, hD₀_pure Z _ f hf φ hSB hvac]
      exact GlobalTheory.ThKSmoothDer.hasDerivAt_pure (fun t => om' (1, γL (Multiplicative.ofAdd t))) hact φ hSB (hvacI φ hvac) y
    | zero =>
      intro y
      simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    | add x y hx hy ihx ihy =>
      intro z
      simp only [map_add, Pi.add_apply]
      exact (ihx z).add (ihy z)
    | smul r x hx ihx =>
      intro z
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (ihx z).const_mul r
  have hDQ : ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), DZ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := fun Ψ hΨ => hD₀_Q _ _ hΨ
  have hk : ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ g h,
      HasDerivAt (fun s : ℝ => theta om' Ψ g (h * γL (Multiplicative.ofAdd s))) (theta om' (DZ Ψ) g h) 0 := by
    intro Ψ hΨ
    obtain ⟨Ψ₁, -, p1, d1⟩ := GlobalTheory.ThKDerSmall.exists_der_pol hKP hT hγL Ψ (Submodule.mem_inf.1 hΨ).1
    have e : Ψ₁ = DZ Ψ := funext fun y => (p1 y).unique (hpt Ψ (Submodule.mem_inf.1 hΨ).1 y)
    rw [← e]; exact d1
  have key := GlobalTheory.ThKDerSmall.hasDerivAt_I hKP hT hγL (Submodule.mem_inf.1 hΦ).2 (Submodule.mem_inf.1 (hDQ Φ hΦ)).2
    (Submodule.mem_inf.1 (hDQ _ (hDQ Φ hΦ))).2 (hk Φ hΦ) (hk _ (hDQ Φ hΦ)) ((toGAd hσ G.W.J hc).symm x)
  rw [hDZ]
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm (x * γ s)) = _
  rw [map_mul, eγ]

end GlobalTheory.ThKSmoothDerSmall
