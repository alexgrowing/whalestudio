import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitianStatement

noncomputable section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ThKFockDer

open Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.RealLift GlobalTheory.RealLift.Main
open scoped Classical

theorem exp_mul_frame {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (C : Matrix α β ℂ)
    (C' : Matrix β α ℂ) (h : C * C' = 1) (h' : C' * C = 1) (Z : Matrix α α ℂ) :
    NormedSpace.exp Z * C = C * NormedSpace.exp (C' * Z * C) := by
  let f : Matrix α α ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C' * X * C
      map_one' := by rw [Matrix.mul_one, h']
      map_mul' := fun X Y => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C C', h, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have e : C' * NormedSpace.exp Z * C = NormedSpace.exp (C' * Z * C) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.map_exp f hf Z
  rw [← e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem exp_map_conj {α : Type} [Fintype α] [DecidableEq α] (Z : Matrix α α ℂ) :
    (NormedSpace.exp Z).map (starRingEnd ℂ) = NormedSpace.exp (Z.map (starRingEnd ℂ)) := by
  have hf : Continuous ((starRingEnd ℂ).mapMatrix (m := α)) := continuous_id.matrix_map Complex.continuous_conj
  open scoped Matrix.Norms.Operator in exact NormedSpace.map_exp (starRingEnd ℂ).mapMatrix hf Z

theorem jm_mul_self (P Q : ℕ) : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem frame_inv {α : Type} [Fintype α] [DecidableEq α] {P Q : ℕ} {M : Matrix α α ℂ} {A : Matrix α (Ix P Q) ℂ}
    (h : IsFrame M A) : ∃ A' : Matrix (Ix P Q) α ℂ, A * A' = 1 ∧ A' * A = 1 := by
  obtain ⟨h1, A', h2⟩ := h
  have h3 : (Jm P Q * (M * A.map star).transpose) * A = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc, this]
    have e : (Jm P Q).transpose = Jm P Q := by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]
    rw [e, jm_mul_self]
  refine ⟨A', h2, ?_⟩
  have : A' = Jm P Q * (M * A.map star).transpose := by
    rw [← Matrix.mul_one (Jm P Q * (M * A.map star).transpose), ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [this, h3]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_transfer {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}
    (τ τ' : EmbOver E w) : ∃ κ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ, ∀ (g : GArch σ J w) Z,
      GlobalTheory.Orb.archMat σ J τ g = NormedSpace.exp Z → GlobalTheory.Orb.archMat σ J τ' g = NormedSpace.exp (κ Z) := by
  rcases infEmb_eq_or_conj h τ τ' with e | e
  · refine ⟨LinearMap.id, fun g Z hg => ?_⟩
    rw [GlobalTheory.Orb.archMat_apply, e]; exact hg
  · refine ⟨Complex.conjAe.toLinearMap.mapMatrix, fun g Z hg => ?_⟩
    rw [GlobalTheory.Orb.archMat_apply, e, RingHom.coe_comp, ← Matrix.map_map, ← GlobalTheory.Orb.archMat_apply, hg]
    exact exp_map_conj Z

theorem exists_fockDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ Δ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ (SInf F (Fin a × Fin (a + a'))),
        (∀ Z, ∀ f ∈ G.M.Pol B.ψ B.emb, Δ Z f ∈ G.M.Pol B.ψ B.emb) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ f ∈ G.M.Pol B.ψ B.emb,
            ActsD (evI F) (fun t => om (1, (toGAd hσ G.W.J hc).symm (γ t))) f (Δ Z f) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ w τ
  obtain ⟨hb, hg, hch, hw, -⟩ := hT
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hKP.base i_derex hfe hvl (i_liescalar hKP.base i_derex hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange actsLaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hch.expβ
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ.1)
  obtain ⟨C', hCC', hC'C⟩ := frame_inv (hC w)
  obtain ⟨κ, hκ⟩ := exists_transfer hb.cm (c • G.W.J.map σ) τ (B.emb w)
  let D : Mat _ _ →ₗ[ℂ] Module.End ℂ (SInf F (Fin a × Fin (a + a'))) :=
    { toFun := fun Y => Φ ∘ₗ atPl w (fockAct2 _ _ _ _ Y + ((B.mβ w : ℂ) / 2 * Y.trace) • 1) ∘ₗ Ψ
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
  obtain ⟨T, rfl⟩ := pol_eq B G.M Φ hr hf
  have hsd := hW2 γL hγL Yg hgen T
  have hact := (actsLaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd
  have hsum : sumPl (fun w' => fockAct2 _ _ _ _ (Yg w') + ((B.mβ w' : ℂ) / 2 * (Yg w').trace) • 1) =
      atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p _ _) w
        (fockAct2 _ _ _ _ (L (κ Z)) + ((B.mβ w : ℂ) / 2 * (L (κ Z)).trace) • 1) := by
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

end GlobalTheory.ThKFockDer
