import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperator

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblKInfFin

open GlobalTheory.ThK.EvAt0.PolD Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.KInfPol

def sigEquiv (r s : ℕ) : Ix r s ⊕ Ix r s ≃ Ix (r + s) (s + r) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans <|
    (Equiv.sumSumSumComm _ _ _ _).trans <|
      Equiv.sumCongr finSumFinEquiv finSumFinEquiv

theorem Jm_dbl (r s : ℕ) :
    Jm (r + s) (s + r) = (Matrix.fromBlocks (Jm r s) 0 0 (-Jm r s)).submatrix (sigEquiv r s).symm (sigEquiv r s).symm := by
  have : (Jm (r + s) (s + r)).submatrix (sigEquiv r s) (sigEquiv r s) = Matrix.fromBlocks (Jm r s) 0 0 (-Jm r s) := by
    ext i j
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
      simp [sigEquiv, Jm, Formalism.UG.Jpq, Matrix.one_apply, Fin.ext_iff] <;> omega
  rw [← this]
  simp

theorem frame_dbl {d r s : ℕ} (M θ : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d) (Ix r s) ℂ) (hC : IsFrame M C)
    (hθ : θ * C = C * Jm r s) :
    ∃ C₂ : Matrix (Fin (d + d)) (Ix (r + s) (s + r)) ℂ, IsFrame (blkMat finSumFinEquiv M (-M)) C₂ ∧
      blkMat finSumFinEquiv θ (-θ) * C₂ = C₂ * Jm (r + s) (s + r) := by
  obtain ⟨h1, C', h2⟩ := hC
  refine ⟨(Matrix.fromBlocks C 0 0 C).submatrix finSumFinEquiv.symm (sigEquiv r s).symm, ⟨?_,
    (Matrix.fromBlocks C' 0 0 C').submatrix (sigEquiv r s).symm finSumFinEquiv.symm, ?_⟩, ?_⟩
  · rw [Jm_dbl, blkMat, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    have h3 : Cᵀ * M * C.map (starRingEnd ℂ) = Jm r s := h1
    simp [Matrix.map_zero, h3]
  · rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [h2]
  · rw [Jm_dbl, blkMat, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hθ]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem vacSp_fin (B : Base F E) (hb : B.IsGood σ) (M : Model σ X W) {r s r' s' : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix r s) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r' s') ℂ)
    (hA : ∀ w, IsFrame (X.J.map (B.emb w).1) (A w)) (hAθ : ∀ w, X.θ w * A w = A w * Jm r s)
    (hC : ∀ w, IsFrame (Complex.I • W.J.map (B.emb w).1) (C w)) (hCθ : ∀ w, W.θ w * C w = C w * Jm r' s') :
    FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.FockKFin.VacFin.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.FockKFin.VacFin.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I
    A C hb.cm hb.std fr
  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hb.std
  have hDd : ∀ u, At (evI F) u → ∀ f : SInf F (Fin n × Fin d), D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    intro u hu f
    refine DFunLike.ext _ _ fun x => ?_
    rw [(hD u hu f).2 x, dOp_apply]
    try rfl
  have tw : ∀ w (c : Matrix (Ix r s) (Ix r' s') ℂ) (e : ℂ),
      A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm r' s' * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, GlobalTheory.FockKFin.VacFin.Jm_transpose]
    calc A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • ((A w * Jm r s) * c * (Jm r' s' * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hAθ w, ← h2]; simp only [Matrix.mul_assoc]
  have hle : GlobalTheory.FockKFin.vacSp M B.emb ≤ Submodule.span ℂ {Φ (PiTensorProduct.tprod ℂ fun _ => 1)} := by
    refine Submodule.span_le.2 fun g ⟨ε, hε⟩ => ?_
    have : ∃ z : ℂ, g = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
      refine GlobalTheory.VacLn.vacLine_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ
        hb.cm hb.std fr hΦ g ε ?_
      intro u u' hu hu' c hc hc' f f' hf hf'
      have e1 : f = D u g := (actsLaws F _ g f (D u g)).2.2.2.2 _ hf (hD u hu g).1
      have e2 : f' = D u' g := (actsLaws F _ g f' (D u' g)).2.2.2.2 _ hf' (hD u' hu' g).1
      rw [e1, e2, hDd u hu, hDd u' hu']
      exact hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w])
    obtain ⟨z, rfl⟩ := this
    exact Submodule.smul_mem _ z (Submodule.subset_span rfl)
  exact Submodule.finiteDimensional_of_le hle

theorem actsD_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil ψ χX χW om) (k : UA σ W.J) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (h : ActsD (evI F) (M.heisLine ψ u) f f₁) :
    ActsD (evI F) (M.heisLine ψ (u * (mat k)ᵀ)) (A f) (A f₁) := by
  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : SD (M.heisLine ψ u) f (D u f) := (hD u hu f).1
  have e : f₁ = D u f := (hL _ _ _).2.2.1 _ h ((hL f _ f).1 _ (heisLine_zero M ψ u) hSD)
  rw [e]
  exact (hL _ _ f).1 _ (heisLine_zero M ψ _) (sd_intertwine hw k (hA f) (hA _) hSD)

theorem op_dOp {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil ψ χX χW om) (k : UA σ W.J) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f))
    (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∀ f, A (dOp a b f) = dOp a' b' (A f) := by
  have hu := GlobalTheory.ThK.EvAt0.PolEv.at_symm M a b
  refine ⟨_, _, fun f => (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hψ M _ (GlobalTheory.KInfPol.at_mul_right hu (mat k)ᵀ) _ _).1
    (actsD_mul hψ hw k A hA _ hu f _ ?_)⟩
  refine (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hψ M _ hu _ _).2 ?_
  rw [LinearEquiv.apply_symm_apply, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA]

theorem op_gauss {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil ψ χX χW om) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : UA σ W.J) (hk : k ∈ KInf σ W τ)
    (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) (f₀ : SInf F (Fin n × Fin d))
    (hf₀ : GaussD M τ f₀) : GaussD M τ (A f₀) := by
  rw [← GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hψ] at hf₀ ⊢
  have hL := actsLaws F (Fin n × Fin d)
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
  have hv := GlobalTheory.KInfPol.at_mul_right hu (mat k⁻¹)ᵀ
  have hv' := GlobalTheory.KInfPol.at_mul_right hu' (mat k⁻¹)ᵀ
  have d1 := (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hψ M _ hv f₀ _).2 rfl
  have d2 := (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hψ M _ hv' f₀ _).2 rfl
  have h1 := actsD_mul hψ hw k A hA _ hv f₀ _ d1
  have h2 := actsD_mul hψ hw k A hA _ hv' f₀ _ d2
  rw [hcan] at h1 h2
  have e1 := (hL _ _ _).2.2.1 _ hg h1
  have e2 := (hL _ _ _).2.2.1 _ hg' h2
  have key := hε _ _ hv hv' (fun w => ?_) _ _ d1 d2
  · rw [e1, e2, key, map_smul]
  · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul]
      change (mat (k⁻¹ * k)).map _ = 1
      rw [inv_mul_cancel]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
    have hc : (mat k⁻¹).map (piInf (τ w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (τ w)) := by
      calc _ = (mat k⁻¹).map (piInf (τ w)) * W.θ w *
            ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
        _ = (mat k⁻¹).map (piInf (τ w)) * (W.θ w * (mat k).map (piInf (τ w))) *
            (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]

theorem pol_kfin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil ψ χX χW om) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (h0 : FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M τ)) (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ τ)
    (g : (Fin n × Fin d → Af F) → ℂ) (hg : g ∈ SB (Fin n × Fin d → Af F)) :
    FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W τ, Ψ = om (1, a) (pureA F f g)}) := by
  have hfin : ∀ m, FiniteDimensional ℂ (GlobalTheory.FockKFin.polLe M τ m) := by
    intro m
    induction m with
    | zero => exact h0
    | succ m ih =>
      rw [GlobalTheory.FockKFin.polLe_succ]
      haveI := ih
      haveI := GlobalTheory.FockKFinStep.dStep_finiteDimensional F _ _ ih
      infer_instance
  have hdir : Directed (· ≤ ·) (GlobalTheory.FockKFin.polLe M τ) := (GlobalTheory.FockKFin.polLe_mono M τ).directed_le
  have hsub : M.Pol ψ τ ≤ ⨆ m, GlobalTheory.FockKFin.polLe M τ m := by
    rw [GlobalTheory.ThK.EvAt0.PolEv.pol_eq hψ]
    refine sInf_le ⟨fun g hg => Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hg), fun a b g hg => ?_⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hg
    refine Submodule.mem_iSup_of_mem (m + 1) ?_
    rw [GlobalTheory.FockKFin.polLe_succ]
    exact Submodule.mem_sup_right (GlobalTheory.FockKFin.dOp_mem_dStep _ a b hm)
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 (hsub hf)
  have hst : ∀ k ∈ KInf σ W τ, ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
      ∀ m, GlobalTheory.FockKFin.polLe M τ m ≤ (GlobalTheory.FockKFin.polLe M τ m).comap A := by
    intro k hk A hA m
    induction m with
    | zero =>
      rw [GlobalTheory.FockKFin.polLe_zero]
      exact Submodule.span_le.2 fun g hg => Submodule.subset_span (op_gauss hψ hw τ k hk A hA g hg)
    | succ m ih =>
      rw [GlobalTheory.FockKFin.polLe_succ]
      refine sup_le (fun y hy => Submodule.mem_sup_left (ih hy)) (Submodule.span_le.2 ?_)
      rintro _ ⟨a, b, g₀, hg₀, rfl⟩
      obtain ⟨a', b', hab⟩ := op_dOp hψ hw k A hA a b
      refine Submodule.mem_comap.2 (Submodule.mem_sup_right ?_)
      rw [hab]
      exact GlobalTheory.FockKFin.dOp_mem_dStep _ a' b' (ih hg₀)
  let L : SInf F (Fin n × Fin d) →ₗ[ℂ] (Fin n × Fin d → AF F) → ℂ :=
    { toFun := fun φ => pureA F φ g
      map_add' := fun φ φ' => by funext x; simp [pureA, add_mul]
      map_smul' := fun c φ => by funext x; simp [pureA, mul_assoc] }
  haveI := hfin m
  refine Submodule.finiteDimensional_of_le (S₂ := (GlobalTheory.FockKFin.polLe M τ m).map L) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, hk, rfl⟩
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hψ hw (1, k) h1 hk.1
  exact ⟨A f, hst k hk A hA m hm, (sa_of_acts (hA f) g hg).symm⟩

theorem dbl_kInf_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ f ∈ Model.Pol ({ co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ } : Model σ Xs W₂) B.ψ B.emb,
    ∀ g ∈ SB (Fin n × Fin (d + d) → Af F),
      FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ a ∈ KInf σ W₂ B.emb, Ψ = om₂ (1, a) (pureA F f g)}) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ _ hθ co _ _ _ om₂ hw f hf g hg
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hP.herm.sig w) (hP.herm.cartan w)
  choose C hC hCθ using fun w => frameEx_holds _ _ _ _ _ (hP.skew.sig w) (hP.skew.cartan w)
  choose C₂ hC₂ hC₂θ using fun w => frame_dbl _ _ _ (hC w) (hCθ w)
  refine pol_kfin (M := { co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ }) hP.base.std hw B.emb
    (vacSp_fin B hP.base _ A C₂ hA hAθ (fun w => ?_) (fun w => ?_)) f hf g hg
  · have e : Complex.I • W₂.J.map (B.emb w).1 =
        blkMat finSumFinEquiv (Complex.I • W.J.map (B.emb w).1) (-(Complex.I • W.J.map (B.emb w).1)) := by
      rw [hJ]
      ext i j
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [dblGram, blkMat, Matrix.smul_apply, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;> simp
    rw [e]; exact hC₂ w
  · rw [hθ]; exact hC₂θ w

end GlobalTheory.DblKInfFin

end
