import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxCoordinatesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSchwartzAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedVec

open GlobalTheory.SympChange GlobalTheory.SympChangeBij GlobalTheory.DblEval GlobalTheory.ThK.Adapt GlobalTheory.ThK.PlaneEv

section Dbl

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_dbl (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (hG : IsSymp G) :
    ∃ Gd : Matrix ((κ ⊕ κ) ⊕ (κ ⊕ κ)) ((κ ⊕ κ) ⊕ (κ ⊕ κ)) F, IsSymp Gd ∧
      ∀ {R : Type} [CommRing R] [Algebra F R] (w₁ w₂ : (κ → R) × (κ → R)),
        spAct Gd (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 (-w₂.2)) =
          (Sum.elim (spAct G w₁).1 (spAct G w₂).1, Sum.elim (spAct G w₁).2 (-(spAct G w₂).2)) := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, G = Matrix.fromBlocks A B C D := ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks G).symm⟩
  refine ⟨Matrix.fromBlocks (Matrix.fromBlocks A 0 0 A) (Matrix.fromBlocks B 0 0 (-B)) (Matrix.fromBlocks C 0 0 (-C))
    (Matrix.fromBlocks D 0 0 D), ?_, fun w₁ w₂ => ?_⟩
  · simp only [IsSymp, weylM, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj,
      Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at hG
    obtain ⟨h1, h2, h3, h4⟩ := hG
    simp only [IsSymp, weylM, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj,
      Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.zero_mul, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, neg_zero, neg_neg]
    rw [← Matrix.fromBlocks_zero, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp only [Matrix.fromBlocks_inj, neg_zero, h1, h2, h3, h4, true_and, and_true]
    refine ⟨?_, ?_⟩
    · rw [← neg_eq_zero, ← h1]; abel
    · rw [← neg_eq_zero, ← h4]; abel
  · ext (k | k) <;>
      simp [spAct, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, add_comm]

end Dbl

section admitted

variable {F : Type} [Field F] [NumberField F] {κ κ₀ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem admissible_of_local_operator (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) (he : IsLocOp e) :
    ∀ l ∈ (adeleClass F).adm κ₁, l ∘ₗ e ∈ (adeleClass F).adm κ := by
  classical
  intro l hl g hg
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hψSB : ∀ k v, ev v (φ k v) ∈ GlobalTheory.WeilM.SB (κ₁ → Fv F v) := fun k v => hSB v _ (hφSB k v)
  have hψstd : ∀ k, ∀ᶠ v in cofinite, ev v (φ k v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun k =>
    ((hφstd k).and hstd).mono fun v h => by rw [h.1]; exact h.2
  have hg' : ∀ k, (fun y : κ₁ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := fun k =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB k) (hψstd k),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB k) (hψstd k)⟩
  choose T hT using fun k => hl _ (hg' k)
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  have h1 : pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)) = pureA F (ei f : (κ₁ → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) := fun k =>
    hloc f (φ k) (hφSB k) (hφstd k)
  simp only [LinearMap.comp_apply, h1, map_sum, map_smul, h2, hT, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]

theorem admissible_of_slice_zero (ε : κ ≃ κ₀ ⊕ κ₁) : ∀ l ∈ (adeleClass F).adm κ₁,
    l ∘ₗ LinearMap.funLeft ℂ ℂ (fun b : κ₁ → AF F => glue ε 0 b) ∈ (adeleClass F).adm κ := by
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  intro l hl g hg
  obtain ⟨T, hT⟩ := exists_slice ε fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ₀ → AF F) k).1
  obtain ⟨S, hS⟩ := hl _ (slice_mem_SB ε (fun k => ((0 : κ₀ → AF F) k).2) hg)
  refine ⟨S.comp T, fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hS, LinearMap.comp_apply]
  congr 1
  funext b
  simp only [LinearMap.funLeft_apply, pureA, hT]
  rw [glue_map ε (fun z : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1), glue_map ε (fun z : AF F => z.2)]

open scoped Classical in

theorem reindex_mem {κ' : Type} [Fintype κ'] (τ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ τ)) ∈ schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) τ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) τ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem hasOpB_of_isSymp [DecidableEq κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (hG : IsSymp G) : HasOpB ψ G := by
  obtain ⟨hunr, hnt⟩ := GlobalTheory.PsiStdCond.psi_std_conductor F ψ hψ
  refine hasOpB_of_mem_closure ?_ G (GlobalTheory.SympChangeGen.mem_closure_gens F _ G hG)
  rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
  · exact hasOpB_levi F ψ hψ hunr hnt _ A hA
  · exact hasOpB_unipM F ψ hψ hunr hnt _ S hS
  · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weyl_element_operator_bijective F ψ hψ hunr hnt _

end admitted

section Weight

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_weight {n : ℕ} {κ : Type} [Fintype κ] (p : (Fin n → AE F E) ≃ₗ[AF F] (κ → AF F))
    (μ : @Measure (Fin n → AE F E) (borel _)) (hμ : GlobalTheory.SiegelAvg.IsHaarB μ) :
    ∃ g₀ ∈ schA F κ, letI : MeasurableSpace (Fin n → AE F E) := borel _;
      Integrable (fun y => g₀ (p y) * starRingEnd ℂ (g₀ (p y))) μ ∧ ∫ y, g₀ (p y) * starRingEnd ℂ (g₀ (p y)) ∂μ ≠ 0 := by
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
  haveI : μ.IsAddHaarMeasure := hμ
  let P : (Fin n → AE F E) ≃ₜ+ (κ → AF F) :=
    { p.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap p.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap p.symm.toLinearMap }
  have hν : (μ.map P).IsAddHaarMeasure := P.isAddHaarMeasure_map μ
  obtain ⟨g₀, hg₀, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
  have hne : ∃ x, g₀ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hθ (by simp [thetaSum, h])
  obtain ⟨x, hx⟩ := hne
  have h2 : Integrable (fun x => ‖g₀ x‖ ^ 2) (μ.map P) :=
    (GlobalTheory.WeilM.schA_memLp_two F κ _ hν g₀ hg₀).integrable_norm_pow two_ne_zero
  have h3 : Integrable (fun y => ‖g₀ (p y)‖ ^ 2) μ :=
    (integrable_map_equiv P.toHomeomorph.toMeasurableEquiv _).1 h2
  have hc : Continuous fun y => ‖g₀ (p y)‖ ^ 2 :=
    (((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hg₀).comp P.continuous).norm.pow 2)
  have e : (fun y => g₀ (p y) * starRingEnd ℂ (g₀ (p y))) = fun y => ((‖g₀ (p y)‖ ^ 2 : ℝ) : ℂ) := funext fun y => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · rw [e]; exact h3.ofReal
  · rw [e, integral_complex_ofReal, Complex.ofReal_ne_zero]
    refine (integral_pos_of_integrable_nonneg_nonzero (x := p.symm x) hc h3 (fun y => by positivity) ?_).ne'
    simpa using hx

end Weight

section Plane

variable {n d d₁ : ℕ}

def eps (hd : d = d₁ + 2) : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃
    ((Fin n × Fin 2) ⊕ (Fin n × Fin 2)) ⊕ ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)) :=
  ((idx hd).sumCongr (idx hd)).trans ((Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumComm _ _))

theorem elim_eq_glue {R : Type} (hd : d = d₁ + 2) (u₁ u₂ : Fin n × Fin d → R) (a₁ a₂ : Fin n × Fin 2 → R)
    (b₁ b₂ : Fin n × Fin d₁ → R) (h₁ : ∀ k, u₁ ((idx hd).symm (.inr k)) = a₁ k)
    (h₂ : ∀ k, u₂ ((idx hd).symm (.inr k)) = a₂ k) (h₃ : ∀ k, u₁ ((idx hd).symm (.inl k)) = b₁ k)
    (h₄ : ∀ k, u₂ ((idx hd).symm (.inl k)) = b₂ k) :
    Sum.elim u₁ u₂ = glue (eps hd) (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) := by
  funext k
  rcases k with k | k <;> obtain ⟨k, rfl⟩ := (idx hd).symm.surjective k <;> rcases k with k | k
  all_goals simp [glue, eps, h₁, h₂, h₃, h₄]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_plane_equiv {B : Base F E} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hL : W.L.IsLattice E) (hd : d = d₁ + 2)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (hlow : ∀ (z : Matrix (Fin n) (Fin d₁) (AE F E)) k, (co.e (z * (incM F H'.ι)ᵀ)).1 ((idx hd).symm (.inr k)) = 0)
    (hx : ∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0)
    (hy : ∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
      ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) :
    ∃ p : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin 2 → AF F),
      ∀ b k, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (.inr k)) = p b k := by
  obtain ⟨Q, h1, h2, -⟩ := exists_frame_inv hH hL
  have hone : ∀ {α : Type} [Fintype α] [DecidableEq α], incM F (1 : Matrix α α E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let p : (Fin n → AE F E) →ₗ[AF F] (Fin n × Fin 2 → AF F) :=
    { toFun := fun b k => (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (.inr k))
      map_add' := fun b b' => by funext k; simp [Matrix.add_vecMulVec]
      map_smul' := fun c b => by funext k; simp [Matrix.smul_vecMulVec] }
  refine ⟨LinearEquiv.ofBijective p ⟨(injective_iff_map_eq_zero p).2 fun b hb => ?_, fun t => ?_⟩, fun _ _ => rfl⟩
  · have h0 : co.e (Matrix.vecMulVec b (incV F H'.y)) = 0 := by
      refine Prod.ext (funext fun k => ?_) (hy b).1
      obtain ⟨k, rfl⟩ := (idx hd).symm.surjective k
      rcases k with k | k
      · exact (hy b).2 k
      · exact congrFun hb k
    rw [map_eq_zero_iff _ co.e.injective] at h0
    have h3 : (incM F Q *ᵥ incV F H'.y) (.inr 1) = 1 := by
      have := congrFun (congrFun (congrArg (incM F) h2) (.inr 1)) (.inr 1)
      rw [incM_mul, hone, Matrix.one_apply_eq] at this
      exact this
    funext i
    have h4 : (Matrix.vecMulVec b (incV F H'.y) * (incM F Q)ᵀ) i (.inr 1) = 0 := by rw [h0, Matrix.zero_mul]; rfl
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.vecMulVec_apply, h3, mul_one] at h4
    exact h4
  · let u := co.e.symm (fun k => Sum.elim 0 t (idx hd k), 0)
    let Y := u * (incM F Q)ᵀ
    have hu : u = Y.submatrix id .inl * (incM F H'.ι)ᵀ + Matrix.vecMulVec (fun i => Y i (.inr 0)) (incV F H'.x) +
        Matrix.vecMulVec (fun i => Y i (.inr 1)) (incV F H'.y) := by
      have : u = Y * (incM F (frame H'))ᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, h1, hone, Matrix.transpose_one, Matrix.mul_one]
      refine this.trans ?_
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, frame, incM, incV, Matrix.vecMulVec_apply, add_assoc]
    refine ⟨fun i => Y i (.inr 1), funext fun k => ?_⟩
    have h5 := congrFun (congrArg Prod.fst (congrArg co.e hu)) ((idx hd).symm (.inr k))
    rw [map_add, map_add, LinearEquiv.apply_symm_apply] at h5
    simp only [Prod.fst_add, Pi.add_apply, hlow, hx, Pi.zero_apply, zero_add, Equiv.apply_symm_apply, Sum.elim_inr] at h5
    exact h5.symm

end Plane

theorem exists_mixedEv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
      ∃ T : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) ∧
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          T (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (T Φ)) ∧
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          T (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = T Φ) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ T ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) ∧
        ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ∃ g : (Fin n → AE F E) → ℂ, (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable g μ ∧ ∫ y, g y ∂μ ≠ 0) ∧
            ∀ y, T (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ) = g y • φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ μ hμ
  have hd : d = d₁ + 2 := hH.rank
  obtain ⟨co, hlow, hx, hy, hrat⟩ := GlobalTheory.ThK.PlaneEv.Coords.exists_coords F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd
    hP.base hP.herm hP.skew hH hP₁.good
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.SympChange.darboux_change_rat F E σ n d X.J W.J M.co co hP.good.rat hrat
  obtain ⟨Gd, hGd, hact⟩ := exists_dbl G hGs
  obtain ⟨U, ei, ev, -, hmaps, hheis, hSB, -, -, hind, hpure, hbij⟩ := hasOpB_of_isSymp B.ψ hP.base.std Gd hGd
  have hloc : IsLocOp U := ⟨ei, ev, fun v φ hφ => hSB v ▸ Submodule.mem_map_of_mem hφ, hind, hpure⟩
  obtain ⟨p, hp⟩ := exists_plane_equiv hH hP.skew.lat hd co (fun z k => by rw [hlow]; exact planeZeroInsertion_apply_inr hd _ _) (fun a => (hx a).1) hy
  have e0 : ∀ w : Matrix (Fin d) (Fin n) (AE F E), d'.e w = M.co.e wᵀ := fun w => by
    rw [← hd', Matrix.transpose_transpose]
  have e1 : ∀ w : Matrix (Fin d₁) (Fin n) (AE F E), d₁'.e w = M₁.co.e wᵀ := fun w => by
    rw [← hd₁', Matrix.transpose_transpose]
  have key : ∀ (w₁ w₂ : Matrix (Fin d) (Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      U (dd.rho B.ψ (Matrix.fromCols w₁ w₂) Φ) = schr B.ψ (Sum.elim (co.e w₁ᵀ).1 (co.e w₂ᵀ).1,
        Sum.elim (co.e w₁ᵀ).2 (-(co.e w₂ᵀ).2)) (U Φ) := fun w₁ w₂ Φ hΦ => by
    rw [Darboux.rho, hheis _ Φ hΦ, hdd, hact, e0, e0, hGe, hGe]
  have hv : ∀ (u : Fin d → AE F E) (z : Fin n ⊕ Fin n → AE F E), Matrix.vecMulVec u z =
      Matrix.fromCols (Matrix.vecMulVec (z ∘ Sum.inl) u)ᵀ (Matrix.vecMulVec (z ∘ Sum.inr) u)ᵀ := fun u z => by
    ext i j; cases j <;> simp [Matrix.vecMulVec_apply, mul_comm]
  refine ⟨LinearMap.funLeft ℂ ℂ (fun b => glue (eps hd) 0 b) ∘ₗ U, fun Φ hΦ => slice_mem_schA (eps hd) 0 (hmaps Φ hΦ),
    fun z Φ hΦ => ?_, fun z Φ hΦ => ?_, fun l hl => ?_, fun φ hφ => ?_⟩
  · rw [← Matrix.fromCols_toCols z, Matrix.mul_fromCols, LinearMap.comp_apply, key _ _ Φ hΦ, Matrix.transpose_mul,
      Matrix.transpose_mul, hlow, hlow,
      elim_eq_glue hd _ _ 0 0 _ _ (planeZeroInsertion_apply_inr hd _) (planeZeroInsertion_apply_inr hd _) (planeZeroInsertion_apply_inl hd _) (planeZeroInsertion_apply_inl hd _),
      elim_eq_glue hd _ _ 0 0 (M₁.co.e z.toCols₁ᵀ).2 (-(M₁.co.e z.toCols₂ᵀ).2) (planeZeroInsertion_apply_inr hd _) (fun k => by simp)
        (planeZeroInsertion_apply_inl hd _) (fun k => by simp)]
    funext b
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Darboux.rho, schr, hdd₁ _ _, e1, glue_dot, glue_add,
      Sum.elim_zero_zero, zero_dotProduct, zero_add]
  · rw [hv, LinearMap.comp_apply, key _ _ Φ hΦ, Matrix.transpose_transpose, Matrix.transpose_transpose, (hx _).1, (hx _).1,
      elim_eq_glue hd _ (-(co.e (Matrix.vecMulVec (z ∘ Sum.inr) (incV F H'.x))).2) _ _ 0 0 (fun _ => rfl) (fun _ => rfl)
        (hx _).2 (fun k => by simp [(hx _).2])]
    funext b
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, schr, glue_dot, Sum.elim_zero_zero, zero_dotProduct,
      dotProduct_zero, add_zero, mul_zero, AddChar.map_zero_eq_one, one_mul]
  · rw [← LinearMap.comp_assoc]
    exact admissible_of_local_operator U hloc _ (admissible_of_slice_zero (eps hd) l hl)
  · obtain ⟨g₀, hg₀, hint⟩ := exists_weight p μ hμ
    have hΨ := reindex_mem (eps hd).symm (GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic F _ _ _ _
      (GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic F _ _ _ _ hg₀ (GlobalTheory.ConjSch.conj_mem_schA g₀ hg₀)) hφ)
    obtain ⟨Φ, hΦ, hU⟩ := hbij.surjOn hΨ
    refine ⟨Φ, hΦ, _, hint, fun y => ?_⟩
    rw [GlobalTheory.SiegelAvg.starFam_apply, hv, LinearMap.comp_apply, key _ _ Φ hΦ, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Sum.elim_comp_inl, Sum.elim_comp_inr, (hy _).1,
      elim_eq_glue hd _ _ (p y) (p y) 0 0 (hp y) (hp y) (hy y).2 (hy y).2, hU]
    funext b
    have hg : ∀ (a : (Fin n × Fin 2) ⊕ (Fin n × Fin 2) → AF F) (c : (Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F),
        glue (eps hd) a c ∘ (eps hd).symm = Sum.elim a c := fun a c => funext fun k => by simp [glue]
    simp only [LinearMap.funLeft_apply, schr, neg_zero, Sum.elim_zero_zero, dotProduct_zero, add_zero, mul_zero,
      AddChar.map_zero_eq_one, one_mul, glue_add, zero_add, hg, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Pi.smul_apply, smul_eq_mul]

end GlobalTheory.MixedVec

end
