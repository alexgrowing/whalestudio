import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (EmbOver htInf htFin compInf compFin infProj opNorm)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt infNorm)
open GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem infEmb_tmul_one_eq_extensionEmbedding {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {w : InfinitePlace F} {τ : E →+* ℂ} (hτ : τ.comp (algebraMap F E) = w.embedding)
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) (b : Ainf F) :
    θ (b ⊗ₜ[F] (1 : E)) = InfinitePlace.Completion.extensionEmbedding w (b w) := by
  have hc : Continuous fun b : Ainf F => InfinitePlace.Completion.extensionEmbedding w (b w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have key := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hθ.2 hc ?_
  · exact congrFun key b
  funext x
  simp only [Function.comp_apply]
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', hθ.1,
    ← RingHom.comp_apply, hτ]
  simp

theorem htInf_eq_infMat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (t : EmbOver E w)
    [StarRing E] {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb t.1 θ) (g : HA (AF F) σ J) :
    htInf F w (bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J g)) =
      max 1 (max (opNorm (infMat σ J θ g)) (opNorm (infMat σ J θ g⁻¹))) := by
  have hre := infEmb_tmul_one_eq_extensionEmbedding t.2 hθ
  have hz : ∀ z : AF F ⊗[F] E, GlobalTheory.AdelicU.infEmb t (compInf F E w z) =
      θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have e : (fstA F a) ⊗ₜ[F] x = ((fstA F a) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by simp
      simp only [GlobalTheory.AdelicU.compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, GlobalTheory.AdelicU.infEmb_tmul]
      rw [e, map_mul, hre, hθ.1]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  have hm : ∀ k : HA (AF F) σ J, ((bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J k) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _).map (GlobalTheory.AdelicU.infEmb t) = infMat σ J θ k := by
    intro k
    ext i j
    exact hz _
  show max 1 (max (GlobalTheory.AdelicU.normInf F w _) (GlobalTheory.AdelicU.normInf F w _)) = _
  rw [GlobalTheory.AdelicU.normInf_eq_opNorm h t, GlobalTheory.AdelicU.normInf_eq_opNorm h t, ← map_inv (bc (compInf F E w)),
    ← map_inv (GlobalTheory.AdelicU.matHom _ σ J), hm, hm]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem htInf_eq_infHt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    htInf D.host.F (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (bc (compInf D.host.F D.host.E _) (Formalism.L2.Theta.matHom V g)) = infHt θ V τ g := by
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have ht : (tauE D τ).comp (algebraMap D.host.F D.host.E) =
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp (hcm.1.isReal _))).symm
  exact (htInf_eq_infMat hcm V.gram ⟨_, ht⟩ (hθ τ) g).trans rfl

private theorem htFin_eq_one_of_mem_GinfC {g : GA D V} (hg : g ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)) = 1 := by
  have hk : Formalism.L2.Theta.finHom V g = 1 := hg
  have hz : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, compFin D.host.F D.host.E v z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
  have h1 : bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g) = 1 := by
    apply Units.ext
    ext i j
    have hij : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) =
        ((1 : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix _ _ _) i j := by
      rw [← hk]; rfl
    show compFin D.host.F D.host.E v (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) = _
    rw [hz, hij, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1]
  refine (GlobalTheory.AdelicU.htOf_eq_one).2 ⟨?_, ?_⟩ <;> simpa using GlobalTheory.AdelicU.normFin_one_le D.host.F v

theorem height_eq_prod_infHt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    height V g = ∏ τ, (infHt θ V τ g : ℝ) := by
  have hinf : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) =
      ∏ τ, infHt θ V τ g :=
    (Fintype.prod_bijective _ (GlobalTheory.CMTypePlaces.places_bijective D) _ _
      fun τ => (htInf_eq_infHt V hθ τ g).symm).symm
  show ((GlobalTheory.AdelicU.heightGL D.host.F (Formalism.L2.Theta.matHom V g) : NNReal) : ℝ) = _
  rw [GlobalTheory.AdelicU.heightGL, hinf]
  simp only [htFin_eq_one_of_mem_GinfC V hg, finprod_one, mul_one, NNReal.coe_prod]

theorem normInf_le_height (hθ : IsInfFam θ) : ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g := by
  refine ⟨2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ), fun g => ?_⟩
  have hb : ∀ τ, (infHt θ V τ g : ℝ) ≤ height V g := fun τ => by
    have := htInf_le_height V g (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
    rwa [htInf_eq_infHt V hθ τ g] at this
  have he : ∀ τ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤
      2 * height V g := by
    intro τ i j
    have h1 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j
    have h2 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j
    have h3 : infNorm θ V τ g ≤ infHt θ V τ g := le_max_of_le_right (le_max_left _ _)
    have h4 : infNorm θ V τ g⁻¹ ≤ infHt θ V τ g := le_max_of_le_right (le_max_right _ _)
    have h3' : (infNorm θ V τ g : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h3).trans (hb τ)
    have h4' : (infNorm θ V τ g⁻¹ : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h4).trans (hb τ)
    have e3 : (infNorm θ V τ g : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖ := rfl
    have e4 : (infNorm θ V τ g⁻¹ : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹)‖ := rfl
    linarith
  calc normInf θ V g = ∑ τ, ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := rfl
    _ ≤ ∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, 2 * height V g := by
        gcongr with τ _ i _ j _
        exact he τ i j
    _ = 2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ) * height V g := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem height_le_normInf_pow (hθ : IsInfFam θ) : ∃ d : ℕ, ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · refine ⟨0, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, pow_zero]
    simp [GlobalTheory.SmoothForms.HeightCoset.infHt_rank_zero θ V h0]
  · refine ⟨Fintype.card D.what₂.Tau, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun τ _ => NNReal.coe_nonneg _)
      (fun τ _ => GlobalTheory.SmoothForms.HeightCoset.infHt_le_normInf θ V hpos τ g)

theorem normInf_height_comparison (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) :
    (∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g) ∧
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ GinfC V, height V g ≤ C * (1 + normInf θ V g) ^ d := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  refine ⟨⟨C, hC⟩, 1, d, fun g hg => ?_⟩
  have h0 : 0 ≤ normInf θ V g := by
    unfold Formalism.L2.Theta.normInf
    positivity
  calc height V g ≤ normInf θ V g ^ d := hd g hg
    _ ≤ (1 + normInf θ V g) ^ d := pow_le_pow_left₀ h0 (by linarith) d
    _ = 1 * (1 + normInf θ V g) ^ d := (one_mul _).symm

private theorem exists_coset_bound_of_modGrowthExp (V : HSp D) {d : ℕ} (hd : ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d) {A : ℕ}
    {f : GA D V → ℂ} (hf : ModGrowthExp V A f) (x : GA D V) :
    ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ (d * A) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := nonneg_of_growth hC
  refine ⟨C * height V x ^ A, fun g hg => ?_⟩
  have h1 : height V (x * g) ≤ height V x * normInf θ V g ^ d :=
    (height_mul_le V x g).trans (mul_le_mul_of_nonneg_left (hd g hg) (height_pos V x).le)
  calc ‖f (x * g)‖ ≤ C * height V (x * g) ^ A := hC _
    _ ≤ C * (height V x * normInf θ V g ^ d) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le h1 A) hC0
    _ = C * height V x ^ A * normInf θ V g ^ (d * A) := by rw [mul_pow, ← pow_mul]; ring

variable {V}

theorem exists_modGrowthExp_le_normInf_pow (hθ : IsInfFam θ) (A : ℕ) :
    ∃ N : ℕ, ∀ f : GA D V → ℂ, ModGrowthExp V A f →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  exact ⟨d * A, fun f hf x => exists_coset_bound_of_modGrowthExp V hd hf x⟩

theorem UnifModGrowth.growth (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) :
    ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨N, hN⟩ := exists_modGrowthExp_le_normInf_pow (V := V) hθ A
  exact ⟨N, fun l hl x => hN _ (hA l hl) x⟩

theorem UnifModGrowth.isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hz : ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) :
    IsAutFunSm θ V φ :=
  { toIsAutFun := ha, smooth := hs, zfin := hz, growth := h.growth hθ }

end GlobalTheory.Grow

end
