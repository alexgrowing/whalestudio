import Development.WeilBound.ThetaLifts.SmallCones.SliceAd
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop

noncomputable section

namespace PositivityTheory.ThKCT.Line

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Ad PositivityTheory.ThKEst
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}

theorem cA_cA (h : IsCMExt F E σ) (a : AE F E) : cA σ (cA σ a) = a := by
  obtain ⟨t⟩ : Nonempty (E →+* ℂ) := inferInstance
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[F] σ (σ x) = _
    rw [t.injective (show t (σ (σ x)) = t x by rw [h.2.2.2, h.2.2.2]; exact Complex.conj_conj _)]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hTens_inc (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    hTens (cA σ) (incM F J) (incM F J') (incM F x) (incM F y) = inclR (F := F) (AF F) (hTens σ J J' x y) := by
  simp only [hTens, incM, Matrix.map_apply, map_sum, map_mul]
  rfl

theorem hTens_smul (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) (a b : E) :
    hTens σ J J' (a • x) (b • y) = a * σ b * hTens σ J J' x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem incM_smul (a : E) (x : Matrix (Fin n) (Fin d) E) : incM F (a • x) = inclR (F := F) (AF F) a • incM F x := by
  ext i j
  exact map_mul (inclR (F := F) (AF F)) _ _

theorem exists_dual (B : Base F E) {X : Spc F E n} {W : Spc F E d} {I : Set (Ten F E n d)} {v₀ z₀ : Matrix (Fin n) (Fin d) E}
    (hI : ∀ a : AE F E, a • incM F z₀ ∈ I) (hu : IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀)))
    {m : ℕ} (b : Module.Basis (Fin m) F E) : ∃ z, Dual σ X W I (fun j => b j • v₀) z := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 : hTens σ X.J W.J z₀ v₀ ≠ 0 := fun h => by
    rw [hTens_inc, h, map_zero] at hu
    exact (hu.map (piInf (B.emb w))).ne_zero (map_zero _)
  refine ⟨fun i => (-σ (b.traceDual i) / hTens σ X.J W.J z₀ v₀) • z₀, fun j a => ?_, fun i j => ?_⟩
  · rw [incM_smul, ← smul_assoc]
    exact hI _
  · rw [sy, symp, hTens_inc, hTens_smul, show -σ (b.traceDual i) / hTens σ X.J W.J z₀ v₀ * σ (b j) * hTens σ X.J W.J z₀ v₀ =
      -σ (b j * b.traceDual i) by rw [map_mul]; field_simp, map_neg, neg_one_mul, neg_neg]
    change Algebra.trace (AF F) _ ((1 : AF F) ⊗ₜ[F] _) = _
    rw [GlobalTheory.ThK.Dbl.Dense.trace_tmul, one_mul, show σ (b j * b.traceDual i) =
      AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ) (b j * b.traceDual i) from rfl,
      Algebra.trace_eq_of_algEquiv, Module.Basis.trace_mul_traceDual]
    simp only [eq_comm (a := i)]
    split_ifs <;> simp

theorem norm_piInf_smul (h : IsCMExt F E σ) {w : InfinitePlace F} (t : EmbOver E w) (y : AF F) (β : AE F E) :
    ‖piInf t (y • β)‖ = normAtPlace w (evI F y) * ‖piInf t β‖ := by
  haveI := h.1
  rw [Algebra.smul_def, map_mul, norm_mul, normAtPlace_apply_of_isReal (IsTotallyReal.isReal w)]
  congr 1
  change ‖infEmb t (evInf F w y ⊗ₜ[F] (1 : E))‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (y.1 w)‖
  rw [infEmb_tmul, map_one, mul_one, (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _)]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

def Nice {κ : Type} [Fintype κ] (μ : Measure (AE F E)ˣ) (z : ℕ) (v : AE F E → (κ → AF F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (φ : ι → (κ → Af F) → ℂ) (g : ι → AE F E → SInf F κ), (∀ i, φ i ∈ SB _) ∧ (∀ i, Continuous (g i)) ∧
    (∀ a, v a = ∑ i, pureA F (g i a) (φ i)) ∧
    ∀ q : Seminorm ℂ (SInf F κ), Continuous q → ∀ i, Integrable (fun l : (AE F E)ˣ => q (g i l) * (absE F E l : ℝ) ^ z) μ

set_option maxHeartbeats 800000 in
theorem nice (hS : Slice) (hT : TateAbs) {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {ι ι' I e}
    (he : IsEv B M M₁ ι ι' I e) {v₀ z₀ : Matrix (Fin n) (Fin d) E} (hI : ∀ a : AE F E, a • incM F z₀ ∈ I)
    (hu : IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀))) (τ : AE F E →ₐ[AF F] AE F E)
    (hτ : ∀ a, τ (τ a) = a) (μ : Measure (AE F E)ˣ) (hμ : μ.IsHaarMeasure) {z : ℕ} (hz : 2 ≤ z) {Ψ : Fn F n d}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) : Nice μ z fun a => e (M.co.rho B.ψ (τ a • incM F v₀) Ψ) := by
  induction hΨ using Submodule.span_induction with
  | zero =>
    refine ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun a => ?_, fun _ _ i => i.elim⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← map_zero e]
    exact congrArg e (funext fun x => mul_zero _)
  | add x y _ _ hx hy =>
    obtain ⟨ι₁, _, φ, g, h1, h2, h3, h4⟩ := hx
    obtain ⟨ι₂, _, φ', g', h1', h2', h3', h4'⟩ := hy
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim φ φ', Sum.elim g g', Sum.forall.2 ⟨h1, h1'⟩, Sum.forall.2 ⟨h2, h2'⟩, fun a => ?_,
      fun q hq => Sum.forall.2 ⟨h4 q hq, h4' q hq⟩⟩
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← h3 a, ← h3' a, ← map_add]
    congr 1
    exact funext fun x => mul_add _ _ _
  | smul c x _ hx =>
    obtain ⟨ι₁, _, φ, g, h1, h2, h3, h4⟩ := hx
    refine ⟨ι₁, inferInstance, fun i => c • φ i, g, fun i => Submodule.smul_mem _ _ (h1 i), h2, fun a => ?_, h4⟩
    simp only [GlobalTheory.ThK.Dbl.Dense.pureA_smul]
    rw [← Finset.smul_sum, ← h3 a, ← map_smul]
    congr 1
    exact funext fun x => mul_left_comm _ _ _
  | mem x hx =>
    obtain ⟨f, φ, hφ, rfl⟩ := hx
    obtain ⟨⟨_, -⟩, -, _, -, -, _, -⟩ := ideleTop F E
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
    let b := Module.finBasis F E
    let Bt := Algebra.TensorProduct.basis (AF F) b
    obtain ⟨zz, hD⟩ := exists_dual B hI hu b
    obtain ⟨r, φ₁, C, A, h1, h2, h3, h4, h5, h6⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he _ _ _ hD φ hφ
    let y : AE F E → Fin (Module.finrank F E) → AF F := fun a => Bt.equivFun (τ a)
    have hy : Continuous y := IsModuleTopology.continuous_of_linearMap (Bt.equivFun.toLinearMap ∘ₗ τ.toLinearMap)
    have e1 : ∀ a, τ a = ∑ j, y a j • Bt j := fun a => (Bt.sum_equivFun _).symm
    have e2 : ∀ a, a = ∑ j, y a j • τ (Bt j) := fun a => by
      conv_lhs => rw [← hτ a, e1 a, map_sum]
      simp only [map_smul]
    refine ⟨Fin r, inferInstance, φ₁, fun i a => A i (y a) f, h1, fun i => (h3 i f).comp hy, fun a => ?_, fun q hq i => ?_⟩
    · beta_reduce
      rw [← h4, lin, e1 a, Finset.sum_smul]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [incM_smul, smul_assoc, Algebra.TensorProduct.basis_apply]
      rfl
    obtain ⟨N, hN⟩ := hT F E σ B hB μ hμ z hz
    obtain ⟨p, -, hp⟩ := h6 q N hq
    have hN' := hN _ (h2.image (f := fun c => ∑ j, mk 0 (c j) • τ (Bt j)) (continuous_finsetSum _ fun j _ =>
      Continuous.smul (f := fun c : _ → Af F => mk 0 (c j)) (g := fun _ => τ (Bt j))
        (continuous_const.prodMk (continuous_apply j)) continuous_const))
    set K := ∑ j, ∑ w, ‖piInf (B.emb w) (τ (Bt j))‖ with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine ⟨((hq.comp ((h3 i f).comp (hy.comp Units.continuous_val))).mul
      ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).pow z)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun l => ?_) ((lintegral_indicator_le _ _).trans_lt
      ((lintegral_const_mul' (ENNReal.ofReal (p f * (1 + K) ^ N)) _ ENNReal.ofReal_ne_top).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN')))
    by_cases hl : (fun j => (y l j).2) ∈ C
    · rw [Set.indicator_of_mem, ← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal (by positivity)]
      · refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_div_assoc, mul_div_right_comm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [le_div_iff₀ (by positivity)]
        refine le_trans ?_ (mul_le_mul_of_nonneg_right (hp i (y l) f) (by positivity))
        rw [mul_assoc, ← mul_pow]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (apply_nonneg _ _)
        set s := ∑ j, ∑ w : InfinitePlace F, normAtPlace w (evI F (y l j)) with hs
        have hs1 : ∀ j w, normAtPlace w (evI F (y l j)) ≤ s := fun j w =>
          (Finset.single_le_sum (fun w _ => normAtPlace_nonneg w _) (Finset.mem_univ w)).trans
            (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, normAtPlace w (evI F (y l j)))
              (fun j _ => Finset.sum_nonneg fun w _ => normAtPlace_nonneg w _) (Finset.mem_univ j))
        have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => normAtPlace_nonneg w _
        have : ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ ≤ s * K := by
          rw [hK, Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_le_sum fun w _ => ?_
          conv_lhs => rw [e2 l, map_sum]
          rw [Finset.mul_sum]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_piInf_smul hB.cm]
          exact mul_le_mul_of_nonneg_right (hs1 j w) (norm_nonneg _)
        nlinarith
      · refine ⟨_, ⟨_, hl, rfl⟩, fun u hu => ?_⟩
        beta_reduce
        rw [congrArg (· - ∑ j, mk 0 (y l j).2 • τ (Bt j)) (e2 l), ← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← sub_smul, ← smul_assoc, show y l j - mk 0 (y l j).2 = mk (y l j).1 0 from
          Prod.ext (sub_zero _) (sub_self _), at_mk _ u hu, zero_smul]
    · simp only [h5 i _ hl, ContinuousLinearMap.zero_apply, map_zero, zero_mul, enorm_zero, zero_le]

end PositivityTheory.ThKCT.Line

end
