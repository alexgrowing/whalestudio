import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.SelmerRankBoundLaurent

noncomputable section
open MeasureTheory NumberField IsDedekindDomain Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo

namespace GlobalTheory.CompanionTheory.HtKernel

section Kernel
variable (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

theorem finite_gam (θ : Twist μ) {D C : Set (G1 K n)} (hD : IsCompact D) (hC : IsCompact C) :
    {γ : Gam K n | ∃ x ∈ D, x⁻¹ * (γ : G1 K n) * θ.e x ∈ C}.Finite := by
  have hS : IsCompact ((fun p : G1 K n × G1 K n × G1 K n => p.1 * p.2.1 * (θ.e p.2.2)⁻¹) '' (D ×ˢ C ×ˢ D)) := by
    refine (hD.prod (hC.prod hD)).image ?_
    exact (continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      ((θ.e.continuous.comp (continuous_snd.comp continuous_snd)).inv)
  have hcl : IsClosed (Gam K n : Set (G1 K n)) := Subgroup.isClosed_of_discrete
  have hT : IsCompact ((↑) ⁻¹' ((fun p : G1 K n × G1 K n × G1 K n => p.1 * p.2.1 * (θ.e p.2.2)⁻¹) '' (D ×ˢ C ×ˢ D)) : Set (Gam K n)) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  refine hT.finite_of_discrete.subset ?_
  rintro γ ⟨x, hx, hc⟩
  refine ⟨(x, _, x), ⟨hx, hc, hx⟩, ?_⟩
  simp [mul_assoc]

theorem continuous_twK (θ : Twist μ) (f : CC K n) : Continuous (twK θ f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨D, hDc, hDn⟩ := exists_compact_mem_nhds x₀
  have hfin := finite_gam K n μ θ hDc f.hasCompactSupport.isCompact
  have heq : ∀ x ∈ D, twK θ f x = ∑ γ ∈ hfin.toFinset, f (x⁻¹ * (γ : G1 K n) * θ.e x) := by
    intro x hx
    refine finsum_eq_sum_of_support_subset _ ?_
    intro γ hγ
    simp only [Set.Finite.coe_toFinset]
    exact ⟨x, hx, subset_tsupport _ hγ⟩
  have hc : Continuous fun x => ∑ γ ∈ hfin.toFinset, f (x⁻¹ * (γ : G1 K n) * θ.e x) :=
    continuous_finset_sum _ fun γ _ => f.continuous.comp
      ((continuous_inv.mul continuous_const).mul θ.e.continuous)
  exact hc.continuousAt.congr (Filter.eventually_of_mem hDn fun x hx => (heq x hx).symm)

theorem twK_gam_mul (θ : Twist μ) (f : CC K n) (δ x : G1 K n) (hδ : δ ∈ Gam K n) :
    twK θ f (δ * x) = twK θ f x := by
  have hθ : θ.e δ ∈ Gam K n := (θ.mem_gam δ).2 hδ
  let e : Gam K n ≃ Gam K n :=
    { toFun := fun γ => ⟨δ⁻¹ * γ * θ.e δ, mul_mem (mul_mem (inv_mem hδ) γ.2) hθ⟩
      invFun := fun γ => ⟨δ * γ * (θ.e δ)⁻¹, mul_mem (mul_mem hδ γ.2) (inv_mem hθ)⟩
      left_inv := fun γ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun γ => Subtype.ext (by simp [mul_assoc]) }
  unfold twK
  rw [← finsum_comp_equiv e (f := fun γ : Gam K n => f (x⁻¹ * (γ : G1 K n) * θ.e x))]
  refine finsum_congr fun γ => ?_
  congr 1
  simp [e, mul_assoc]

def normCC {K : Type} [Field K] [NumberField K] {n : ℕ} (f : CC K n) : CC K n where
  toFun x := ((‖f x‖ : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous.norm
  hasCompactSupport' := f.hasCompactSupport.mono fun x hx => by
    simpa using hx

theorem norm_twK_le (θ : Twist μ) (f : CC K n) (x : G1 K n) :
    ‖twK θ f x‖ ≤ ‖twK θ (normCC f) x‖ := by
  have hfin := finite_gam K n μ θ (isCompact_singleton (x := x)) f.hasCompactSupport.isCompact
  have h1 : twK θ f x = ∑ γ ∈ hfin.toFinset, f (x⁻¹ * (γ : G1 K n) * θ.e x) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro γ hγ
    simp only [Set.Finite.coe_toFinset]
    exact ⟨x, rfl, subset_tsupport _ hγ⟩
  have h2 : twK θ (normCC f) x = ∑ γ ∈ hfin.toFinset, ((‖f (x⁻¹ * (γ : G1 K n) * θ.e x)‖ : ℝ) : ℂ) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro γ hγ
    simp only [Set.Finite.coe_toFinset]
    refine ⟨x, rfl, subset_tsupport _ fun h0 => hγ ?_⟩
    change ((‖f (x⁻¹ * (γ : G1 K n) * θ.e x)‖ : ℝ) : ℂ) = 0
    simp [h0]
  rw [h1, h2, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact norm_sum_le _ _

end Kernel
end GlobalTheory.CompanionTheory.HtKernel

namespace GlobalTheory.CompanionTheory.HtKernel

open AutomorphicForm

section Local
variable {E : Type*} [NormedField E] {n : ℕ}

theorem continuous_locHeight : Continuous (locHeight : GL (Fin n) E → ℝ) := by
  have hc : Continuous fun g : GL (Fin n) E => (Finset.univ.sup fun p : Fin n × Fin n =>
      max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
        ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ : NNReal) := by
    refine Continuous.finset_sup_apply (s := Finset.univ) (f := fun (p : Fin n × Fin n) (g : GL (Fin n) E) =>
      max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
        ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) fun p _ => ?_
    refine Continuous.max ?_ ?_
    · exact continuous_nnnorm.comp (Continuous.matrix_elem Units.continuous_val _ _)
    · exact continuous_nnnorm.comp (Continuous.matrix_elem Units.continuous_coe_inv _ _)
  exact continuous_const.max (NNReal.continuous_coe.comp hc)

theorem isCompact_locHeight_le [ProperSpace E] (Y : ℝ) :
    IsCompact {h : GL (Fin n) E | locHeight h ≤ Y} := by
  have hA : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : E) Y : Set (Matrix (Fin n) (Fin n) E)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hB := hA.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hA)
  have hC := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) E)).isCompact_preimage hB
  refine hC.of_isClosed_subset (isClosed_Iic.preimage (continuous_locHeight (E := E) (n := n)) : IsClosed (locHeight ⁻¹' Set.Iic Y)) ?_
  intro h hh
  refine ⟨?_, ?_⟩
  · intro i _ j _
    simpa using (norm_apply_le_locHeight h i j).trans hh
  · intro i _ j _
    exact mem_closedBall_zero_iff.2 ((norm_inv_apply_le_locHeight h i j).trans hh)

end Local

theorem isCompact_restricted {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (C : ∀ i, Set (R i)) (hC : ∀ i, IsCompact (C i)) (hT : ∀ᶠ i in Filter.cofinite, C i ⊆ A i) :
    IsCompact {x : RestrictedProduct R A Filter.cofinite | ∀ i, x i ∈ C i} := by
  set S : Set ι := {i | C i ⊆ A i}
  have hS : (Filter.cofinite : Filter ι) ≤ Filter.principal S := Filter.le_principal_iff.2 hT
  have hM : IsCompact {x : RestrictedProduct R A (Filter.principal S) | ∀ i, x i ∈ C i} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ i _
      exact hx i
    · intro hy
      exact ⟨⟨y, Filter.eventually_principal.2 fun i hi => hi (hy i (Set.mem_univ i))⟩, fun i => hy i (Set.mem_univ i), rfl⟩
  convert hM.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, Filter.eventually_principal.2 fun i hi => hi (hx i)⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i

end GlobalTheory.CompanionTheory.HtKernel

namespace GlobalTheory.CompanionTheory.HtKernel
open AutomorphicForm

section Global
variable (K : Type) [Field K] [NumberField K] (n : ℕ)

theorem locHeight_mul_integral {v : HeightOneSpectrum (𝓞 K)} (a u : GL (Fin n) (v.adicCompletion K))
    (hu : u ∈ GLnLocal.integralGL (v.adicCompletion K) n) : locHeight (a * u) = locHeight a := by
  have h1 := locHeight_eq_one_of_mem_integralGL hu
  have h2 := locHeight_eq_one_of_mem_integralGL (inv_mem hu)
  refine le_antisymm ?_ ?_
  · simpa [h1] using locHeight_mul_le_of_ultrametric a u
  · simpa [h2] using locHeight_mul_le_of_ultrametric (a * u) u⁻¹

theorem isOpen_integral_everywhere :
    IsOpen {u : AdelicGLn.AdelicGL K n | ∀ v : HeightOneSpectrum (𝓞 K), finAt v u ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
  have ho := RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => GL (Fin n) (v.adicCompletion K))
    (A := fun v => (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))))
    fun v => GLnLocal.isOpen_integralGL _ n
  exact ho.preimage (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

theorem continuous_height : Continuous fun g : AdelicGLn.AdelicGL K n => AutomorphicForm.height g := by
  have hinf : Continuous fun g : AdelicGLn.AdelicGL K n => ∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult :=
    continuous_finset_prod _ fun w _ => (continuous_locHeight.comp (continuous_infAt w)).pow _
  rw [continuous_iff_continuousAt]
  intro g₀
  have hev : ∀ᶠ g in 𝓝 g₀, g₀⁻¹ * g ∈ {u : AdelicGLn.AdelicGL K n | ∀ v : HeightOneSpectrum (𝓞 K), finAt v u ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
    have hc : Continuous fun g : AdelicGLn.AdelicGL K n => g₀⁻¹ * g := continuous_const.mul continuous_id
    refine hc.continuousAt.eventually ((isOpen_integral_everywhere K n).mem_nhds ?_)
    intro v
    change finAt v (g₀⁻¹ * g₀) ∈ _
    rw [inv_mul_cancel, finAt_one]
    exact one_mem _
  have hk : ContinuousAt (fun g => (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g₀)) g₀ :=
    (hinf.mul continuous_const).continuousAt
  refine hk.congr (hev.mono fun g hg => ?_)
  have : ∀ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) = locHeight (finAt v g₀) := by
    intro v
    have h := locHeight_mul_integral K n (finAt v g₀) (finAt v (g₀⁻¹ * g)) (hg v)
    rwa [← finAt_mul, mul_inv_cancel_left] at h
  simp only [AutomorphicForm.height, this]

theorem absNorm_le_norm {v : HeightOneSpectrum (𝓞 K)} {x : v.adicCompletion K} (hx : 1 < ‖x‖) :
    (Ideal.absNorm v.asIdeal : ℝ) ≤ ‖x‖ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx; linarith
  have h := GroundTheory.Global.normalizedAbv_eq_zpow v hx0
  rw [GroundTheory.Global.normalizedAbv_apply] at h
  have hN : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => NumberField.HeightOneSpectrum.absNorm_ne_zero v (by simp [h])
    exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  rw [h] at hx ⊢
  set k := WithZero.log (Valued.v x)
  have hk : 1 ≤ k := by
    by_contra hk
    have : k ≤ 0 := by omega
    exact absurd hx (not_lt.2 (zpow_le_one_of_nonpos₀ hN this))
  calc (Ideal.absNorm v.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℤ) := by simp
    _ ≤ _ := zpow_le_zpow_right₀ hN hk

theorem mem_integralGL_of_locHeight_lt {v : HeightOneSpectrum (𝓞 K)} {g : GL (Fin n) (v.adicCompletion K)}
    (h : locHeight g < Ideal.absNorm v.asIdeal) : g ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  have key : ∀ x : v.adicCompletion K, ‖x‖ ≤ locHeight g → x ∈ v.adicCompletionIntegers K := by
    intro x hx
    have h1 : ‖x‖ ≤ 1 := by
      by_contra hc
      exact absurd (absNorm_le_norm K (not_le.1 hc)) (not_le.2 (lt_of_le_of_lt hx h))
    exact (Valued.toNormedField.norm_le_one_iff).1 h1
  rw [GLnLocal.mem_integralGL_iff]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
  exact ⟨fun i j => key _ (norm_apply_le_locHeight g i j), fun i j => key _ (norm_inv_apply_le_locHeight g i j)⟩

theorem properSpace_adic (v : HeightOneSpectrum (𝓞 K)) : ProperSpace (v.adicCompletion K) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hne : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hlt : ‖(π : v.adicCompletion K)‖ < 1 := by
    refine (Valued.toNormedField.norm_lt_one_iff).2 ?_
    rw [hv]
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    { (inferInstance : NormedField (v.adicCompletion K)) with
      non_trivial := ⟨(π : v.adicCompletion K)⁻¹, by
        rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 hne)).2 hlt⟩ }
  exact ProperSpace.of_locallyCompactSpace (v.adicCompletion K)

attribute [local instance] properSpace_adic

theorem locHeight_infAt_le_height (g : AdelicGLn.AdelicGL K n) (w : InfinitePlace K) :
    locHeight (infAt w g) ≤ AutomorphicForm.height g := by
  classical
  have h1 : locHeight (infAt w g) ≤ locHeight (infAt w g) ^ w.mult :=
    le_self_pow₀ (one_le_locHeight _) (InfinitePlace.mult_pos).ne'
  have h2 : locHeight (infAt w g) ^ w.mult ≤ ∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult :=
by
    rw [← Finset.mul_prod_erase Finset.univ (fun w : InfinitePlace K => locHeight (infAt w g) ^ w.mult) (Finset.mem_univ w)]
    refine le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) ?_
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
      le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _)
  exact (h1.trans h2).trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight g)) (one_le_finprod_locHeight g))

theorem locHeight_finAt_le_height (g : AdelicGLn.AdelicGL K n) (v : HeightOneSpectrum (𝓞 K)) :
    locHeight (finAt v g) ≤ AutomorphicForm.height g := by
  classical
  have h2 : locHeight (finAt v g) ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) := by
    have hs : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => locHeight (finAt v g)) ⊆
        ↑(insert v (finite_mulSupport_locHeight_finAt g).toFinset) := by
      intro u hu
      simp only [Finset.coe_insert, Set.Finite.coe_toFinset]
      exact Or.inr hu
    rw [finprod_eq_prod_of_mulSupport_subset _ hs,
      ← Finset.mul_prod_erase _ (fun v : HeightOneSpectrum (𝓞 K) => locHeight (finAt v g)) (Finset.mem_insert_self v _)]
    refine le_mul_of_one_le_right (locHeight_pos _).le ?_
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
      le_rfl fun _ _ => one_le_locHeight _
  exact h2.trans (le_mul_of_one_le_left (zero_le_one.trans (one_le_finprod_locHeight g)) (one_le_prod_locHeight g))

theorem eventually_lt_absNorm (Y : ℝ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, Y < Ideal.absNorm v.asIdeal := by
  have hfin : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ ⌊Y⌋₊}.Finite := Ideal.finite_setOf_absNorm_le _
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal := fun a b h => HeightOneSpectrum.ext h
  refine Filter.eventually_cofinite.2 ((hfin.preimage hinj.injOn).subset fun v hv => ?_)
  have h1 : (Ideal.absNorm v.asIdeal : ℝ) ≤ Y := not_lt.1 hv
  have h2 : 0 ≤ Y := (Nat.cast_nonneg _).trans h1
  exact Nat.le_floor h1

theorem isCompact_height_le (Y : ℝ) : IsCompact {g : AdelicGLn.AdelicGL K n | AutomorphicForm.height g ≤ Y} := by
  have hM := isCompact_restricted
    (A := fun v : HeightOneSpectrum (𝓞 K) => (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))))
    (fun v => {h : GL (Fin n) (v.adicCompletion K) | locHeight h ≤ Y})
    (fun v => isCompact_locHeight_le Y)
    ((eventually_lt_absNorm K Y).mono fun v hv h hh => mem_integralGL_of_locHeight_lt K n (lt_of_le_of_lt hh hv))
  have hI : IsCompact (Set.pi Set.univ fun w : InfinitePlace K => {h : GL (Fin n) w.Completion | locHeight h ≤ Y}) :=
    isCompact_univ_pi fun w => isCompact_locHeight_le Y
  have hW := (AdelicGLn.restrictedProductEquiv K n).toHomeomorph.isCompact_preimage.2 (hI.prod hM)
  refine hW.of_isClosed_subset (isClosed_Iic.preimage (continuous_height K n) : IsClosed ((fun g : AdelicGLn.AdelicGL K n => AutomorphicForm.height g) ⁻¹' Set.Iic Y)) ?_
  intro g hg
  exact ⟨fun w _ => (locHeight_infAt_le_height K n g w).trans hg, fun v => (locHeight_finAt_le_height K n g v).trans hg⟩

end Global
end GlobalTheory.CompanionTheory.HtKernel

namespace GlobalTheory.CompanionTheory.HtKernel

theorem isCompact_normOne_height_le (K : Type) [Field K] [NumberField K] (n : ℕ) (Y : ℝ) :
    IsCompact {g : G1 K n | AutomorphicForm.height (g : AdelicGLn.AdelicGL K n) ≤ Y} :=
  (isClosed_normOneGL (K := K) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_height_le K n Y)

theorem ell_normCC {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (σ : E ≃ₐ[F] E) {f : CC E n} (hf : Ell σ f) : Ell σ (normCC f) := by
  intro δ x y hy hne
  refine hf δ x y hy fun h0 => hne ?_
  change (((‖f y‖ : ℝ) : ℂ)) = 0
  simp [h0]

theorem exists_height_bound (K : Type) [Field K] [NumberField K] (n : ℕ) (f : CC K n) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ g : G1 K n, f g ≠ 0 → AutomorphicForm.height (g : AdelicGLn.AdelicGL K n) ≤ Y := by
  have hc : Continuous fun g : G1 K n => AutomorphicForm.height (g : AdelicGLn.AdelicGL K n) :=
    (continuous_height K n).comp continuous_subtype_val
  obtain ⟨m, hm1, hm⟩ := exists_one_le_bound f.hasCompactSupport.isCompact hc
  exact ⟨m, hm1, fun g hg => hm g (subset_tsupport _ hg)⟩

theorem twKQ_mk (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (θ : Twist μ) (f : CC K n) (x : G1 K n) : twKQ θ f (mk (Gam K n) x) = twK θ f x := by
  have h : mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x := Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 h
  change twK θ f (Quotient.out (mk (Gam K n) x)) = _
  rw [← hγ]
  exact twK_gam_mul K n μ θ f γ x γ.2

theorem exists_forall_norm_twK_le (G2h : G2) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (n : ℕ) (hn : 0 < n)
    (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ) (hθ : IsGalTwist σ θ) (f : CC E n) (hf : Ell σ f) :
    ∃ B : ℝ, ∀ x, ‖twK θ f x‖ ≤ B := by
  obtain ⟨C, c, hG⟩ := G2h F E σ hσ n hn
  obtain ⟨Y, hY1, hY⟩ := exists_height_bound E n (normCC f)
  have hker := hG μ θ hθ (normCC f) Y hY1 hY (ell_normCC σ hf)
  set Z := C * Y ^ c + 1 with hZ
  obtain ⟨B, hB⟩ := (isCompact_normOne_height_le E n Z).exists_bound_of_continuousOn
    (continuous_twK E n μ θ (normCC f)).continuousOn
  refine ⟨max B 0, fun x => ?_⟩
  refine (norm_twK_le E n μ θ f x).trans ?_
  by_cases h0 : twK θ (normCC f) x = 0
  · rw [h0, norm_zero]; exact le_max_right _ _
  have hq := hker x h0
  have : ∃ γ : Gam E n, AutomorphicForm.height (((γ : G1 E n) * x : G1 E n) : AdelicGLn.AdelicGL E n) < C * Y ^ c + 1 := by
    refine exists_lt_of_ciInf_lt (lt_of_le_of_lt hq (lt_add_one _))
  obtain ⟨γ, hγ⟩ := this
  rw [← twK_gam_mul E n μ θ (normCC f) γ x γ.2]
  exact (hB _ hγ.le).trans (le_max_left _ _)

theorem main : G2 → HtC := by
  intro G2h
  refine ⟨fun E _ _ n Y => isCompact_normOne_height_le E n Y, ?_⟩
  intro F E _ _ _ _ _ _ σ hσ n hn μ _ θ hθ f hf
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  obtain ⟨B, hB⟩ := exists_forall_norm_twK_le G2h F E σ hσ n hn μ θ hθ f hf
  have hm : Measurable (twKQ θ f) := by
    refine measurable_from_quotient.2 ?_
    have : (twKQ θ f) ∘ Quotient.mk'' = twK θ f := funext fun x => twKQ_mk E n μ θ f x
    rw [this]
    exact (continuous_twK E n μ θ f).measurable
  refine Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall fun y => ?_)
  exact hB _

end GlobalTheory.CompanionTheory.HtKernel
