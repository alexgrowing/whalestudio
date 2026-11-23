import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR

noncomputable section

open Filter Topology TensorProduct

namespace GlobalTheory.WeakTop

section Val

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]

theorem mem_nhds_iff_lt {s : Set K} {x : K} :
    s ∈ 𝓝 x ↔ ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by
  rw [Valued.mem_nhds]
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ)) γ.1
    have hc' : (Valued.v : Valuation K Γ).restrict c = γ.1 := hc
    refine ⟨c, ?_, fun y hy => hγ ?_⟩
    · rintro rfl
      rw [map_zero] at hc'
      exact γ.ne_zero hc'.symm
    · change (Valued.v : Valuation K Γ).restrict (y - x) < γ.1
      rw [← hc', Valuation.restrict_lt_iff]
      exact hy
  · rintro ⟨c, hc, h⟩
    have h' : (Valued.v : Valuation K Γ).restrict c ≠ 0 := by simp [hc]
    refine ⟨Units.mk0 _ h', fun y hy => h ?_⟩
    exact (Valuation.restrict_lt_iff _).1 hy

theorem continuous_act_of_orbits {G : Type} [TopologicalSpace G] (σ : G → (K ≃+* K))
    (hσ : ∀ g x y, Valued.v x < Valued.v y → Valued.v (σ g x) < Valued.v (σ g y))
    (ho : ∀ x, Continuous fun g => σ g x) :
    Continuous fun p : G × K => σ p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, x₀⟩ s hs
  obtain ⟨c, hc, hs⟩ := mem_nhds_iff_lt.1 hs
  set b := (σ g₀).symm c with hb
  have hb0 : b ≠ 0 := by simpa [hb] using hc
  have hcb : σ g₀ b = c := by simp [hb]
  have h1 : ∀ᶠ g in 𝓝 g₀, Valued.v (σ g b) = Valued.v c := by
    have := (ho b).continuousAt (x := g₀) (hcb ▸ Valued.locally_const (x := c) (by simpa using hc))
    rw [← hcb]
    exact this
  have h2 : ∀ᶠ g in 𝓝 g₀, Valued.v (σ g x₀ - σ g₀ x₀) < Valued.v c :=
    (ho x₀).continuousAt (x := g₀) (mem_nhds_iff_lt.2 ⟨c, hc, subset_rfl⟩)
  have h3 : ∀ᶠ x in 𝓝 x₀, Valued.v (x - x₀) < Valued.v b :=
    mem_nhds_iff_lt.2 ⟨b, hb0, subset_rfl⟩
  rw [mem_map, nhds_prod_eq]
  filter_upwards [(h1.and h2).prod_mk h3] with ⟨g, x⟩ ⟨⟨a1, a2⟩, a3⟩
  apply hs
  have e : σ g x - σ g₀ x₀ = σ g (x - x₀) + (σ g x₀ - σ g₀ x₀) := by rw [map_sub]; ring
  change Valued.v (σ g x - σ g₀ x₀) < Valued.v c
  rw [e]
  exact Valuation.map_add_lt _ (a1 ▸ hσ g _ _ a3) a2

end Val

theorem exists_top_frac {A K G : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [TopologicalSpace G] (τ : G → (A ≃+* A))
    (σ : G → (K ≃+* K)) (hσ : ∀ g a, σ g (algebraMap A K a) = algebraMap A K (τ g a))
    (ho : ∀ (x a : A) (g₀ : G), a ≠ 0 → ∀ᶠ g in 𝓝 g₀, ¬ (τ g x - τ g₀ x ∣ a)) :
    ∃ t : TopologicalSpace K, letI := t
      T2Space K ∧ IsTopologicalRing K ∧ Continuous fun p : G × K => σ p.1 p.2 := by
  letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
  have hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x := by
    intro x y
    change (∃ c : A, c • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective A K
  refine ⟨inferInstance, inferInstance, inferInstance, continuous_act_of_orbits σ ?_ ?_⟩
  · intro g x y
    simp only [← not_le, hle]
    rintro h ⟨c, hc⟩
    refine h ⟨(τ g).symm c, (σ g).injective ?_⟩
    rw [map_mul, hσ, RingEquiv.apply_symm_apply, hc]
  · have hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x) := by
      intro x
      rw [continuous_iff_continuousAt]
      intro g₀ s hs
      obtain ⟨c, hc, hs⟩ := mem_nhds_iff_lt.1 hs
      obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A c
      have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hc
      rw [mem_map]
      filter_upwards [ho x a g₀ ha] with g hg
      apply hs
      change Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _
      rw [← not_le, hle, hσ, hσ, ← map_sub]
      rintro ⟨e, he⟩
      refine hg ⟨e * d, hinj ?_⟩
      rw [eq_div_iff hd0] at he
      rw [← he, map_mul, map_mul]
      ring
    intro x
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A x
    have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    simp only [map_div₀]
    exact (hA a).div (hA d) fun g => by simpa using hd0

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [TopologicalSpace R]

@[reducible] def wittTop (p : ℕ) (R : Type) [TopologicalSpace R] :
    TopologicalSpace (WittVector p R) :=
  TopologicalSpace.induced WittVector.coeff inferInstance

theorem continuous_peval [IsTopologicalRing R] {k : ℕ} (φ : MvPolynomial (Fin k × ℕ) ℤ)
    {X : Type} [TopologicalSpace X] (f : X → Fin k → ℕ → R) (hf : Continuous f) :
    Continuous fun x => WittVector.peval φ (f x) := by
  unfold WittVector.peval
  induction φ using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add φ ψ h1 h2 =>
    simp only [map_add]
    exact h1.add h2
  | mul_X φ i h =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact h.mul ((continuous_apply i.2).comp ((continuous_apply i.1).comp hf))

theorem isTopologicalRing_witt [IsTopologicalRing R] :
    letI := wittTop p R
    IsTopologicalRing (WittVector p R) := by
  letI := wittTop p R
  have hc : Continuous (WittVector.coeff : WittVector p R → ℕ → R) := continuous_induced_dom
  have h2 : Continuous fun x : WittVector p R × WittVector p R => ![x.1.coeff, x.2.coeff] := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact hc.comp continuous_fst
    · exact hc.comp continuous_snd
  have h1 : Continuous fun x : WittVector p R => ![x.coeff] := by
    refine continuous_pi fun i => ?_
    fin_cases i
    exact hc
  refine { continuous_add := ?_, continuous_mul := ?_, continuous_neg := ?_ }
  · refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
    simp only [Function.comp_apply, WittVector.add_coeff]
    exact continuous_peval _ _ h2
  · refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
    simp only [Function.comp_apply, WittVector.mul_coeff]
    exact continuous_peval _ _ h2
  · refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
    simp only [Function.comp_apply, WittVector.neg_coeff]
    exact continuous_peval _ _ h1

theorem t2Space_wittVector_product [T2Space R] :
    letI := wittTop p R
    T2Space (WittVector p R) := by
  letI := wittTop p R
  exact T2Space.of_injective_continuous (f := (WittVector.coeff : WittVector p R → ℕ → R))
    (fun x y h => WittVector.ext fun n => congrFun h n) continuous_induced_dom

theorem continuous_map_witt {G : Type} [TopologicalSpace G] (σ : G → (R →+* R))
    (h : Continuous fun q : G × R => σ q.1 q.2) :
    letI := wittTop p R
    Continuous fun q : G × WittVector p R => WittVector.map (σ q.1) q.2 := by
  letI := wittTop p R
  have hc : Continuous (WittVector.coeff : WittVector p R → ℕ → R) := continuous_induced_dom
  refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
  simp only [Function.comp_apply, WittVector.map_coeff]
  exact h.comp (continuous_fst.prodMk ((continuous_apply n).comp (hc.comp continuous_snd)))

theorem continuous_padicInt_witt [CharP R p] (f : ℤ_[p] →+* WittVector p R) :
    letI := wittTop p R
    Continuous f := by
  letI := wittTop p R
  refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  have hp : (0 : ℝ) < (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton'] at hy
  obtain ⟨z, hz⟩ := hy
  have h0 : WittVector.truncate (n + 1) (f y - f x) = 0 := by
    rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro i hi
    rw [← map_sub, ← hz, map_mul, map_pow, map_natCast]
    exact WittVector.mul_pow_charP_coeff_zero _ hi
  rw [map_sub, sub_eq_zero] at h0
  have := congrArg (TruncatedWittVector.coeff (Fin.last n)) h0
  simpa [WittVector.coeff_truncate] using this

end Witt

section Tensor

variable {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W] [Algebra R W]
  [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι] [DecidableEq ι]

def coords (W : Type) [CommRing W] [Algebra R W] (O : Type) [CommRing O] [Algebra R O] [Module O T]
    [IsScalarTower R O T] (b : Module.Basis ι R T) : ((O ⊗[R] W) ⊗[O] T) ≃+ (ι → W) :=
  (TensorProduct.comm O (O ⊗[R] W) T).toAddEquiv.trans
    ((AlgebraTensorModule.cancelBaseChange R O O T W).toAddEquiv.trans
      ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
        (Finsupp.linearEquivFunOnFinite R W ι).toAddEquiv))

theorem coords_tmul (b : Module.Basis ι R T) (a : O) (w : W) (t : T) (i : ι) :
    coords W O b ((a ⊗ₜ[R] w) ⊗ₜ[O] t) i = b.repr (a • t) i • w := by
  simp [coords]

theorem coords_map (b : Module.Basis ι R T) (σ : W →ₐ[R] W) (ρ : T →ₗ[O] T)
    (x : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    coords W O b (TensorProduct.map
      (Algebra.TensorProduct.map (AlgHom.id O O) σ).toLinearMap ρ x) i =
      ∑ j, algebraMap R W (b.repr (ρ (b j)) i) * σ (coords W O b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [add_tmul, map_add, Pi.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
    | tmul a w =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, coords_tmul, map_smul σ]
      rw [← map_smul ρ]
      generalize a • t = u
      conv_lhs => rw [← b.sum_repr u]
      simp only [map_sum, LinearMap.map_smul_of_tower, map_smul, Finsupp.coe_finset_sum,
        Finset.sum_apply, Finsupp.smul_apply, Finset.sum_smul, smul_eq_mul, Algebra.smul_def,
        map_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_top_tensor [TopologicalSpace R] [TopologicalSpace W] [IsTopologicalRing W]
    [T2Space W] [TopologicalSpace T] [CompactSpace T] {G : Type} [TopologicalSpace G]
    (b : Module.Basis ι R T) (hb : ∀ i, Continuous fun t => b.repr t i)
    (hc : Continuous (algebraMap R W)) (hi : Function.Injective (algebraMap R W))
    (σ : G → (W →ₐ[R] W)) (hσ : Continuous fun q : G × W => σ q.1 q.2)
    (ρ : G → (T →ₗ[O] T)) (hρ : ∀ i j, Continuous fun g => b.repr (ρ g (b j)) i) :
    ∃ τ : TopologicalSpace ((O ⊗[R] W) ⊗[O] T), letI := τ
      T2Space ((O ⊗[R] W) ⊗[O] T) ∧ IsTopologicalAddGroup ((O ⊗[R] W) ⊗[O] T) ∧
      Continuous (fun q : G × ((O ⊗[R] W) ⊗[O] T) => TensorProduct.map
        (Algebra.TensorProduct.map (AlgHom.id O O) (σ q.1)).toLinearMap (ρ q.1) q.2) ∧
      Topology.IsEmbedding (fun t : T => (1 : O ⊗[R] W) ⊗ₜ[O] t) := by
  letI τ : TopologicalSpace ((O ⊗[R] W) ⊗[O] T) :=
    TopologicalSpace.induced (coords W O b) inferInstance
  have h0 : Continuous (coords W O b) := continuous_induced_dom
  haveI h2 : T2Space ((O ⊗[R] W) ⊗[O] T) :=
    T2Space.of_injective_continuous (coords W O b).injective h0
  have h1 : ∀ (t : T) i, coords W O b ((1 : O ⊗[R] W) ⊗ₜ[O] t) i = algebraMap R W (b.repr t i) := by
    intro t i
    rw [Algebra.TensorProduct.one_def, coords_tmul, one_smul, Algebra.algebraMap_eq_smul_one]
  refine ⟨τ, h2, Topology.IsInducing.topologicalAddGroup (coords W O b) ⟨rfl⟩, ?_, ?_⟩
  · refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    simp only [Function.comp_apply, coords_map]
    refine continuous_finset_sum _ fun j _ => ?_
    exact ((hc.comp (hρ i j)).comp continuous_fst).mul
      (hσ.comp (continuous_fst.prodMk ((continuous_apply j).comp (h0.comp continuous_snd))))
  · refine (Continuous.isClosedEmbedding ?_ ?_).isEmbedding
    · refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
      simp only [Function.comp_apply, h1]
      exact hc.comp (hb i)
    · intro s t h
      refine b.ext_elem fun i => hi ?_
      rw [← h1, ← h1]
      exact congrArg (fun x => coords W O b x i) h

end Tensor

theorem compact_of_basis {p : ℕ} [Fact p.Prime] {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T]
    [TopologicalSpace T] [ContinuousAdd T] [Fintype ι] (b : Module.Basis ι ℤ_[p] T)
    (h : ∀ t : T, Continuous fun c : ℤ_[p] => c • t) :
    CompactSpace T ∧ ∀ U ∈ 𝓝 (0 : T), ∃ k : ℕ, ∀ t : T, p ^ k • t ∈ U := by
  have hF : Continuous (b.equivFun.symm : (ι → ℤ_[p]) → T) := by
    have : (b.equivFun.symm : (ι → ℤ_[p]) → T) = fun c => ∑ i, c i • b i :=
      funext fun c => b.equivFun_symm_apply c
    rw [this]
    exact continuous_finset_sum _ fun i _ => (h (b i)).comp (continuous_apply i)
  refine ⟨b.equivFun.symm.surjective.compactSpace hF, fun U hU => ?_⟩
  have h1 : b.equivFun.symm ⁻¹' U ∈ 𝓝 (0 : ι → ℤ_[p]) :=
    hF.continuousAt (by simpa using hU)
  obtain ⟨ε, hε, hU'⟩ := Metric.mem_nhds_iff.1 h1
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k, fun t => ?_⟩
  obtain ⟨c, rfl⟩ := b.equivFun.symm.surjective t
  rw [← map_nsmul]
  apply hU'
  rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
  intro i
  refine lt_of_le_of_lt ?_ hk
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem eventually_coeff_eq (AI : LocAinf l P) (x : OCb l) (n : ℕ) (g₀ : GQ l) :
    ∀ᶠ g in 𝓝 g₀, PreTilt.coeff n (AI.actT g x) = PreTilt.coeff n (AI.actT g₀ x) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  have hc := GlobalTheory.Cyc.IsActC.continuous_orbit l AI.actC ⟨AI.actC_ext, AI.actC_norm⟩
    (y : PadicComplex l)
  have hl : ((l : ℕ) : PadicComplex l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨y₀, hy₀, e₀⟩ := AI.actT_coeff g₀ x n y hy.symm
  filter_upwards [hc.continuousAt (x := g₀) (Metric.ball_mem_nhds _ (norm_pos_iff.2 hl))] with g hg
  obtain ⟨y₁, hy₁, e₁⟩ := AI.actT_coeff g x n y hy.symm
  rw [e₀, e₁, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    ← (PadicComplexInt.integers l).le_iff_dvd]
  have hg' : ‖(y₁ : PadicComplex l) - y₀‖ ≤ ‖((l : ℕ) : PadicComplex l)‖ := by
    rw [hy₀, hy₁, ← dist_eq_norm]
    exact le_of_lt hg
  rw [map_natCast, map_sub]
  rw [PadicComplex.norm_eq_norm, PadicComplex.norm_eq_norm, Valuation.norm_def, Valuation.norm_def,
    NNReal.coe_le_coe, (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_iff] at hg'
  exact hg'

theorem exists_top_Cb (AI : LocAinf l P) :
    ∃ t : TopologicalSpace (Cb l), letI := t
      T2Space (Cb l) ∧ IsTopologicalRing (Cb l) ∧
        Continuous fun q : GQ l × Cb l => autCb l (AI.actT q.1) q.2 := by
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2
  refine exists_top_frac (fun g => AI.actT g) (fun g => autCb l (AI.actT g))
    (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0 := by
    by_contra! h
    refine ha (Perfection.ext fun n => ?_)
    change PreTilt.coeff n a = PreTilt.coeff n 0
    rw [h, map_zero]
  filter_upwards [eventually_coeff_eq AI x n g₀] with g hg
  rintro ⟨c, hc⟩
  apply hn
  rw [hc, map_mul, map_sub, hg, sub_self, zero_mul]

theorem zlW_injective (R : Type) [CommRing R] [CharP R l] : Function.Injective (zlW l R) :=
  (WittVector.map_injective _ (ZMod.castHom_injective R)).comp (WittVector.equiv l).symm.injective

theorem exists_top_lat {G L O W : Type} [Group G] [TopologicalSpace G] [Field L] [Algebra ℚ_[l] L]
    [CommRing O] [Algebra O L] [TopologicalSpace L] [Algebra ℤ_[l] O] [FiniteDimensional ℚ_[l] L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul ℚ_[l] L] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O]
    (hc : ∀ c : ℤ_[l], algebraMap O L (algebraMap ℤ_[l] O c) =
      algebraMap ℚ_[l] L (algebraMap ℤ_[l] ℚ_[l] c))
    [CommRing W] [Algebra ℤ_[l] W] [TopologicalSpace W] [IsTopologicalRing W] [T2Space W]
    (hW : Continuous (algebraMap ℤ_[l] W)) (hi : Function.Injective (algebraMap ℤ_[l] W))
    (σ : G → (W →ₐ[ℤ_[l]] W)) (hσ : Continuous fun q : G × W => σ q.1 q.2)
    (T : LocLat G ℚ_[l] L O) :
    ∃ τ : TopologicalSpace (TW (O ⊗[ℤ_[l]] W) T), letI := τ
      T2Space (TW (O ⊗[ℤ_[l]] W) T) ∧ IsTopologicalAddGroup (TW (O ⊗[ℤ_[l]] W) T) ∧
      Continuous (fun q : G × TW (O ⊗[ℤ_[l]] W) T =>
        TWact (Algebra.TensorProduct.map (AlgHom.id O O) (σ q.1)) T q.1 q.2) ∧
      Topology.IsEmbedding (fun t : ↥T.L.T => (1 : O ⊗[ℤ_[l]] W) ⊗ₜ[O] t) ∧
      CompactSpace ↥T.L.T ∧ ∀ U ∈ nhds (0 : ↥T.L.T), ∃ k : ℕ, ∀ t : ↥T.L.T, l ^ k • t ∈ U := by
  letI := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
  haveI : IsScalarTower ℤ_[l] O ↥T.L.T := ⟨fun c a x => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  obtain ⟨d, ⟨b⟩⟩ := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hb : ∀ i, Continuous fun t : ↥T.L.T => b.repr t i := by
    intro i
    obtain ⟨φ, hφ⟩ := GlobalTheory.Cyc.exists_form_lat hc T b i
    have h1 : Continuous φ := GlobalTheory.Cyc.continuous_form_of_moduleTopology (L := L) φ
    exact hemb.continuous_iff.2 ((h1.comp continuous_subtype_val).congr hφ)
  have hρ : ∀ i j, Continuous fun g : G => b.repr (T.actT g (b j)) i := fun i j =>
    hemb.continuous_iff.2 (GlobalTheory.Cyc.continuous_coord_lat hc T b (b j) i)
  have hs : ∀ t : ↥T.L.T, Continuous fun c : ℤ_[l] => c • t := by
    intro t
    refine continuous_induced_rng.2 ?_
    haveI : ContinuousSMul L T.V := IsModuleTopology.toContinuousSMul _ _
    have h1 : Continuous fun c : ℤ_[l] =>
        algebraMap ℚ_[l] L (algebraMap ℤ_[l] ℚ_[l] c) • (t : T.V) :=
      ((continuous_algebraMap ℚ_[l] L).comp hemb.continuous).smul continuous_const
    refine h1.congr fun c => ?_
    rw [← hc, algebraMap_smul]
    rfl
  haveI : ContinuousAdd ↥T.L.T := T.L.T.toAddSubmonoid.continuousAdd
  obtain ⟨hcpt, hU⟩ := compact_of_basis b hs
  obtain ⟨τ, a1, a2, a3, a4⟩ := exists_top_tensor (O := O) (W := W) b hb hW hi σ hσ
    (fun g => T.actT g) hρ
  exact ⟨τ, a1, a2, a3, a4, hcpt, hU⟩

theorem exists_top_WCb (AI : LocAinf l P) :
    ∃ t : TopologicalSpace (WCb l), letI := t
      T2Space (WCb l) ∧ IsTopologicalRing (WCb l) ∧ Continuous (algebraMap ℤ_[l] (WCb l)) ∧
        Continuous fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2 := by
  obtain ⟨t, h2, hr, ha⟩ := exists_top_Cb AI
  exact ⟨wittTop l (Cb l), t2Space_wittVector_product, isTopologicalRing_witt,
    continuous_padicInt_witt (zlW l (Cb l)),
    continuous_map_witt (fun g : GQ l => (autCb l (AI.actT g)).toRingHom) ha⟩

open GlobalTheory.HWL in

theorem exists_weakTop : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ Continuous (fun p : ↥(GK K) × TW (RW LL) T => TWact (AI.gRW LL (p.1 : GQ l)) T p.1 p.2) ∧ Topology.IsEmbedding (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ CompactSpace ↥T.L.T ∧ ∀ U ∈ nhds (0 : ↥T.L.T), ∃ k : ℕ, ∀ t : ↥T.L.T, l ^ k • t ∈ U := by
  intro l _ P AI K LL T
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  letI t : TopologicalSpace (WCb l) := (exists_top_WCb AI).choose
  have ht := (exists_top_WCb AI).choose_spec
  haveI : T2Space (WCb l) := ht.1
  haveI : IsTopologicalRing (WCb l) := ht.2.1
  have hW := ht.2.2.1
  have ha := ht.2.2.2
  have hp : Continuous fun q : ↥(GK K) × WCb l => (((q.1 : GQ l), q.2) : GQ l × WCb l) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hσ := ha.comp hp
  have hi : Function.Injective (algebraMap ℤ_[l] (WCb l)) := zlW_injective (Cb l)
  have key := exists_top_lat (G := ↥(GK K)) (L := ↥LL.1) (O := ↥(OL LL)) (W := WCb l) hc hW hi
    (fun g : ↥(GK K) => (AI.actWCbHom (g : GQ l)).toAlgHom) hσ T
  exact key

end GlobalTheory.WeakTop
