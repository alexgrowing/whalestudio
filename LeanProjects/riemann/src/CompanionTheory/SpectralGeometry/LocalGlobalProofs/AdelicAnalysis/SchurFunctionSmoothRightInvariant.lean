import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.CoefEis

theorem tsum_integral_swap : ∀ (K X : Type) [Countable K] [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (T : K → X → ℂ) (C : ℝ), (∀ b, AEStronglyMeasurable (T b) μ) → (∀ x, Summable fun b => ‖T b x‖) → (∀ x, ∑' b, ‖T b x‖ ≤ C) → Integrable (fun x => ∑' b, T b x) μ ∧ Summable (fun b => ∫ x, T b x ∂μ) ∧ ∫ x, ∑' b, T b x ∂μ = ∑' b, ∫ x, T b x ∂μ := by
  intro K X _ _ μ _ T C hm hs hb
  have hbound : ∀ b x, ‖T b x‖ ≤ C := fun b x =>
    ((hs x).le_tsum b (fun _ _ => norm_nonneg _)).trans (hb x)
  have hint : ∀ b, Integrable (T b) μ := fun b =>
    Integrable.of_bound (hm b) C (ae_of_all _ (hbound b))
  have hlin : ∑' b, ∫⁻ x, ‖T b x‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (fun b => (hm b).enorm)]
    have h1 : ∀ x, ∑' b, ‖T b x‖ₑ ≤ ENNReal.ofReal C := by
      intro x
      have h2 : ∀ b, ‖T b x‖ₑ = ENNReal.ofReal ‖T b x‖ := fun b => (ofReal_norm_eq_enorm _).symm
      simp only [h2]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hs x)]
      exact ENNReal.ofReal_le_ofReal (hb x)
    refine ne_of_lt ((lintegral_mono h1).trans_lt ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hsn : Summable fun b => ∫ x, ‖T b x‖ ∂μ := by
    have h3 := ENNReal.summable_toReal hlin
    refine h3.congr fun b => ?_
    exact (integral_norm_eq_lintegral_enorm (hm b)).symm
  have hS := hasSum_integral_of_summable_integral_norm hint hsn
  refine ⟨?_, hS.summable, hS.tsum_eq.symm⟩
  refine Integrable.of_bound ?_ C (ae_of_all _ fun x => (norm_tsum_le_tsum_norm (hs x)).trans (hb x))
  refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset K))
    (f := fun s x => ∑ b ∈ s, T b x) (fun s => ?_) (ae_of_all _ fun x => (hs x).of_norm.hasSum)
  exact Finset.aestronglyMeasurable_fun_sum s fun b _ => hm b

theorem tsum_cosets : ∀ (K : Type) [AddCommGroup K] (H : AddSubgroup K) (f : K → ℂ), Summable f → ∑' b, f b = ∑' q : K ⧸ H, ∑' h : H, f (q.out + (h : K)) := by
  intro K _ H f hf
  let E : K ≃ (K ⧸ H) × H :=
    { toFun := fun b => ((b : K ⧸ H), ⟨-(b : K ⧸ H).out + b, QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (b : K ⧸ H))⟩)
      invFun := fun p => p.1.out + (p.2 : K)
      left_inv := fun b => by simp
      right_inv := by
        rintro ⟨q, h⟩
        have hq : ((q.out + (h : K) : K) : K ⧸ H) = q := by
          rw [QuotientAddGroup.mk_add_of_mem _ h.2]
          exact QuotientAddGroup.out_eq' q
        refine Prod.ext hq (Subtype.ext ?_)
        simp [hq] }
  have h1 : Summable (fun p : (K ⧸ H) × H => f (p.1.out + (p.2 : K))) :=
    (E.symm.summable_iff (f := f)).2 hf
  calc ∑' b, f b = ∑' p : (K ⧸ H) × H, f (p.1.out + (p.2 : K)) := (E.symm.tsum_eq f).symm
    _ = _ := h1.tsum_prod

theorem unfold_char : ∀ (κ : Type) [Fintype κ] (Λ : AddSubgroup (κ → ℝ)) [Countable Λ] (D : Set (κ → ℝ)), IsAddFundamentalDomain Λ D volume → ∀ (c e : (κ → ℝ) → ℂ), Integrable c → Continuous e → (∀ x, ‖e x‖ = 1) → (∀ x y, e (x + y) = e x * e y) → (∀ l ∈ Λ, e l = 1) → ∀ s : κ → ℝ, ∑' l : Λ, ∫ x in D, c (x + (s + (l : κ → ℝ))) * e x = e (-s) * ∫ x, c x * e x := by
  intro κ _ Λ _ D hD c e hc hecont he1 hadd hΛ s
  have hf : Integrable (fun x => c (x + s) * e x) volume := by
    refine (hc.comp_add_right s).mono
      ((hc.comp_add_right s).aestronglyMeasurable.mul hecont.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    simp [he1]
  have h1 := hD.integral_eq_tsum'' _ hf
  have h2 : ∫ x, c (x + s) * e x = e (-s) * ∫ x, c x * e x := by
    have h3 : ∀ x, c (x + s) * e x = (fun y => e (-s) * (c y * e y)) (x + s) := by
      intro x
      have h4 : e x = e (-s) * e (x + s) := by
        rw [← hadd]
        congr 1
        abel
      simp only []
      rw [h4]
      ring
    rw [integral_congr_ae (ae_of_all _ h3),
      integral_add_right_eq_self (μ := volume) (fun y => e (-s) * (c y * e y)) s, integral_const_mul]
  rw [← h2, h1]
  refine tsum_congr fun l => integral_congr_ae (ae_of_all _ fun x => ?_)
  have h4 : (l +ᵥ x) = (l : κ → ℝ) + x := rfl
  have h5 : x + (s + (l : κ → ℝ)) = (l : κ → ℝ) + x + s := by abel
  simp only [h4, h5, hadd, hΛ l l.2, one_mul]

theorem hasSum_integral_cosets : ∀ (G Q : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [Countable Q] (lf : Measure G) [lf.IsAddLeftInvariant] (s : Q → G) (W : Set G), IsOpen W → (∀ y, ∃ q, y - s q ∈ W) → (∀ q q', (∃ w ∈ W, ∃ w' ∈ W, s q + w = s q' + w') → q = q') → ∀ g : G → ℂ, Integrable g lf → (∀ y, ∀ w ∈ W, g (y + w) = g y) → HasSum (fun q => ((lf W).toReal : ℂ) * g (s q)) (∫ y, g y ∂lf) := by
  intro G Q _ _ _ _ _ _ lf _ s W hW hcov hdis g hg hper
  let E : Q → Set G := fun q => (fun y => -s q + y) ⁻¹' W
  have hEo : ∀ q, IsOpen (E q) := fun q => hW.preimage (by fun_prop)
  have hEm : ∀ q, MeasurableSet (E q) := fun q => (hEo q).measurableSet
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun y h1 h2 => hne (hdis q q' ⟨_, h1, _, h2, ?_⟩)
    change s q + (-s q + y) = s q' + (-s q' + y)
    rw [add_neg_cancel_left, add_neg_cancel_left]
  have hEc : ⋃ q, E q = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨q, hq⟩ := hcov y
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    change -s q + y ∈ W
    rwa [neg_add_eq_sub]
  have hS := hasSum_integral_iUnion (μ := lf) (f := g) hEm hEd (by rw [hEc]; exact hg.integrableOn)
  rw [hEc, setIntegral_univ] at hS
  have hq : ∀ q, ∫ a in E q, g a ∂lf = ((lf W).toReal : ℂ) * g (s q) := by
    intro q
    have h1 : ∫ a in E q, g a ∂lf = ∫ a in E q, g (s q) ∂lf := by
      refine setIntegral_congr_fun (hEm q) fun y hy => ?_
      have h2 := hper (s q) _ hy
      simpa using h2
    have h3 : lf (E q) = lf W := measure_preimage_add lf (-s q) W
    rw [h1, setIntegral_const, Measure.real, h3, Complex.real_smul]
  simp only [hq] at hS
  exact hS

theorem cosets_of_multiples : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → ∀ H : AddSubgroup F, (∀ b, b ∈ H ↔ ∃ r : 𝓞 F, b = (N : F) * (r : F)) → (∀ y : A F, ∃ q : F ⧸ H, y - algebraMap F (A F) q.out ∈ {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z}) ∧ ∀ q q' : F ⧸ H, (∃ w ∈ {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z}, ∃ w' ∈ {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z}, algebraMap F (A F) q.out + w = algebraMap F (A F) q'.out + w') → q = q' := by
  intro F _ _ N hN H hH
  obtain ⟨-, -, -, -, hOopen, hdense, hOint, -, -, hWopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hO0 : (0 : A F) ∈ Oh F := fun v => zero_mem _
  have hOsub : ∀ x y : A F, x ∈ Oh F → y ∈ Oh F → x - y ∈ Oh F :=
    fun x y hx hy v => sub_mem (hx v) (hy v)
  have hNal : algebraMap F (A F) (N : F) = (N : A F) := map_natCast _ N
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  constructor
  · intro y
    have hU : IsOpen {b : A F | y - b ∈ {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z}} :=
      (hWopen N hN).preimage (by fun_prop)
    obtain ⟨b, z, hz, hbz⟩ := hdense.exists_mem_open hU ⟨y, ⟨0, hO0, by simp⟩⟩
    refine ⟨((b : F) : F ⧸ H), ?_⟩
    have h1 : -b + ((b : F) : F ⧸ H).out ∈ H :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
    obtain ⟨r, hr⟩ := (hH _).1 h1
    have h2 : ((b : F) : F ⧸ H).out = b + (N : F) * (r : F) := by
      rw [← hr]
      abel
    refine ⟨z - algebraMap F (A F) (r : F), hOsub _ _ hz ((hOint _).2 ⟨r, rfl⟩), ?_⟩
    rw [h2, map_add, map_mul, hNal, mul_sub, ← hbz]
    ring
  · rintro q q' ⟨w, ⟨z, hz, rfl⟩, w', ⟨z', hz', rfl⟩, h⟩
    have h1 : algebraMap F (A F) (q.out - q'.out) = (N : A F) * (z' - z) := by
      rw [map_sub, mul_sub]
      linear_combination h
    have h2 : algebraMap F (A F) ((q.out - q'.out) / (N : F)) = z' - z := by
      have h3 : algebraMap F (A F) (N : F)⁻¹ * (N : A F) = 1 := by
        rw [← hNal, ← map_mul, inv_mul_cancel₀ hN0, map_one]
      rw [div_eq_mul_inv, map_mul, h1, mul_comm, ← mul_assoc, h3, one_mul]
    obtain ⟨r, hr⟩ := (hOint _).1 (h2 ▸ hOsub _ _ hz' hz)
    have h3 : -q'.out + q.out ∈ H := (hH _).2 ⟨r, by
      rw [hr]
      field_simp
      ring⟩
    have h4 : ((q'.out : F) : F ⧸ H) = ((q.out : F) : F ⧸ H) := QuotientAddGroup.eq.2 h3
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h4
    exact h4.symm

theorem mass_multiples : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ N : ℕ, 0 < N → (lf {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z}).toReal * (N : ℝ) ^ Module.finrank ℚ F = 1 := by
  intro F _ _ _ _ lf hlf h1 N hN
  obtain ⟨-, -, -, -, hOopen, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨h2, -⟩ := GlobalTheory.T.adelic_haar_measure_scaling F lf hlf h1
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h3 := h2 (N : F) hN0 (Oh F) hOopen.measurableSet
  have h4 : (fun x => algebraMap F (A F) (N : F) * x) '' Oh F = {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, map_natCast]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [h4, h1, mul_one] at h3
  have h5 : Algebra.norm ℚ (N : F) = (N : ℚ) ^ Module.finrank ℚ F := by
    have : (N : F) = algebraMap ℚ F (N : ℚ) := (map_natCast _ N).symm
    rw [this, Algebra.norm_algebraMap]
  rw [h3, h5]
  have h6 : (0 : ℝ) < (N : ℝ) ^ Module.finrank ℚ F := by positivity
  push_cast
  rw [abs_of_pos h6, ENNReal.toReal_ofReal (inv_nonneg.2 h6.le), inv_mul_cancel₀ h6.ne']

theorem sum_places_eq_trace : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ z : F, ∑ w, ρ w z = ((Algebra.trace ℚ F z : ℚ) : ℝ) := by
  intro F _ _ hTR ρ hρ z
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := z)
  have hreal : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ := by
    intro φ
    have hr : (InfinitePlace.mk φ).IsReal := IsTotallyReal.isReal _
    exact InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)
  let E : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
    { toFun := fun w => w.embedding.toRatAlgHom
      invFun := fun σ => InfinitePlace.mk (σ : F →+* ℂ)
      left_inv := fun w => by
        change InfinitePlace.mk w.embedding = w
        exact InfinitePlace.mk_embedding w
      right_inv := fun σ => by
        ext x
        change (InfinitePlace.mk (σ : F →+* ℂ)).embedding x = σ x
        rw [hreal]
        rfl }
  have h2 : ((∑ w, ρ w z : ℝ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
    rw [Complex.ofReal_sum, ← E.sum_comp]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hρ]
    rfl
  rw [← h1] at h2
  have h3 : ((∑ w, ρ w z : ℝ) : ℂ) = (((Algebra.trace ℚ F z : ℚ) : ℝ) : ℂ) := by
    rw [h2]
    simp
  exact_mod_cast h3

theorem Oh_mul_mem : ∀ (F : Type) [Field F] [NumberField F] (x y : A F), x ∈ Oh F → y ∈ Oh F → x * y ∈ Oh F := by
  intro F _ _ x y hx hy v
  exact mul_mem (hx v) (hy v)

theorem fourier_coeff_eis : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → Integrable (fstar ψ (hf F) (Bf B) (muF B lf) φ) lf → Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) → ∀ β : F, β ≠ 0 → ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ x ∈ Oh F, ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → IntegrableOn (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) φ y * ψ (-(algebraMap F (A F) β) * y) ∂lf) * ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ hΦ hc β hβ N hN hNβ hper D hD
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  have hcount : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  obtain ⟨-, hLcount, hLmem, hLD⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, horth⟩ := hLD D hD
  obtain ⟨-, -, -, -, hOopen, -, hOint, -, -, hWopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hψ'⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨hψ1, hψO, -⟩ := hψ' ψ hψ
  obtain ⟨C, hC⟩ := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ 1 one_pos
  haveI := hLcount
  haveI : lf.IsAddHaarMeasure := hlf

  set Φ := fstar ψ (hf F) (Bf B) (muF B lf) φ with hΦdef
  set c : (InfinitePlace F → ℝ) → ℂ := fun x => cG B ρ P (fun w => (x w : ℂ) + Complex.I) with hcdef
  set e : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hedef
  let j : F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun b w => ρ w b
      map_zero' := by ext w; simp
      map_add' := fun a b => by ext w; simp }
  have hj : ∀ b w, j b w = ρ w b := fun _ _ => rfl
  have hjinj : Function.Injective j := by
    intro a b hab
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (ρ w).injective (congrFun hab w)
  set al : F →+* A F := algebraMap F (A F) with hal

  have hecont : Continuous e := by
    simp only [hedef]
    fun_prop
  have henorm : ∀ x, ‖e x‖ = 1 := by
    intro x
    simp only [hedef]
    have : -(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)
        = ((-(2 * Real.pi * ∑ w, ρ w β * x w) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have headd : ∀ x y, e (x + y) = e x * e y := by
    intro x y
    simp only [hedef, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  have hechar : ∀ b : F, e (-(j b)) = ψ (-(al β) * al b) := by
    intro b
    have h2 : -(al β) * al b = al (-(β * b)) := by simp [hal]
    rw [h2, hψ.2]
    simp only [hedef]
    congr 1
    have h3 : (∑ w, ρ w β * (-(j b)) w) = -((Algebra.trace ℚ F (β * b) : ℚ) : ℝ) := by
      rw [← sum_places_eq_trace F hTR ρ hρ (β * b), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [hj]
    rw [h3, map_neg]
    push_cast
    ring

  let H : AddSubgroup F := (latR ρ N).comap j
  have hHmem : ∀ b, b ∈ H ↔ ∃ r : 𝓞 F, b = (N : F) * (r : F) := by
    intro b
    rw [AddSubgroup.mem_comap, hLmem]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, hjinj ?_⟩
      rw [hr]
      rfl
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  have hNal : ∀ n : ℕ, al (n : F) = (n : A F) := fun n => map_natCast _ n

  have hOr : ∀ r : 𝓞 F, al (r : F) ∈ Oh F := fun r => (hOint _).2 ⟨r, rfl⟩
  have heLat : ∀ l ∈ latR ρ N, e l = 1 := by
    intro l hl
    obtain ⟨r, rfl⟩ := (hLmem l).1 hl
    obtain ⟨r0, hr0⟩ := hNβ
    have h4 : (fun w => ρ w ((N : F) * (r : F))) = -(j (-((N : F) * (r : F)))) := by
      ext w
      simp [hj]
    rw [h4, hechar]
    have h5 : -(al β) * al (-((N : F) * (r : F))) = al ((r0 * r : 𝓞 F) : F) := by
      rw [← map_neg, ← map_mul]
      congr 1
      rw [show ((r0 * r : 𝓞 F) : F) = (r0 : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) r0 r, hr0]
      ring
    rw [h5]
    exact hψO _ (hOr _)
  have hap : ∀ b, ∀ h ∈ H, Φ (al (b + h)) = Φ (al b) := by
    intro b h hh
    obtain ⟨r, rfl⟩ := (hHmem h).1 hh
    have : al (b + (N : F) * (r : F)) = al b + (N : A F) * al (r : F) := by
      rw [map_add, map_mul, hNal]
    rw [this]
    exact hper _ (hOr r) _
  have hterm : ∀ (x : InfinitePlace F → ℝ) (b : F),
      eiTerm ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) b = Φ (al b) * c (x + j b) := by
    intro x b
    simp only [eiTerm, hcdef]
    congr 2
    funext w
    simp only [Pi.add_apply, hj]
    push_cast
    ring
  have hbd : ∀ x : InfinitePlace F → ℝ, Summable (fun b => ‖Φ (al b) * c (x + j b)‖) ∧
      ∑' b, ‖Φ (al b) * c (x + j b)‖ ≤ C := by
    intro x
    have h6 := hC (fun w => (x w : ℂ) + Complex.I) (fun w => by simp)
    simp only [hterm] at h6
    have h7 : wt M (fun w => (x w : ℂ) + Complex.I) = 1 := by simp [wt]
    rw [h7, one_mul] at h6
    exact h6
  have hDfin : volume D ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hDfin⟩
  set T : F → (InfinitePlace F → ℝ) → ℂ := fun b x => Φ (al b) * c (x + j b) * e x with hT
  have hTnorm : ∀ b x, ‖T b x‖ = ‖Φ (al b) * c (x + j b)‖ := by
    intro b x
    simp only [hT, norm_mul, henorm, mul_one]
  have hTmeas : ∀ b, AEStronglyMeasurable (T b) (volume.restrict D) := by
    intro b
    have h8 : AEStronglyMeasurable (fun x => c (x + j b)) volume :=
      (hc.comp_add_right (j b)).aestronglyMeasurable
    exact ((h8.const_mul _).mul hecont.aestronglyMeasurable).restrict
  obtain ⟨hInt, hSum, hEq⟩ := tsum_integral_swap F (InfinitePlace F → ℝ) (volume.restrict D) T C hTmeas
    (fun x => by simpa only [hTnorm] using (hbd x).1)
    (fun x => by simpa only [hTnorm] using (hbd x).2)
  have heInt : Integrable e (volume.restrict D) :=
    Integrable.of_bound hecont.aestronglyMeasurable 1 (ae_of_all _ fun x => (henorm x).le)
  have Heisenberg₂ : ∀ x : InfinitePlace F → ℝ,
      eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x = φ 0 * e x + ∑' b, T b x := by
    intro x
    simp only [eis, add_mul, hT, hterm, tsum_mul_right]
  have he0 : ∫ x in D, e x = 0 := by
    have h9 := horth (-β) (neg_ne_zero.2 hβ) (by
      obtain ⟨r0, hr0⟩ := hNβ
      exact ⟨-r0, by rw [show ((-r0 : 𝓞 F) : F) = -(r0 : F) from map_neg (algebraMap (𝓞 F) F) r0, hr0]; ring⟩)
    rw [← h9]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hedef]
    congr 1
    simp only [map_neg, neg_mul, Finset.sum_neg_distrib]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · have : (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x)
        = fun x => φ 0 * e x + ∑' b, T b x := funext Heisenberg₂
    rw [IntegrableOn, this]
    exact (heInt.const_mul _).add hInt
  · change ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x =
      ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, Φ y * ψ (-(al β) * y) ∂lf) * ∫ x, c x * e x
    set Ch : ℂ := ∫ x, c x * e x with hCh
    simp only [Heisenberg₂]
    rw [integral_add (heInt.const_mul _) hInt, integral_const_mul, he0, mul_zero, zero_add, hEq,
      tsum_cosets F H _ hSum]

    let eH : H ≃ latR ρ N := Equiv.ofBijective (fun h => ⟨j h, h.2⟩) (by
      constructor
      · intro a b hab
        exact Subtype.ext (hjinj (congrArg Subtype.val hab))
      · rintro ⟨l, hl⟩
        obtain ⟨r, rfl⟩ := (hLmem l).1 hl
        exact ⟨⟨(N : F) * (r : F), (hHmem _).2 ⟨r, rfl⟩⟩, rfl⟩)
    have hcoset : ∀ q : F ⧸ H, ∑' h : H, ∫ x in D, T (q.out + (h : F)) x =
        Φ (al q.out) * e (-(j q.out)) * Ch := by
      intro q
      have h10 : ∀ h : H, ∫ x in D, T (q.out + (h : F)) x =
          Φ (al q.out) * ∫ x in D, c (x + (j q.out + ((eH h : latR ρ N) : InfinitePlace F → ℝ))) * e x := by
        intro h
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hT]
        rw [hap _ _ h.2, map_add j, mul_assoc]
        rfl
      simp only [h10]
      rw [tsum_mul_left, eH.tsum_eq (fun l : latR ρ N =>
        ∫ x in D, c (x + (j q.out + (l : InfinitePlace F → ℝ))) * e x),
        unfold_char (InfinitePlace F) (latR ρ N) D hD c e hc hecont henorm headd heLat (j q.out)]
      ring
    simp only [hcoset]
    rw [tsum_mul_right]
    congr 1

    set W : Set (A F) := {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z} with hW
    obtain ⟨hcov, hdis⟩ := cosets_of_multiples F N hN H hHmem
    set G : A F → ℂ := fun y => Φ y * ψ (-(al β) * y) with hG
    have hGint : Integrable G lf := by
      refine hΦ.mono ?_ (ae_of_all _ fun y => ?_)
      · refine hΦ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
        exact hψ.1.comp (by fun_prop)
      · simp only [hG, norm_mul, hψ1, mul_one, le_refl]
    have hGper : ∀ y, ∀ w ∈ W, G (y + w) = G y := by
      rintro y w ⟨z, hz, rfl⟩
      obtain ⟨r0, hr0⟩ := hNβ
      have h11 : -(al β) * (y + (N : A F) * z) = -(al β) * y + al (-(r0 : F)) * z := by
        rw [hr0, ← hNal]
        simp only [map_neg, map_mul]
        ring
      have h12 : al (-(r0 : F)) * z ∈ Oh F := by
        rw [show -(r0 : F) = ((-r0 : 𝓞 F) : F) from (map_neg (algebraMap (𝓞 F) F) r0).symm]
        exact Oh_mul_mem F _ _ (hOr _) hz
      simp only [hG]
      rw [hper z hz y, h11, AddChar.map_add_eq_mul, hψO _ h12, mul_one]
    haveI : Countable (F ⧸ H) := Function.Surjective.countable (f := fun b : F => (b : F ⧸ H))
      (fun q => ⟨q.out, QuotientAddGroup.out_eq' q⟩)
    have hsum := hasSum_integral_cosets (A F) (F ⧸ H) lf (fun q => al q.out) W (hWopen N hN) hcov hdis G hGint hGper
    have h13 : ∀ q : F ⧸ H, G (al q.out) = Φ (al q.out) * e (-(j q.out)) := by
      intro q
      simp only [hG, hechar]
    have h14 := hsum.tsum_eq
    simp only [h13] at h14
    rw [tsum_mul_left] at h14
    rw [← h14, ← mul_assoc]
    have h15 := mass_multiples F lf hlf h1 N hN
    have h16 : (((N : ℂ) ^ Module.finrank ℚ F) * (((lf W).toReal : ℝ) : ℂ)) = 1 := by
      rw [mul_comm]
      exact_mod_cast h15
    rw [h16, one_mul]

end GlobalTheory.CompanionTheory.SW.CoefEis
