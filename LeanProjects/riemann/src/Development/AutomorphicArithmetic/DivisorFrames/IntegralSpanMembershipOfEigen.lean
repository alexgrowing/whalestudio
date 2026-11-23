import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.Casimir
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.LocalGen
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.NormGen
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem exists_higman_linear_map {R La : Type} [CommRing R] [AddCommGroup La] [Module R La] [Module.Finite R La]
    [Module.Projective R La] {n : ℕ} (a b : Fin n → R) (lam : R →+ ℤ) (m : ℕ)
    (h1 : ∀ x : R, ∑ j, lam (b j * x) • a j = (m : R) * x) :
    ∃ f : La →ₗ[ℤ] La, ∀ t, ∑ j, a j • f (b j • t) = m • t := by
  obtain ⟨k, s, i, -, -, hsi⟩ := Module.Finite.exists_comp_eq_id_of_projective R La
  let f : La →+ La :=
    { toFun := fun t => s (fun l => (lam (i t l) : R))
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by rw [← map_add s]; congr 1; ext l; simp }
  refine ⟨f.toIntLinearMap, fun t => ?_⟩
  have h2 : s (i t) = t := LinearMap.congr_fun hsi t
  conv_rhs => rw [← h2, ← map_nsmul]
  change ∑ j, a j • s (fun l => (lam (i (b j • t) l) : R)) = _
  simp only [← map_smul s, ← map_sum s]
  congr 1
  ext l
  simp only [Finset.sum_apply, Pi.smul_apply, map_smul, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← h1,
    zsmul_eq_mul, mul_comm]

private theorem projective_of_torsion_free_finite (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
    [Module.Finite (𝓞 E) La] [Module.IsTorsionFree ℤ La] : Module.Projective (𝓞 E) La := by
  have : Module.IsTorsionFree (𝓞 E) La := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    by_cases hr : r = 0
    · exact .inl hr
    right
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using hr
    have h2 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul, h, smul_zero]
    exact (smul_eq_zero.1 h2).resolve_left hN
  have : Module.FinitePresentation (𝓞 E) La := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

private theorem higman_trace_integrality {R K La : Type} [CommRing R] [Field K] (O : Subring K) [AddCommGroup La] [Module R La]
    (σ : R →+* K) (hσ : ∀ o, σ o ∈ O) {n : ℕ} (a b : Fin n → R) (m : ℕ) (hm0 : (m : K) ≠ 0) (hm : (m : K)⁻¹ ∈ O)
    (h2 : ∀ x : R, ∃ M : Fin n → Fin n → ℤ, (∀ j, x * a j = ∑ i, M i j • a i) ∧ ∀ i, x * b i = ∑ j, M i j • b j)
    (δ : K) (hδ : δ ≠ 0) (h3 : ∑ j, σ (a j) * σ (b j) = δ)
    (f : La →ₗ[ℤ] La) (hf : ∀ t, ∑ j, a j • f (b j • t) = m • t) (y : K ⊗[ℤ] La)
    (hy : ∀ o : R, ((LinearMap.lsmul R La o).restrictScalars ℤ).baseChange K y = σ o • y) :
    δ • y ∈ Submodule.span O (Set.range fun a : La => (1 : K) ⊗ₜ[ℤ] a) ↔
      ∃ z ∈ Submodule.span O (Set.range fun a : La => (1 : K) ⊗ₜ[ℤ] a), y - z ∈ Submodule.span K
        {u : K ⊗[ℤ] La | ∃ (o : R) (u' : K ⊗[ℤ] La),
          u = ((LinearMap.lsmul R La o).restrictScalars ℤ).baseChange K u' - σ o • u'} := by
  set L := Submodule.span O (Set.range fun a : La => (1 : K) ⊗ₜ[ℤ] a) with hL
  set N := Submodule.span K {u : K ⊗[ℤ] La | ∃ (o : R) (u' : K ⊗[ℤ] La),
    u = ((LinearMap.lsmul R La o).restrictScalars ℤ).baseChange K u' - σ o • u'} with hN
  obtain ⟨A, hA⟩ : ∃ A : R → (K ⊗[ℤ] La →ₗ[K] K ⊗[ℤ] La),
      A = fun o => ((LinearMap.lsmul R La o).restrictScalars ℤ).baseChange K := ⟨_, rfl⟩
  have hAt : ∀ o c t, A o (c ⊗ₜ t) = c ⊗ₜ (o • t) := fun o c t => by rw [hA]; rfl
  have hyA : ∀ o, A o y = σ o • y := fun o => by rw [hA]; exact hy o
  have hsm : ∀ c ∈ O, ∀ u ∈ L, c • u ∈ L := fun c hc u hu => L.smul_mem ⟨c, hc⟩ hu
  have hbc : ∀ g : La →ₗ[ℤ] La, ∀ u ∈ L, g.baseChange K u ∈ L := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨g t, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      change g.baseChange K ((c : K) • x) ∈ L
      rw [map_smul]; exact hsm c c.2 _ hx
  let P : K ⊗[ℤ] La →ₗ[K] K ⊗[ℤ] La := ∑ j, σ (b j) • A (a j)
  have hP : ∀ u, P u = ∑ j, σ (b j) • A (a j) u := fun u => by
    simp only [P, LinearMap.sum_apply, LinearMap.smul_apply]
  have hPy : P y = δ • y := by
    rw [hP, ← h3, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hyA, smul_smul, mul_comm]
  have hPA : ∀ o u, P (A o u) = σ o • P u := by
    intro o u
    obtain ⟨M, hMa, hMb⟩ := h2 o
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul c t =>
      rw [hP, hP, Finset.smul_sum]
      simp only [hAt, smul_smul, ← map_mul, hMb, mul_comm (a _) o, hMa, Finset.sum_smul, TensorProduct.tmul_sum,
        Finset.smul_sum, map_sum, map_zsmul, smul_assoc, TensorProduct.tmul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  constructor
  · intro hw
    have hF : ∀ u, ∑ j, A (a j) (f.baseChange K (A (b j) u)) = (m : K) • u := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, smul_add, Finset.sum_add_distrib, hx, hy]
      | tmul c t =>
        simp only [hAt, LinearMap.baseChange_tmul]
        rw [← TensorProduct.tmul_sum, hf, Nat.cast_smul_eq_nsmul, ← natCast_zsmul, TensorProduct.tmul_smul, natCast_zsmul]
    have hPF : P (f.baseChange K y) = (m : K) • y := by
      rw [← hF, hP]
      exact Finset.sum_congr rfl fun j _ => by rw [hyA, map_smul, map_smul]
    have hPN : ∀ u, P u - δ • u ∈ N := by
      intro u
      rw [hP, ← h3, Finset.sum_smul, ← Finset.sum_sub_distrib]
      refine N.sum_mem fun j _ => ?_
      rw [mul_comm, mul_smul, ← smul_sub]
      exact N.smul_mem _ (Submodule.subset_span ⟨a j, u, by rw [hA]⟩)
    refine ⟨(m : K)⁻¹ • f.baseChange K (δ • y), hsm _ hm _ (hbc f _ hw), ?_⟩
    have h4 := N.smul_mem (m : K)⁻¹ (hPN (f.baseChange K y))
    rwa [hPF, smul_sub, smul_smul, inv_mul_cancel₀ hm0, one_smul, ← map_smul] at h4
  · rintro ⟨z, hz, hyz⟩
    have hker : N ≤ LinearMap.ker P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨o, u, rfl⟩
      have := hPA o u
      rw [hA] at this
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, this, sub_self]
    have h4 : P y = P z := by
      have := hker hyz
      rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    rw [← hPy, h4, hP]
    refine L.sum_mem fun j _ => hsm _ (hσ _) _ ?_
    rw [hA]
    exact hbc _ _ hz

private theorem norm_integral_element_le_one {K R : Type} [NormedField K] [IsUltrametricDist K] [CommRing R] [Algebra.IsIntegral ℤ R]
    (σ : R →+* K) (o : R) : ‖σ o‖ ≤ 1 := by
  let v : Valuation K NNReal := NormedField.valuation
  have hi : IsIntegral ℤ (σ o) := (Algebra.IsIntegral.isIntegral (R := ℤ) o).map σ.toIntAlgHom
  have hi2 : IsIntegral v.integer (σ o) := hi.tower_top
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.1 hi2

theorem UpperTheory.integral_span_membership_of_eigen :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (σ : 𝓞 E →+* ℂ_[p]), ∃ δ : ℂ_[p], δ ≠ 0 ∧ Real.log ‖δ‖ = -(vDiff E p * Real.log p) ∧ ∀ (La : Type) [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] [Module.IsTorsionFree ℤ La] (y : ℂ_[p] ⊗[ℤ] La), (∀ o : 𝓞 E, ((LinearMap.lsmul (𝓞 E) La o).restrictScalars ℤ).baseChange ℂ_[p] y = σ o • y) → (δ • y ∈ Submodule.span ↥(intO ℂ_[p]) (Set.range fun a : La => (1 : ℂ_[p]) ⊗ₜ[ℤ] a) ↔ ∃ z ∈ Submodule.span ↥(intO ℂ_[p]) (Set.range fun a : La => (1 : ℂ_[p]) ⊗ₜ[ℤ] a), y - z ∈ Submodule.span ℂ_[p] {u : ℂ_[p] ⊗[ℤ] La | ∃ (o : 𝓞 E) (u' : ℂ_[p] ⊗[ℤ] La), u = ((LinearMap.lsmul (𝓞 E) La o).restrictScalars ℤ).baseChange ℂ_[p] u' - σ o • u'}) := by
  intro E _ _ _ p hp σ
  have hσi : Function.Injective σ := by
    refine (injective_iff_map_eq_zero σ).2 fun r hr => ?_
    by_contra hr0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : (Ideal.absNorm (Ideal.span {r}) : ℕ) ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using hr0
    have h2 := congrArg σ hc
    rw [map_mul, hr, mul_zero, map_natCast] at h2
    exact hN (Nat.cast_eq_zero.1 h2.symm)
  let φ : E →+* ℂ_[p] := IsFractionRing.lift hσi
  have hφ : ∀ x : 𝓞 E, φ (x : E) = σ x := fun x => IsFractionRing.lift_algebraMap hσi x
  obtain ⟨d, m, hd, hd0, hpm, hm⟩ := UpperTheory.WildB.localGen E p hp.out
  obtain ⟨n, a, b, lam, h1, h2, h3⟩ := UpperTheory.WildB.casimir E d m hd hd0 hm
  have hδ : φ (d : E) ≠ 0 := (map_ne_zero φ).2 (by simpa using hd0)
  refine ⟨φ (d : E), hδ, UpperTheory.WildB.normGen E p d m hd hpm hm φ, fun La _ _ _ _ y hy => ?_⟩
  have := projective_of_torsion_free_finite E La
  obtain ⟨f, hf⟩ := exists_higman_linear_map (La := La) a b lam m h1
  have hnm : ‖(m : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) m, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm
  refine higman_trace_integrality (intO ℂ_[p]) σ (fun o => ?_) a b m ?_ ?_ h2 _ hδ ?_ f hf y hy
  · exact norm_integral_element_le_one σ o
  · intro h
    rw [h, norm_zero] at hnm
    exact zero_ne_one hnm
  · change ‖(m : ℂ_[p])⁻¹‖ ≤ 1
    rw [norm_inv, hnm, inv_one]
  · simpa only [hφ, if_true] using h3 ℂ_[p] φ φ
