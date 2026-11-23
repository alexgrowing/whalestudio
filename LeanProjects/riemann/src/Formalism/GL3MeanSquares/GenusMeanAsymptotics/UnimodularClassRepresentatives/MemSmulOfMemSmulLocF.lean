import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients

open LocalSpans idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem le_locF (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (L : Submodule (𝓞 K) V) : L ≤ locF 𝔭 L := fun x hx =>
  (mem_locF 𝔭 L x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h,
    by simpa using hx⟩

theorem ι_mem_pow {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) : ι a ∈ extP K 𝔭 ^ k :=
  (mem_pow_iff 𝔭 k a).2 ha

theorem exists_approx {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) {w : V}
    (hw : w ∈ locF 𝔭 L) : ∃ c : 𝓞 F, c - 1 ∈ 𝔭 ^ k ∧ ι c • w ∈ L := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, h⟩ := (mem_locF 𝔭 L w).1 hw
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  exact ⟨u * t, hu, by rw [map_mul, mul_smul]; exact L.smul_mem _ h⟩

theorem exists_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V)
    (J : Ideal (𝓞 K)) {v : V} (hv : v ∈ J • locF 𝔭 L) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t • v ∈ J • L := by
  have := h𝔭.isPrime
  induction hv using Submodule.smul_induction_on' with
  | smul a ha w hw =>
    obtain ⟨t, ht, h⟩ := (mem_locF 𝔭 L w).1 hw
    exact ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul ha h⟩
  | add x _ y _ hx hy =>
    obtain ⟨t, ht, h1⟩ := hx
    obtain ⟨u, hu, h2⟩ := hy
    refine ⟨t * u, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht hu, ?_⟩
    rw [smul_add, map_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h1
    · rw [mul_smul]; exact Submodule.smul_mem _ _ h2

theorem mem_smul_of_mem_smul_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V)
    (k : ℕ) {y : V} (hy : y ∈ L) (h : y ∈ extP K 𝔭 ^ k • locF 𝔭 L) : y ∈ extP K 𝔭 ^ k • L := by
  obtain ⟨t, ht, h1⟩ := exists_smul_mem h𝔭 L _ h
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : y = ι u • (ι t • y) - ι (u * t - 1) • y := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem_smul (ι_mem_pow hu) hy)

def quotLocF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) :
    (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) ≃ₗ[𝓞 K]
      (↥(locF 𝔭 L) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 L))) :=
  have := h𝔭.isPrime
  LinearEquiv.ofBijective
    (Submodule.mapQ _ _ (Submodule.inclusion (le_locF 𝔭 L)) (by
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hy
      exact Submodule.smul_mono le_rfl (le_locF 𝔭 L) hy))
    (by
      constructor
      · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro x hx
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at hx
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
        exact mem_smul_of_mem_smul_locF h𝔭 L k y.2 hx
      · intro x
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨c, hc, h⟩ := exists_approx h𝔭 L k w.2
        refine ⟨Submodule.Quotient.mk ⟨_, h⟩, ?_⟩
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
        have : ((Submodule.inclusion (le_locF 𝔭 L) ⟨ι c • (w : V), h⟩ - w : ↥(locF 𝔭 L)) : V) =
            ι (c - 1) • (w : V) := by
          rw [map_sub, map_one, sub_smul, one_smul]; rfl
        rw [this]
        exact Submodule.smul_mem_smul (ι_mem_pow hc) w.2)

theorem quotLocF_mk {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) (y : ↥L)
    (hy : (y : V) ∈ locF 𝔭 L) :
    quotLocF h𝔭 L k (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨(y : V), hy⟩ := rfl

theorem star_ι (hF : IsFixF K F) (a : 𝓞 F) :
    star (algebraMap (𝓞 K) K (ι a)) = algebraMap (𝓞 K) K (ι a) :=
  MeanB.star_algebraMap hF _

theorem form_smul (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (a b : 𝓞 F) (x y : V) :
    h (ι a • x) (ι b • y) = algebraMap (𝓞 K) K (ι (a * b)) * h x y := by
  rw [← algebraMap_smul K (ι a), ← algebraMap_smul K (ι b), map_smul, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, starRingEnd_apply, star_ι hF, map_mul, map_mul]
  ring

theorem congrP_of_mul_left {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a b : K}
    (h : CongrP 𝔭 k (algebraMap (𝓞 K) K (ι t) * a) (algebraMap (𝓞 K) K (ι t) * b)) :
    CongrP 𝔭 k a b := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  refine ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, z, hz, ?_⟩
  rw [e, ← mul_sub, ← mul_assoc]
  congr 1
  simp [MeanB.algebraMap_comp]

theorem congrP_mul_left_of_sub_one_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} {c : 𝓞 F} (hc : c - 1 ∈ 𝔭 ^ k) {a : K} {n : 𝓞 F}
    (h : CongrP 𝔭 k a (algebraMap F K (n : F))) :
    CongrP 𝔭 k (algebraMap (𝓞 K) K (ι c) * a) (algebraMap F K (n : F)) := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  refine ⟨u, hu, ι c * z + ι (u * (c - 1) * n), ?_, ?_⟩
  · refine add_mem (Ideal.mul_mem_left _ _ hz) (ι_mem_pow ?_)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc)
  · rw [map_add, map_mul, e]
    simp only [MeanB.algebraMap_comp, map_mul, map_sub, map_one]
    ring

theorem nkCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) :
    nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n := by
  have := h𝔭.isPrime
  unfold nkCount
  symm
  refine Nat.card_congr ((quotLocF h𝔭 L k).toEquiv.subtypeEquiv fun x => ?_)
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨⟨y, le_locF 𝔭 L y.2⟩, rfl, hy⟩
  · rintro ⟨w, hw, hc⟩
    obtain ⟨c, hc1, hcL⟩ := exists_approx h𝔭 L k w.2
    refine ⟨⟨_, hcL⟩, ?_, ?_⟩
    · apply (quotLocF h𝔭 L k).injective
      rw [quotLocF_mk h𝔭 L k _ (le_locF 𝔭 L hcL)]
      refine Eq.trans ?_ hw
      rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
      have : (((⟨ι c • (w : V), le_locF 𝔭 L hcL⟩ : ↥(locF 𝔭 L)) - w : ↥(locF 𝔭 L)) : V) =
          ι (c - 1) • (w : V) := by
        rw [map_sub, map_one, sub_smul, one_smul]; rfl
      rw [this]
      exact Submodule.smul_mem_smul (ι_mem_pow hc1) w.2
    · show CongrP 𝔭 k (h (ι c • (w : V)) (ι c • (w : V))) _
      rw [form_smul hF]
      refine congrP_mul_left_of_sub_one_mem ?_ hc
      have : c * c - 1 = (c - 1) * (c + 1) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hc1

theorem exists_common {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) {ι' : Type*}
    [Finite ι'] (w : ι' → V) (hw : ∀ i, w i ∈ locF 𝔭 L) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ i, ι t • w i ∈ L := by
  classical
  have := h𝔭.isPrime
  have := Fintype.ofFinite ι'
  choose t ht h using fun i => (mem_locF 𝔭 L (w i)).1 (hw i)
  refine ⟨∏ i, t i, ?_, fun i => ?_⟩
  · intro hmem
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact ht i hi
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, map_mul, mul_smul]
    exact L.smul_mem _ (h i)

theorem akCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : akCount h (locF 𝔭 L) 𝔭 k = akCount h L 𝔭 k := by
  have := h𝔭.isPrime
  unfold akCount
  symm
  refine Nat.card_congr ((quotLocF h𝔭 L k).conj.toEquiv.subtypeEquiv fun X => ?_)
  have hconj : ∀ q, (quotLocF h𝔭 L k).conj X (quotLocF h𝔭 L k q) = quotLocF h𝔭 L k (X q) := by
    intro q
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  constructor
  · intro hX x y x' y' hx hy
    obtain ⟨t, ht, htL⟩ := exists_common h𝔭 L ![(x : V), y, x', y'] (by
      intro i; fin_cases i
      · exact x.2
      · exact y.2
      · exact x'.2
      · exact y'.2)
    have key : ∀ (u u' : ↥(locF 𝔭 L)) (hu : ι t • (u : V) ∈ L) (hu' : ι t • (u' : V) ∈ L),
        Submodule.Quotient.mk u' = (quotLocF h𝔭 L k).conj X (Submodule.Quotient.mk u) →
        (Submodule.Quotient.mk (⟨_, hu'⟩ : ↥L) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
          X (Submodule.Quotient.mk ⟨_, hu⟩) := by
      intro u u' hu hu' e
      apply (quotLocF h𝔭 L k).injective
      rw [← hconj, quotLocF_mk h𝔭 L k _ (le_locF 𝔭 L hu'), quotLocF_mk h𝔭 L k _ (le_locF 𝔭 L hu)]
      have e1 : ∀ (v : ↥(locF 𝔭 L)) (hv : ι t • (v : V) ∈ locF 𝔭 L),
          (Submodule.Quotient.mk (⟨_, hv⟩ : ↥(locF 𝔭 L)) :
            ↥(locF 𝔭 L) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 L))) =
            ι t • Submodule.Quotient.mk v := fun v hv => rfl
      rw [e1, e1, e, map_smul]
    have h1 := hX ⟨_, htL 0⟩ ⟨_, htL 1⟩ ⟨_, htL 2⟩ ⟨_, htL 3⟩ (key x x' (htL 0) (htL 2) hx)
      (key y y' (htL 1) (htL 3) hy)
    have h2 : CongrP 𝔭 k (h (ι t • (x' : V)) (ι t • (y' : V))) (h (ι t • (x : V)) (ι t • (y : V))) := h1
    rw [form_smul hF, form_smul hF] at h2
    exact congrP_of_mul_left h𝔭 (fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht ht) h2
  · intro hX x y x' y' hx hy
    refine hX ⟨x, le_locF 𝔭 L x.2⟩ ⟨y, le_locF 𝔭 L y.2⟩ ⟨x', le_locF 𝔭 L x'.2⟩ ⟨y', le_locF 𝔭 L y'.2⟩
      ?_ ?_
    · rw [← quotLocF_mk h𝔭 L k x', ← quotLocF_mk h𝔭 L k x, hx]
      exact (hconj _).symm
    · rw [← quotLocF_mk h𝔭 L k y', ← quotLocF_mk h𝔭 L k y, hy]
      exact (hconj _).symm

theorem vd_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h (locF 𝔭 L) 𝔭 = vd h L 𝔭 := by
  have := h𝔭.isPrime
  unfold vd
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hle
    refine le_trans (Ideal.span_mono ?_) hle
    rintro z ⟨x, hx, e⟩
    exact ⟨x, fun i => le_locF 𝔭 L (hx i), e⟩
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨t, ht, htL⟩ := exists_common h𝔭 L x hx
    have h1 : ι ((t * t) ^ finrank K V) * z ∈ discrIdeal h L := by
      apply Ideal.subset_span
      refine ⟨fun i => ι t • x i, htL, ?_⟩
      have : (Matrix.of fun i j => h (ι t • x i) (ι t • x j)) =
          algebraMap (𝓞 K) K (ι (t * t)) • (Matrix.of fun i j => h (x i) (x j)) := by
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
        exact form_smul hF h t t _ _
      rw [this, Matrix.det_smul, Fintype.card_fin, map_mul, ez, map_pow, map_pow]
    have h2 : (t * t) ^ finrank K V ∉ 𝔭 ^ (0 + 1) := by
      rw [zero_add, pow_one]
      intro hm
      exact (h𝔭.isPrime.mem_or_mem (h𝔭.isPrime.mem_of_pow_mem _ hm)).elim ht ht
    exact mem_of_mul_mem h𝔭 h2 (by rw [zero_add]; exact hle h1)

end Formalism.HermitianLattices.Ext.L3.localizedQuotients
