import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulEqUnifPow

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem exists_dvd_mul {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R} (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) {x y : R} {v : ℕ} (hx : x ∈ P ^ v) (hy : y ∉ P ^ (v + 1)) :
    ∃ t, t ∉ P ∧ y ∣ t * x := by
  have hprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hy0 : Ideal.span {y} ≠ 0 := by
    intro h0
    apply hy
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h0
    rw [h0]
    exact zero_mem _
  obtain ⟨c, J, hJ, e⟩ := WfDvdMonoid.max_power_factor hy0 hprime.irreducible
  have hc : c ≤ v := by
    by_contra hlt
    rw [not_le] at hlt
    apply hy
    have : y ∈ P ^ c * J := e ▸ Ideal.mem_span_singleton_self y
    exact Ideal.pow_le_pow_right hlt (Ideal.mul_le_left this)
  rw [Ideal.dvd_iff_le] at hJ
  obtain ⟨t, htJ, ht⟩ := SetLike.not_le_iff_exists.1 hJ
  refine ⟨t, ht, ?_⟩
  rw [← Ideal.mem_span_singleton, e, mul_comm t x]
  exact Ideal.mul_mem_mul (Ideal.pow_le_pow_right hc hx) htJ

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration in

theorem exists_gram_det (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (b : Basis (Fin (finrank K V)) K V) (hbL : ∀ i, b i ∈ L)
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (Matrix.of fun i j => h (b i) (b j)).det = algebraMap (𝓞 K) K (ι D) ∧
      vd h L 𝔭 = vF 𝔭 D := by
  obtain ⟨H, hH, hdet⟩ := LocF.exists_gram hLi b hbL
  have hHH : H.conjTranspose = H := by
    ext i j
    show algebraMap (𝓞 K) K (star (H j i)) = algebraMap (𝓞 K) K (H i j)
    rw [hH, star_def]
    show star (algebraMap (𝓞 K) K (H j i)) = _
    rw [hH]
    exact hs.eq _ _
  obtain ⟨D, hD⟩ := (conjO_eq_iff_mem_range hF H.det).1 (by
    rw [← star_def, ← Matrix.det_conjTranspose, hHH])
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent
    rw [← hdet, ← hD, map_zero, map_zero]
  refine ⟨D, hD0, by rw [← hdet, hD], ?_⟩
  rw [← localizedQuotients.vd_locF hF h L h𝔭, ← hb, localizedQuotients.vd_locF hF h _ h𝔭]
  unfold vd vF
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [← mem_pow_iff (K := K), hD]
  constructor
  · intro hle
    exact hle (Ideal.subset_span ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, hdet⟩)
  · intro hmem
    refine BallB.discrIdeal_le b fun x hx z hz => ?_
    have hx' : b.det x = algebraMap (𝓞 K) K (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det := by
      rw [Basis.det_apply, RingHom.map_det]
      congr 1
      ext i j
      exact repr_coe b ⟨x j, hx j⟩ i
    have : z = star (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det * H.det *
        (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det := by
      apply RingOfIntegers.coe_injective
      rw [hz, hx', BallB.gdet, ← hdet]
      rfl
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)

theorem coe_ι (x : 𝓞 F) : algebraMap F K (x : F) = algebraMap (𝓞 K) K (ι x) := rfl

theorem cι_ne_zero {x : 𝓞 F} (hx : x ≠ 0) : algebraMap (𝓞 K) K (ι x) ≠ 0 := by
  intro e
  apply hx
  apply idealPowerSpanBounds.ι_inj (K := K)
  apply RingOfIntegers.coe_injective
  rw [map_zero]
  exact e

theorem mem_pK_zero_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {x : K}
    {z : 𝓞 K} (e : algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K (ι t) * x) : x ∈ pK K 𝔭 0 :=
  (mem_pK h𝔭).2 ⟨t, ht, z, by rw [pow_zero, Ideal.one_eq_top]; trivial, e⟩

theorem unit_of_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : 𝓞 F} (hs𝔭 : s ∉ 𝔭) :
    algebraMap (𝓞 K) K (ι s) ∈ pK K 𝔭 0 ∧ (algebraMap (𝓞 K) K (ι s))⁻¹ ∈ pK K 𝔭 0 ∧
      algebraMap (𝓞 K) K (ι s) ≠ 0 := by
  have hs0 : s ≠ 0 := fun h0 => hs𝔭 (h0 ▸ zero_mem _)
  have h0 := cι_ne_zero (K := K) hs0
  refine ⟨algebraMap_mem_pK 𝔭 (ι s), ?_, h0⟩
  refine mem_pK_zero_of_mul h𝔭 hs𝔭 (z := 1) ?_
  rw [map_one, mul_inv_cancel₀ h0]

theorem exists_unit_factor {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) {D : 𝓞 F} (hD0 : D ≠ 0) :
    ∃ w : K, w ∈ pK K 𝔭 0 ∧ w⁻¹ ∈ pK K 𝔭 0 ∧ w ≠ 0 ∧
      algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D * w := by
  have hpr := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := idealPowerSpanBounds.ne_bot h𝔭
  have hπ0 : π ≠ 0 := fun h0 => hπ' (h0 ▸ zero_mem _)
  have hDv : algebraMap (𝓞 K) K (ι D) ∈ pK K 𝔭 (vF 𝔭 D) :=
    (mem_pK h𝔭).2 ⟨1, fun h1 => hpr.ne_top ((Ideal.eq_top_iff_one _).2 h1), ι D,
      (idealPowerSpanBounds.mem_pow_iff 𝔭 _ D).2 (localValuationFiltration.mem_pow_vF h𝔭 hD0), by
        rw [coe_ι, map_one, map_one, one_mul]⟩
  obtain ⟨w, hw, ew⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 hDv
  rw [coe_ι] at ew
  obtain ⟨t1, ht1, r1, er1⟩ := exists_dvd_mul hpr hp0 (Ideal.pow_mem_pow hπ (vF 𝔭 D))
    (localValuationFiltration.notMem_pow_vF h𝔭 hD0)
  have hP0 : algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D ≠ 0 := pow_ne_zero _ (cι_ne_zero hπ0)
  have hDK0 := cι_ne_zero (K := K) hD0
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ew
    exact hDK0 ew
  have er1' : algebraMap (𝓞 K) K (ι t1) * algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D =
      algebraMap (𝓞 K) K (ι D) * algebraMap (𝓞 K) K (ι r1) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_pow, ← map_mul, ← map_mul, er1]
  refine ⟨w, hw, ?_, hw0, ew⟩
  refine mem_pK_zero_of_mul h𝔭 ht1 (z := ι r1) ?_
  rw [ew] at er1'
  have h2 : algebraMap (𝓞 K) K (ι t1) = w * algebraMap (𝓞 K) K (ι r1) :=
    mul_left_cancel₀ hP0 (by linear_combination er1')
  rw [h2, mul_comm w, mul_assoc, mul_inv_cancel₀ hw0, mul_one]

theorem mul_mem_prime_power {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a b : K} (ha : a ∈ pK K 𝔭 0)
    (hb : b ∈ pK K 𝔭 0) : a * b ∈ pK K 𝔭 0 := by
  have := mul_mem_pK h𝔭 ha hb
  rwa [add_zero] at this

theorem nO_of_rel (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {D s : 𝓞 F} (hD0 : D ≠ 0) (hs𝔭 : s ∉ 𝔭) {G : K}
    (hrel : algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι s) * G) :
    G ∈ pK K 𝔭 0 ∧ G ≠ 0 ∧ nO 𝔭 G = Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 D) := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 : π ≠ 0 := fun h0 => hπ' (h0 ▸ zero_mem _)
  obtain ⟨w, hw, hwi, hw0, ew⟩ := exists_unit_factor (K := K) h𝔭 hπ hπ' hD0
  obtain ⟨hsm, hsi, hsK0⟩ := unit_of_notMem (K := K) h𝔭 hs𝔭
  have hP0 : algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D ≠ 0 := pow_ne_zero _ (cι_ne_zero hπ0)
  have hPm : algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D ∈ pK K 𝔭 0 := by
    rw [← map_pow]
    exact algebraMap_mem_pK 𝔭 _
  obtain ⟨u, hu⟩ : ∃ u, u = (algebraMap (𝓞 K) K (ι s))⁻¹ * w := ⟨_, rfl⟩
  have hum : u ∈ pK K 𝔭 0 := by
    rw [hu]
    exact mul_mem_prime_power h𝔭 hsi hw
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (inv_ne_zero hsK0) hw0
  have hui : u⁻¹ ∈ pK K 𝔭 0 := by
    rw [hu, mul_inv, inv_inv]
    exact mul_mem_prime_power h𝔭 hsm hwi
  have hGu : G = algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D * u := by
    rw [hu]
    rw [ew] at hrel
    apply mul_left_cancel₀ hsK0
    rw [← hrel, mul_left_comm, ← mul_assoc (algebraMap (𝓞 K) K (ι s)), mul_inv_cancel₀ hsK0, one_mul]
  have hn := nO_unif_pow hK hF h𝔭 hπ hπ' (vF 𝔭 D)
  rw [coe_ι] at hn
  rw [hGu]
  refine ⟨mul_mem_prime_power h𝔭 hPm hum, mul_ne_zero hP0 hu0, ?_⟩
  rw [nO_mul h𝔭 hPm hP0 hum, hn, nO_unit h𝔭 hum hui hu0, mul_one]

theorem nO_gram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Basis (Fin (finrank K V)) K V)
    (ha : locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀) :
    (Matrix.of fun i j => h (a i) (a j)).det ∈ pK K 𝔭 0 ∧
      (Matrix.of fun i j => h (a i) (a j)).det ≠ 0 ∧
      nO 𝔭 (Matrix.of fun i j => h (a i) (a j)).det =
        Ideal.absNorm 𝔭 ^ (2 * vd h (locF 𝔭 A₀) 𝔭) := by
  classical
  have hpr := h𝔭.isPrime
  have haL : ∀ i, a i ∈ locF 𝔭 A₀ := fun i =>
    ha ▸ LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨t, ht, htL⟩ := localizedQuotients.exists_common h𝔭 A₀ a haL
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ zero_mem _)
  have hτ0 : algebraMap (𝓞 K) K (ι t) ≠ 0 := cι_ne_zero ht0
  obtain ⟨b, hbi⟩ : ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, b i = ι t • a i :=
    ⟨a.isUnitSMul (w := fun _ => algebraMap (𝓞 K) K (ι t)) (fun _ => hτ0.isUnit), fun i => by
      rw [Basis.isUnitSMul_apply, algebraMap_smul]⟩
  have hbL : ∀ i, b i ∈ A₀ := fun i => by rw [hbi]; exact htL i
  have hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 A₀ := by
    rw [← ha]
    apply le_antisymm
    · apply LocF.locF_mono
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hbi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [← LocF.locF_idem 𝔭 (Submodule.span (𝓞 K) (Set.range b))]
      apply LocF.locF_mono
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t, ht, by rw [← hbi]; exact Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨D, hD0, hdet, hv⟩ := exists_gram_det hF hs hd hA₀i h𝔭 b hbL hb
  have hs𝔭 : (t * t) ^ finrank K V ∉ 𝔭 := fun hm =>
    (hpr.mem_or_mem (hpr.mem_of_pow_mem _ hm)).elim ht ht
  have hrel : algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι ((t * t) ^ finrank K V)) *
      (Matrix.of fun i j => h (a i) (a j)).det := by
    have : (Matrix.of fun i j => h (b i) (b j)) =
        algebraMap (𝓞 K) K (ι (t * t)) • (Matrix.of fun i j => h (a i) (a j)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hbi, hbi]
      exact localizedQuotients.form_smul hF h t t _ _
    rw [← hdet, this, Matrix.det_smul, Fintype.card_fin, map_pow, map_pow]
  rw [localizedQuotients.vd_locF hF h A₀ h𝔭, hv]
  exact nO_of_rel hK hF h𝔭 hD0 hs𝔭 hrel

end Formalism.HermitianLattices.Ext.L3.D2
