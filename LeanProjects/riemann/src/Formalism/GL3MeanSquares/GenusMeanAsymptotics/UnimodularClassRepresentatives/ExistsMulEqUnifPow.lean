import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace NO

abbrev zR (𝔭 : Ideal (𝓞 F)) (z : K) : AddSubgroup K :=
  (pK K 𝔭 0).toAddSubgroup.map (AddMonoidHom.mulLeft z)

theorem mem_zR {𝔭 : Ideal (𝓞 F)} {z a : K} : a ∈ zR 𝔭 z ↔ ∃ b ∈ pK K 𝔭 0, z * b = a := Iff.rfl

theorem mul_mem₀ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a b : K} (ha : a ∈ pK K 𝔭 k)
    (hb : b ∈ pK K 𝔭 0) : a * b ∈ pK K 𝔭 k := by
  have h := mul_mem_pK h𝔭 ha hb
  rwa [add_zero] at h

theorem zR_le {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K} (hz : z ∈ pK K 𝔭 0) :
    zR 𝔭 z ≤ (pK K 𝔭 0).toAddSubgroup := by
  rintro a ⟨b, hb, rfl⟩
  exact mul_mem₀ h𝔭 hz hb

theorem zR_mul (𝔭 : Ideal (𝓞 F)) (z w : K) :
    zR 𝔭 (z * w) = (zR 𝔭 w).map (AddMonoidHom.mulLeft z) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨w * b, ⟨b, hb, rfl⟩, (mul_assoc z w b).symm⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, mul_assoc z w b⟩

theorem algF_mem_pK {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap F K (s : F) ∈ pK K 𝔭 k := by
  refine (mem_pK h𝔭).2 ⟨1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h),
    algebraMap (𝓞 F) (𝓞 K) s, ?_, ?_⟩
  · rw [extP, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hs
  · rw [show ((1 : 𝓞 F) : F) = 1 from rfl, map_one, one_mul]
    rfl

theorem zR_unif_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2)
    (k : ℕ) : zR 𝔭 (algebraMap F K (π : F) ^ k) = (pK K 𝔭 k).toAddSubgroup := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, rfl⟩
  · intro ha
    obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 ha
    exact ⟨b, hb, e.symm⟩

theorem exists_sub_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {a : K} (ha : a ∈ pK K 𝔭 0) :
    ∃ z : 𝓞 K, a - algebraMap (𝓞 K) K z ∈ pK K 𝔭 k := by
  obtain ⟨t, ht, z, -, e⟩ := (mem_pK h𝔭).1 ha
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  refine ⟨algebraMap (𝓞 F) (𝓞 K) u * z, ?_⟩
  have h1 := mul_mem₀ h𝔭 (algF_mem_pK (K := K) h𝔭 hu) ha
  have h2 : a - algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u * z) =
      -(algebraMap F K ((u * t - 1 : 𝓞 F) : F) * a) := by
    rw [map_mul, e]
    have e1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = algebraMap F K (u : F) := rfl
    have e2 : ((u * t - 1 : 𝓞 F) : F) = (u : F) * (t : F) - 1 := by simp
    rw [e1, e2, map_sub, map_mul, map_one]
    ring
  rw [h2]
  exact (pK K 𝔭 k).neg_mem h1

theorem comap_pK {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    (pK K 𝔭 k).toAddSubgroup.comap (algebraMap (𝓞 K) K).toAddMonoidHom =
      (extP K 𝔭 ^ k).toAddSubgroup := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, w, hw, e⟩ := (mem_pK h𝔭).1 (show algebraMap (𝓞 K) K z ∈ pK K 𝔭 k from hz)
    obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
    have e1 : w = algebraMap (𝓞 F) (𝓞 K) t * z := by
      apply RingOfIntegers.ext
      exact e
    have e2 : z = algebraMap (𝓞 F) (𝓞 K) u * w - algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
      rw [e1, map_sub, map_mul, map_one]
      ring
    show z ∈ extP K 𝔭 ^ k
    rw [e2]
    refine sub_mem (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_right _ _ ?_)
    rw [extP, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hu
  · intro hz
    exact (mem_pK h𝔭).2 ⟨1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h), z, hz, by simp⟩

theorem relIndex_pK (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    (pK K 𝔭 k).toAddSubgroup.relIndex (pK K 𝔭 0).toAddSubgroup = Ideal.absNorm 𝔭 ^ (2 * k) := by
  have h1 : (algebraMap (𝓞 K) K).toAddMonoidHom.range ⊔ (pK K 𝔭 k).toAddSubgroup =
      (pK K 𝔭 0).toAddSubgroup := by
    apply le_antisymm
    · refine sup_le ?_ (pK_anti 𝔭 (Nat.zero_le k))
      rintro _ ⟨z, rfl⟩
      exact algebraMap_mem_pK 𝔭 z
    · intro a ha
      obtain ⟨z, hz⟩ := exists_sub_mem h𝔭 k ha
      rw [show a = algebraMap (𝓞 K) K z + (a - algebraMap (𝓞 K) K z) by ring]
      exact add_mem (AddSubgroup.mem_sup_left ⟨z, rfl⟩) (AddSubgroup.mem_sup_right hz)
  rw [← h1, AddSubgroup.relIndex_sup_right, ← AddSubgroup.index_comap, comap_pK h𝔭,
    ← Ideal.absNorm_eq_index, map_pow, idealPowerSpanBounds.absNorm_extP_eq_sq hK hF h𝔭, ← pow_mul]

end NO

open NO in
theorem nO_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z w : K} (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0)
    (hw : w ∈ pK K 𝔭 0) : nO 𝔭 (z * w) = nO 𝔭 z * nO 𝔭 w := by
  have h1 := AddSubgroup.relIndex_mul_relIndex ((zR 𝔭 w).map (AddMonoidHom.mulLeft z)) (zR 𝔭 z)
    (pK K 𝔭 0).toAddSubgroup (AddSubgroup.map_mono (zR_le h𝔭 hw)) (zR_le h𝔭 hz)
  have h2 : ((zR 𝔭 w).map (AddMonoidHom.mulLeft z)).relIndex (zR 𝔭 z) = nO 𝔭 w :=
    AddSubgroup.relIndex_map_map_of_injective _ _ (mul_right_injective₀ hz0)
  rw [h2, ← zR_mul] at h1
  rw [mul_comm (nO 𝔭 z)]
  exact h1.symm

open NO in
theorem nO_star (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (z : K) :
    nO 𝔭 (star z) = nO 𝔭 z := by
  have hs : ∀ a : K, star a ∈ pK K 𝔭 0 ↔ a ∈ pK K 𝔭 0 := fun a =>
    ⟨fun h => by simpa using star_mem_pK hF h𝔭 h, star_mem_pK hF h𝔭⟩
  have h1 : (pK K 𝔭 0).toAddSubgroup.map (starAddEquiv : K ≃+ K).toAddMonoidHom =
      (pK K 𝔭 0).toAddSubgroup := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact star_mem_pK hF h𝔭 hb
    · intro ha
      exact ⟨star a, star_mem_pK hF h𝔭 ha, star_star a⟩
  have h2 : (zR 𝔭 z).map (starAddEquiv : K ≃+ K).toAddMonoidHom = zR 𝔭 (star z) := by
    ext a
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨star b, star_mem_pK hF h𝔭 hb, (star_mul' z b).symm⟩
    · rintro ⟨b, hb, rfl⟩
      refine ⟨z * star b, ⟨star b, star_mem_pK hF h𝔭 hb, rfl⟩, ?_⟩
      show star (z * star b) = star z * b
      rw [star_mul', star_star]
  have h3 := AddSubgroup.relIndex_map_map_of_injective (zR 𝔭 z) (pK K 𝔭 0).toAddSubgroup
    (f := (starAddEquiv : K ≃+ K).toAddMonoidHom) (starAddEquiv : K ≃+ K).injective
  rw [h1, h2] at h3
  exact h3

open NO in
theorem nO_unit {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K} (hz : z ∈ pK K 𝔭 0)
    (hz' : z⁻¹ ∈ pK K 𝔭 0) (hz0 : z ≠ 0) : nO 𝔭 z = 1 := by
  have h1 : zR 𝔭 z = (pK K 𝔭 0).toAddSubgroup := by
    apply le_antisymm (zR_le h𝔭 hz)
    intro a ha
    exact ⟨z⁻¹ * a, mul_mem₀ h𝔭 hz' ha, mul_inv_cancel_left₀ hz0 a⟩
  show (zR 𝔭 z).relIndex _ = 1
  rw [h1, AddSubgroup.relIndex_self]

open NO in
theorem nO_unif_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) :
    nO 𝔭 (algebraMap F K (π : F) ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  show (zR 𝔭 _).relIndex _ = _
  rw [zR_unif_pow h𝔭 hπ hπ', relIndex_pK hK hF h𝔭]

namespace NO

theorem exists_mul_eq_unif_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) {z : K}
    (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0) :
    ∃ (m : ℕ) (w : K), w ∈ pK K 𝔭 0 ∧ z * w = algebraMap F K (π : F) ^ m := by
  obtain ⟨t, ht, z₀, -, e⟩ := (mem_pK h𝔭).1 hz
  have ht0 : (t : F) ≠ 0 := by
    intro h
    apply ht
    rw [show t = 0 from RingOfIntegers.ext h]
    exact 𝔭.zero_mem
  have hz₀ : z₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    rcases mul_eq_zero.1 e.symm with h | h
    · exact ht0 ((map_eq_zero _).1 h)
    · exact hz0 h
  set n : ℕ := Ideal.absNorm (Ideal.span {z₀}) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz₀
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {z₀}))
  have hc' : Ideal.span {(n : 𝓞 F)} ≠ (0 : Ideal (𝓞 F)) := by
    simpa using hn0
  have hun : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact h𝔭.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hun hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨s, hsb, hsp⟩ := SetLike.not_le_iff_exists.mp hnd
  set m := multiplicity 𝔭 (Ideal.span {(n : 𝓞 F)}) with hm
  have h1 : π ^ m * s ∈ Ideal.span {(n : 𝓞 F)} := by
    rw [hb]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ m) hsb
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
  have hs0 : (s : F) ≠ 0 := by
    intro h
    apply hsp
    rw [show s = 0 from RingOfIntegers.ext h]
    exact 𝔭.zero_mem
  have hs0' : algebraMap F K (s : F) ≠ 0 := (map_ne_zero _).2 hs0
  have hu' : algebraMap (𝓞 K) K u * algebraMap (𝓞 K) K z₀ = (n : K) := by
    rw [← map_mul, hu, map_natCast]
  have hr' : algebraMap F K (r : F) * (n : K) =
      algebraMap F K (π : F) ^ m * algebraMap F K (s : F) := by
    have := congrArg (fun x : 𝓞 F => algebraMap F K (x : F)) hr
    simpa using this
  refine ⟨m, (algebraMap F K (s : F))⁻¹ * (algebraMap F K (r : F) * algebraMap (𝓞 K) K u *
    algebraMap F K (t : F)), ?_, ?_⟩
  · refine (mem_pK h𝔭).2 ⟨s, hsp, algebraMap (𝓞 F) (𝓞 K) r * u * algebraMap (𝓞 F) (𝓞 K) t, by simp, ?_⟩
    rw [mul_inv_cancel_left₀ hs0', map_mul, map_mul]
    rfl
  · have : z * (algebraMap F K (r : F) * algebraMap (𝓞 K) K u * algebraMap F K (t : F)) =
        algebraMap F K (π : F) ^ m * algebraMap F K (s : F) := by
      rw [← hr', ← hu', e]
      ring
    rw [mul_left_comm, this, mul_left_comm, inv_mul_cancel₀ hs0', mul_one]

end NO

theorem nO_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K}
    (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0) : nO 𝔭 z ≠ 0 := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨m, w, hw, e⟩ := NO.exists_mul_eq_unif_pow h𝔭 hπ hz hz0
  have h1 := nO_mul h𝔭 hz hz0 hw
  rw [e, nO_unif_pow hK hF h𝔭 hπ hπ'] at h1
  intro h0
  rw [h0, zero_mul] at h1
  exact pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact idealPowerSpanBounds.ne_bot h𝔭) h1

def matL {κ : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (f g : κ → κ → K) : AddSubgroup (Matrix κ κ K) where
  carrier := {M | ∀ i j, ∃ w ∈ pK K 𝔭 k, f i j * M i j = g i j * w}
  zero_mem' := fun i j => ⟨0, (pK K 𝔭 k).zero_mem, by simp⟩
  add_mem' := by
    intro M N hM hN i j
    obtain ⟨w, hw, e⟩ := hM i j
    obtain ⟨w', hw', e'⟩ := hN i j
    exact ⟨w + w', (pK K 𝔭 k).add_mem hw hw', by rw [Matrix.add_apply, mul_add, mul_add, e, e']⟩
  neg_mem' := by
    intro M hM i j
    obtain ⟨w, hw, e⟩ := hM i j
    exact ⟨-w, (pK K 𝔭 k).neg_mem hw, by rw [Matrix.neg_apply, mul_neg, mul_neg, e]⟩

namespace NO

def scal (κ : Type) (𝔭 : Ideal (𝓞 F)) (a : K) :
    (κ × κ → (pK K 𝔭 0).toAddSubgroup) →+ Matrix κ κ K where
  toFun v := Matrix.of fun i j => a * (v (i, j) : K)
  map_zero' := by
    ext i j
    simp
  map_add' v w := by
    ext i j
    simp [mul_add]

theorem scal_apply {κ : Type} (𝔭 : Ideal (𝓞 F)) (a : K) (v : κ × κ → (pK K 𝔭 0).toAddSubgroup)
    (i j : κ) : scal κ 𝔭 a v i j = a * (v (i, j) : K) := rfl

theorem range_scal {κ : Type} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) :
    (scal κ 𝔭 (algebraMap F K (π : F) ^ k)).range = matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1) := by
  ext M
  constructor
  · rintro ⟨v, rfl⟩ i j
    exact ⟨_, (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨_, (v (i, j)).2, rfl⟩, rfl⟩
  · intro hM
    have h1 : ∀ p : κ × κ, ∃ b ∈ pK K 𝔭 0, M p.1 p.2 = algebraMap F K (π : F) ^ k * b := by
      intro p
      obtain ⟨w, hw, e⟩ := hM p.1 p.2
      rw [one_mul, one_mul] at e
      rw [e]
      exact (mem_pK_iff_unif h𝔭 hπ hπ').1 hw
    choose b hb e using h1
    refine ⟨fun p => ⟨b p, hb p⟩, ?_⟩
    ext i j
    exact (e (i, j)).symm

theorem comap_scal {κ : Type} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (hπ0 : algebraMap F K (π : F) ≠ 0) (k c : ℕ) (f g d : κ → κ → K)
    (hf : ∀ i j, f i j ≠ 0)
    (hd : ∀ i j, f i j * d i j = g i j * algebraMap F K (π : F) ^ c) :
    (matL 𝔭 (k + c) f g).comap (scal κ 𝔭 (algebraMap F K (π : F) ^ k)) =
      AddSubgroup.pi Set.univ
        (fun p : κ × κ => (zR 𝔭 (d p.1 p.2)).addSubgroupOf (pK K 𝔭 0).toAddSubgroup) := by
  ext v
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  constructor
  · rintro hv ⟨i, j⟩ -
    obtain ⟨w, hw, e⟩ := hv i j
    obtain ⟨b, hb, rfl⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 hw
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨b, hb, ?_⟩
    show d i j * b = (v (i, j) : K)
    rw [scal_apply] at e
    apply mul_left_cancel₀ (mul_ne_zero (hf i j) (pow_ne_zero k hπ0))
    calc f i j * algebraMap F K (π : F) ^ k * (d i j * b)
        = (f i j * d i j) * (algebraMap F K (π : F) ^ k * b) := by ring
      _ = g i j * (algebraMap F K (π : F) ^ (k + c) * b) := by rw [hd, pow_add]; ring
      _ = f i j * algebraMap F K (π : F) ^ k * (v (i, j) : K) := by rw [← e]; ring
  · intro hv i j
    obtain ⟨b, hb, e⟩ := AddSubgroup.mem_addSubgroupOf.1 (hv (i, j) (Set.mem_univ _))
    replace e : d i j * b = (v (i, j) : K) := e
    refine ⟨algebraMap F K (π : F) ^ (k + c) * b, (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, rfl⟩, ?_⟩
    rw [scal_apply, ← e]
    calc f i j * (algebraMap F K (π : F) ^ k * (d i j * b))
        = (f i j * d i j) * (algebraMap F K (π : F) ^ k * b) := by ring
      _ = g i j * (algebraMap F K (π : F) ^ (k + c) * b) := by rw [hd, pow_add]; ring

end NO

open NO in
theorem relIndex_matL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {κ : Type} [Fintype κ] (f g : κ → κ → K) (hf : ∀ i j, f i j ∈ pK K 𝔭 0 ∧ f i j ≠ 0)
    (hg : ∀ i j, g i j ∈ pK K 𝔭 0 ∧ g i j ≠ 0) (k c : ℕ)
    (hle : matL 𝔭 (k + c) f g ≤ matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) :
    (matL 𝔭 (k + c) f g).relIndex (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) *
        ∏ i, ∏ j, nO 𝔭 (f i j) =
      (∏ i, ∏ j, nO 𝔭 (g i j)) * Ideal.absNorm 𝔭 ^ (2 * Fintype.card κ ^ 2 * c) := by
  classical
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    intro h
    apply hπ'
    rw [show π = 0 from RingOfIntegers.ext h]
    exact (𝔭 ^ 2).zero_mem
  set ϖ : K := algebraMap F K (π : F) with hϖ
  have hϖc : ϖ ^ c ∈ pK K 𝔭 0 :=
    pK_anti 𝔭 (Nat.zero_le c) ((mem_pK_iff_unif h𝔭 hπ hπ').2
      ⟨1, by simpa using algebraMap_mem_pK (K := K) 𝔭 1, (mul_one _).symm⟩)
  let d : κ → κ → K := fun i j => (f i j)⁻¹ * (g i j * ϖ ^ c)
  have hfd : ∀ i j, f i j * d i j = g i j * ϖ ^ c := fun i j =>
    mul_inv_cancel_left₀ (hf i j).2 _
  have hd : ∀ i j, d i j ∈ pK K 𝔭 0 := by
    intro i j
    have h1 : Matrix.single i j (ϖ ^ k * d i j) ∈ matL 𝔭 (k + c) f g := by
      intro i' j'
      by_cases h : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := h
        refine ⟨ϖ ^ (k + c) * 1, (mem_pK_iff_unif h𝔭 hπ hπ').2
          ⟨1, by simpa using algebraMap_mem_pK (K := K) 𝔭 1, rfl⟩, ?_⟩
        rw [Matrix.single_apply_same, mul_left_comm, hfd, pow_add]
        ring
      · refine ⟨0, (pK K 𝔭 (k + c)).zero_mem, ?_⟩
        rw [Matrix.single_apply, if_neg h, mul_zero, mul_zero]
    obtain ⟨w, hw, e⟩ := hle h1 i j
    rw [one_mul, one_mul, Matrix.single_apply_same] at e
    obtain ⟨b, hb, rfl⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 hw
    rw [mul_left_cancel₀ (pow_ne_zero k hπ0) e]
    exact hb
  have hn : ∀ i j, nO 𝔭 (d i j) * nO 𝔭 (f i j) = nO 𝔭 (g i j) * Ideal.absNorm 𝔭 ^ (2 * c) := by
    intro i j
    rw [mul_comm, ← nO_mul h𝔭 (hf i j).1 (hf i j).2 (hd i j), hfd,
      nO_mul h𝔭 (hg i j).1 (hg i j).2 hϖc, nO_unif_pow hK hF h𝔭 hπ hπ']
  have h1 : (matL 𝔭 (k + c) f g).relIndex (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) =
      ∏ i, ∏ j, nO 𝔭 (d i j) := by
    rw [← range_scal h𝔭 hπ hπ' k, ← AddSubgroup.index_comap,
      comap_scal h𝔭 hπ hπ' hπ0 k c f g d (fun i j => (hf i j).2) hfd, AddSubgroup.index_pi,
      Fintype.prod_prod_type]
    rfl
  rw [h1]
  simp_rw [← Finset.prod_mul_distrib, hn, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← pow_mul]
  congr 2
  ring

end Formalism.HermitianLattices.Ext.L3.D2
