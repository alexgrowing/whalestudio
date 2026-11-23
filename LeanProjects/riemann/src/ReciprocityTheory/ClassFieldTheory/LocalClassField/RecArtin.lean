import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Existence
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_artin_hom (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a →
    ∀ L, IsAbLK p K L → IsRecip p K L a g := by
  classical
  let γ : IntermediateField ℚ_[p] (PadicAlgCl p) → Kˣ → GK p K := fun L a =>
    if h : IsAbLK p K L then (exists_isRecip h a).choose else 1
  have hγ : ∀ L, IsAbLK p K L → ∀ a, IsRecip p K L a (γ L a) := by
    intro L hL a
    simp only [γ, dif_pos hL]
    exact (exists_isRecip hL a).choose_spec
  obtain ⟨f, hf⟩ := exists_hom_GKab hK γ
    (fun L hL a b => IsRecip.unique hL (hγ L hL (a * b)) ((hγ L hL a).mul (hγ L hL b)))
    (fun L L' hL hL' hle a => IsRecip.unique hL (hγ L hL a) ((hγ L' hL' a).of_le hle))
  exact ⟨f, fun a g hg L hL => (hγ L hL a).congr (hf L hL a g hg)⟩

theorem isFrob_of_forall_Kn (hK : FiniteDimensional ℚ_[p] K) (g : GK p K)
    (h : ∀ n, 0 < n → (frobK p K)⁻¹ * g ∈ subG p K (Kn p K n)) : IsFrob p K g := by
  rw [isFrob_iff hK]
  intro ζ m hm hζ
  obtain ⟨n, hn, hζn⟩ := (mem_Kur_iff hK ζ).1 (mem_Kur_of_pow hK hm hζ)
  have h1 : frobK p K ζ = g ζ :=
    (mk_eq_mk_iff (M := Kn p K n) (frobK p K) g).1 (QuotientGroup.eq.2 (h n hn)) ζ hζn
  rw [← h1]
  exact (isFrob_iff hK _).1 (isFrob_frobK hK) ζ m hm hζ

theorem isFrob_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (g : GK p K)
    (h : ∀ L, IsAbLK p K L → IsRecip p K L π g) : IsFrob p K g :=
  isFrob_of_forall_Kn hK g fun _ hn =>
    IsRecip.unique (isAbLK_Kn hK hn) (isRecip_uniformiser_Kn hK hn π hπ) (h _ (isAbLK_Kn hK hn))

theorem IsRecip.inv_mul_mem (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a b : Kˣ} {g g' : GK p K}
    (h : IsRecip p K L a g) (h' : IsRecip p K L b g') : g⁻¹ * g' ∈ subG p K L ↔ a⁻¹ * b ∈ normGrp p K L := by
  obtain ⟨k, hk⟩ := exists_isRecip hL (a⁻¹ * b)
  have h1 : IsRecip p K L b (g * k) := by
    have := h.mul hk
    rwa [mul_inv_cancel_left] at this
  have h2 : (g * k)⁻¹ * g' ∈ subG p K L := IsRecip.unique hL h1 h'
  rw [← hk.mem_subG_iff hK hL]
  have h3 : g⁻¹ * g' = k * ((g * k)⁻¹ * g') := by group
  rw [h3]
  exact Subgroup.mul_mem_cancel_right _ h2

theorem isArtinK_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (Art : Kˣ →* GKab p K)
    (h : ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a → ∀ L, IsAbLK p K L → IsRecip p K L a g) :
    IsArtinK p K Art := by
  have hsurj : ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧
      g'⁻¹ * g ∈ subG p K L := by
    intro L hL g
    obtain ⟨a, ha⟩ := exists_isRecip_of_gal hK hL g
    obtain ⟨g', hg'⟩ := toAbK_surjective (Art a)
    exact ⟨a, g', hg', IsRecip.unique hL (h a g' hg' L hL) ha⟩
  refine ⟨?_, ?_, (denseRange_GKab_iff hK Art).2 hsurj, ?_, fun L hL => ⟨hsurj L hL, ?_⟩⟩
  · rw [continuous_GKab_iff hK]
    intro L hL x
    have hopen : IsOpen ((fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ)) :=
      (isOpen_normGrp hK hL.fin hL.le).preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ) := by
      show x⁻¹ * x ∈ normGrp p K L
      rw [inv_mul_cancel]; exact one_mem _
    filter_upwards [hopen.mem_nhds hx] with y hy g g' hg hg'
    exact (IsRecip.inv_mul_mem hK hL (h x g hg L hL) (h y g' hg' L hL)).2 hy
  · rw [injective_iff_map_eq_one]
    intro a ha
    refine eq_one_of_forall_mem_normGrp hK a fun L hL => ?_
    have h1 : toAbK p K 1 = Art a := by rw [map_one, ha]
    exact ((h a 1 h1 L hL).mem_subG_iff hK hL).1 (one_mem _)
  · intro π hπ g hg
    exact isFrob_of_isRecip hK π hπ g (h π g hg)
  · intro x g hg
    exact (h x g hg L hL).mem_subG_iff hK hL

theorem exists_isArtinK (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, IsArtinK p K Art := by
  obtain ⟨Art, h⟩ := exists_artin_hom hK
  exact ⟨Art, isArtinK_of_isRecip hK Art h⟩

theorem isRecip_Kn_zpow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (a : Kˣ) :
    IsRecip p K (Kn p K n) a (frobK p K ^ vK p K a) := by
  intro χ hχ
  rw [pairK_unr hK a χ (hχ.of_le (Kn_le_Kur hn)), ofMul_zpow, map_zsmul]

theorem dvd_vK_of_mem_normGrp_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (a : Kˣ)
    (ha : a ∈ normGrp p K (Kn p K n)) : (n : ℤ) ∣ vK p K a := by
  have hab := isAbLK_Kn hK hn
  have := hab.normal
  have h1 : frobK p K ^ vK p K a ∈ subG p K (Kn p K n) := ((isRecip_Kn_zpow hK hn a).mem_subG_iff hK hab).2 ha
  have h2 : frobLK p K (Kn p K n) ^ vK p K a = 1 := (QuotientGroup.eq_one_iff _).2 h1
  rw [← orderOf_frobLK_Kn hK hn]
  exact orderOf_dvd_iff_zpow_eq_one.2 h2

theorem exists_le_sup_Kn (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (π : Kˣ) (hπ : vK p K π = 1) :
    ∃ (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ), IsAbLK p K L' ∧ 0 < n ∧ π ∈ normGrp p K L' ∧
      L ≤ L' ⊔ Kn p K n := by
  let φ : Kˣ →* Kˣ := MonoidHom.mk' (fun x => x * (π ^ vK p K x)⁻¹) fun x y => by
    rw [vK_mul, zpow_add, mul_inv, mul_mul_mul_comm]
  have hfi : (normGrp p K L).FiniteIndex := finiteIndex_normGrp hK hL.fin hL.le
  obtain ⟨L', hL', hN⟩ := existence hK ((normGrp p K L).comap φ)
    ⟨by rw [Subgroup.index_comap]
        exact ne_zero_of_dvd_ne_zero hfi.index_ne_zero (Subgroup.relIndex_dvd_index_of_normal _ _)⟩
  have hn : 0 < degLK p K L := degLK_pos hL.fin
  refine ⟨L', degLK p K L, hL', hn, ?_, ?_⟩
  · rw [hN, Subgroup.mem_comap]
    show π * (π ^ vK p K π)⁻¹ ∈ normGrp p K L
    rw [hπ, zpow_one, mul_inv_cancel]
    exact one_mem _
  · rw [← normGrp_le_iff hK hL (hL'.sup (isAbLK_Kn hK hn)), normGrp_sup hK hL' (isAbLK_Kn hK hn), hN]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨k, hk⟩ := dvd_vK_of_mem_normGrp_Kn hK hn x hx2
    have h1 : x * (π ^ vK p K x)⁻¹ ∈ normGrp p K L := hx1
    have h2 : π ^ vK p K x ∈ normGrp p K L := by
      rw [hk, zpow_mul, zpow_natCast]
      exact zpow_mem (pow_degLK_mem_normGrp hL.le π) k
    have h3 := mul_mem h1 h2
    rwa [inv_mul_cancel_right] at h3

theorem IsArtinK.eq_on_uniformiser (hK : FiniteDimensional ℚ_[p] K) {Art Art' : Kˣ →* GKab p K} (hA : IsArtinK p K Art)
    (hA' : IsArtinK p K Art') (π : Kˣ) (hπ : vK p K π = 1) : Art π = Art' π := by
  obtain ⟨g, hg⟩ := toAbK_surjective (Art π)
  obtain ⟨g', hg'⟩ := toAbK_surjective (Art' π)
  rw [← hg, ← hg', toAbK_eq_iff hK]
  intro L hL
  obtain ⟨L', n, hL', hn, hπL', hle⟩ := exists_le_sup_Kn hK hL π hπ
  refine subG_anti hle ?_
  rw [subG_sup_eq_inf]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact mul_mem (inv_mem (((hA.2.2.2.2 L' hL').2 π g hg).2 hπL')) (((hA'.2.2.2.2 L' hL').2 π g' hg').2 hπL')
  · refine subG_anti (Kn_le_Kur hn) ?_
    rw [← QuotientGroup.eq, (hA.2.2.2.1 π hπ g hg).mk_eq hK, (hA'.2.2.2.1 π hπ g' hg').mk_eq hK]

theorem IsArtinK.unique (hK : FiniteDimensional ℚ_[p] K) {Art Art' : Kˣ →* GKab p K} (hA : IsArtinK p K Art)
    (hA' : IsArtinK p K Art') : Art = Art' := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have h0 := hA.eq_on_uniformiser hK hA' π hπ
  have hu : ∀ u : Kˣ, vK p K u = 0 → Art u = Art' u := by
    intro u hu
    have h1 := hA.eq_on_uniformiser hK hA' (π * u) (by rw [vK_mul, hπ, hu, add_zero])
    rw [map_mul, map_mul, h0] at h1
    exact mul_left_cancel h1
  ext a
  have h1 := hu ((π ^ vK p K a)⁻¹ * a) (by rw [vK_mul, vK_inv, vK_zpow, hπ]; ring)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h0] at h1
  exact mul_left_cancel h1

end ReciprocityTheory.DiscreteGroups.LocalClassField
