import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CntIOneOfNotMem

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

private lemma coe_conjO_eq_star (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

private lemma conjO_conjO_unimodular_class_representatives (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star, coe_conjO_eq_star, star_star]

private lemma mem_conjIdeal_iff' (P : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ conjO K r ∈ P := by
  have hS : {r : 𝓞 K | ∃ s ∈ P, algebraMap (𝓞 K) K r = star (algebraMap (𝓞 K) K s)} =
      ((P.comap (conjO K) : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    ext r
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_comap]
    constructor
    · rintro ⟨s, hs, h⟩
      have : conjO K r = s := by
        apply RingOfIntegers.ext
        rw [coe_conjO_eq_star]
        change star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K s
        rw [h, star_star]
      rwa [this]
    · intro h
      refine ⟨conjO K r, h, ?_⟩
      change (r : K) = star ((conjO K r : 𝓞 K) : K)
      rw [coe_conjO_eq_star, star_star]
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  rw [hS, Ideal.span_eq, Ideal.mem_comap]

private lemma conjO_algebraMap_of_fixed_field (hF : IsFixF K F) (x : 𝓞 F) :
    conjO K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star]
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (algebraMap (𝓞 F) F x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x)) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x)
  rw [h1]
  exact (hF _).mpr ⟨_, rfl⟩

private lemma exists_algebraMap_eq_of_conjO_eq (hF : IsFixF K F) (y : 𝓞 K) (hy : conjO K y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) a = y := by
  have h1 : star (y : K) = y := by rw [← coe_conjO_eq_star, hy]
  obtain ⟨f, hf⟩ := (hF _).mp h1
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (algebraMap F K).injective, hf]
    exact RingOfIntegers.isIntegral_coe y
  let a : 𝓞 F := ⟨f, (mem_integralClosure_iff ℤ F).mpr hint⟩
  refine ⟨a, RingOfIntegers.ext ?_⟩
  have h2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (algebraMap (𝓞 F) F a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = (y : K)
  rw [h2, ← hf]
  rfl

private lemma extP_comap_eq_inf_conjIdeal_of_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P ⊓ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply le_antisymm
  · unfold extP
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_comap, Ideal.mem_inf, mem_conjIdeal_iff', conjO_algebraMap_of_fixed_field hF]
    exact ⟨hx, hx⟩
  · intro x hx
    rw [Ideal.mem_inf, mem_conjIdeal_iff'] at hx
    obtain ⟨hxP, hxc⟩ := hx
    have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
    have htc : t = conjO K θ := RingOfIntegers.ext (by rw [coe_conjO_eq_star]; exact ht)
    subst htc
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_conjO_eq hF (x + conjO K x) (by rw [map_add, conjO_conjO_unimodular_class_representatives, add_comm])
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_conjO_eq hF (conjO K θ * x + θ * conjO K x)
      (by rw [map_add, map_mul, map_mul, conjO_conjO_unimodular_class_representatives, conjO_conjO_unimodular_class_representatives, add_comm])
    obtain ⟨g, hg⟩ := exists_algebraMap_eq_of_conjO_eq hF ((θ - conjO K θ) * (θ - conjO K θ))
      (by rw [map_mul, map_sub, conjO_conjO_unimodular_class_representatives]; ring)
    have ha𝔭 : a ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, ha]; exact P.add_mem hxP hxc
    have hb𝔭 : b ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, hb]; exact P.add_mem (P.mul_mem_left _ hxP) (P.mul_mem_left _ hxc)
    have hg𝔭 : g ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, hg]
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h <;> exact hθ h
    obtain ⟨e, i, hi, hei⟩ := h𝔭.exists_inv hg𝔭
    have hEI : algebraMap (𝓞 F) (𝓞 K) e * ((θ - conjO K θ) * (θ - conjO K θ)) +
        algebraMap (𝓞 F) (𝓞 K) i = 1 := by
      rw [← hg, ← map_mul, ← map_add, hei, map_one]
    have hx_eq : x = algebraMap (𝓞 F) (𝓞 K) e * (θ - conjO K θ) * θ * algebraMap (𝓞 F) (𝓞 K) a -
        algebraMap (𝓞 F) (𝓞 K) e * (θ - conjO K θ) * algebraMap (𝓞 F) (𝓞 K) b +
        algebraMap (𝓞 F) (𝓞 K) i * x := by
      rw [ha, hb]
      linear_combination (-x) * hEI
    have hmem : ∀ z ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)), algebraMap (𝓞 F) (𝓞 K) z ∈
        extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) := fun z hz => Ideal.mem_map_of_mem _ hz
    rw [hx_eq]
    exact Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hmem _ ha𝔭))
      (Ideal.mul_mem_left _ _ (hmem _ hb𝔭))) (Ideal.mul_mem_right _ _ (hmem _ hi))

theorem map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  rw [extP_comap_eq_inf_conjIdeal_of_isMaximal hK hF hP, hc, inf_idem]

theorem extP_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hle : ¬ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P := by
    intro h
    apply hc
    apply le_antisymm h
    intro r hr
    rw [mem_conjIdeal_iff']
    apply h
    rw [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
    exact hr
  have htop : P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = ⊤ := by
    by_contra h
    exact hle (le_sup_right.trans (hP.eq_of_le h le_sup_left).ge)
  rw [extP_comap_eq_inf_conjIdeal_of_isMaximal hK hF hP, Ideal.mul_eq_inf_of_coprime htop]

theorem etaF_eq (𝔭 : Ideal (𝓞 F)) : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
  unfold etaF
  split_ifs <;> simp

theorem one_lt_q {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  have h1 : Ideal.absNorm 𝔭 ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have : 1 < Ideal.absNorm 𝔭 := by omega
  exact_mod_cast this

theorem beta_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    0 < 1 - etaF K F 𝔭 ^ M * (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) := by
  have hq := one_lt_q h𝔭
  have hlt : (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) := zpow_pos (by linarith) _
  rcases etaF_eq (K := K) 𝔭 with h | h <;> rw [h]
  · rw [one_pow, one_mul]; linarith
  · rcases neg_one_pow_eq_or ℝ M with h' | h' <;> rw [h'] <;> linarith

theorem cnt_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    (cnt hF 𝔭 k M (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * M - 1) * k) *
      (1 - etaF K F 𝔭 ^ M * (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ))) := by
  classical
  have hinj : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h2 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx, map_zero]
    rw [map_eq_zero_iff _ (algebraMap F K).injective] at h2
    have : x = 0 := RingOfIntegers.ext (h2.trans (map_zero (algebraMap (𝓞 F) F)).symm)
    rw [this]
    exact 𝔭.zero_mem
  haveI := h𝔭
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hinj
  subst hPc
  have hq := one_lt_q h𝔭
  have hnP : ι n ∉ P := by rwa [Ideal.mem_comap] at hn
  have hfix : conjO K (ι n) = ι n := conjO_algebraMap_of_fixed_field hF n
  rw [cnt_eq_normRepCount]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hin := map_comap_eq_of_inert hK hF hP hc
    rw [hin, normRepCount_eq_eulerFac_inert hK hP hc M k hM hk _ hfix hnP]
    have hN := absNorm_comap_inert hK hF hP hc
    have hpr : ((P.comap ι).map ι).IsPrime := by
      have h3 := hin
      unfold extP at h3
      rw [h3]
      exact hP.isPrime
    have heta : etaF K F (P.comap ι) = -1 := by
      unfold etaF
      rw [if_pos hpr]
    unfold Formalism.HermitianLatticesTheory.eulerFac
    rw [if_pos hc, inv_inv, heta, ← hN]
    push_cast
    rw [Real.sqrt_sq (by positivity)]
  · have hsplit := extP_split hK hF hP hc
    rw [hsplit, normRepCount_eq_eulerFac_split hK hP hc M k hM hk _ hfix hnP]
    have hN := absNorm_comap_split hK hF hP hc
    have hcc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
      ext r
      rw [mem_conjIdeal_iff', mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
    have hc2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠
        Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      rw [hcc]
      exact Ne.symm hc
    have hNc := absNorm_conjIdeal hK P
    have hpr : ¬ ((P.comap ι).map ι).IsPrime := by
      intro hpr
      have h3 := hsplit
      unfold extP at h3
      rw [h3] at hpr
      rcases (hpr.mul_le).mp le_rfl with h | h
      · have h1 : P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := h.trans Ideal.mul_le_right
        apply hc
        refine le_antisymm ?_ h1
        intro r hr
        rw [mem_conjIdeal_iff'] at hr
        have h4 := h1 hr
        rwa [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives] at h4
      · have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P := h.trans Ideal.mul_le_left
        apply hc
        refine le_antisymm h1 ?_
        intro r hr
        rw [mem_conjIdeal_iff']
        apply h1
        rw [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
        exact hr
    have heta : etaF K F (P.comap ι) = 1 := by
      unfold etaF
      rw [if_neg hpr]
    have hx : 0 < 1 - (Ideal.absNorm (P.comap ι) : ℝ) ^ (-(M : ℤ)) := by
      have hlt : (Ideal.absNorm (P.comap ι) : ℝ) ^ (-(M : ℤ)) < 1 := by
        rw [zpow_neg, zpow_natCast]
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
      linarith
    have hh : (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 := by norm_num
    unfold Formalism.HermitianLatticesTheory.eulerFac
    rw [if_neg hc, if_neg hc2, hNc, ← hN, heta, ← Real.rpow_add hx, hh, Real.rpow_neg_one, inv_inv,
      one_pow, one_mul]

theorem exists_norm (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {u : 𝓞 F} (hu : u ∉ 𝔭) :
    ∃ c : 𝓞 K, conjO K c * c - ι u ∈ extP K 𝔭 ^ k := by
  have hq := one_lt_q h𝔭
  have h1 := cnt_unit hK hF h𝔭 (M := 1) le_rfl hk hu
  have h2 := beta_pos (K := K) h𝔭 (M := 1) le_rfl
  have hpos : (0 : ℝ) < (cnt hF 𝔭 k 1 (ι u) : ℝ) := by
    rw [h1]
    exact mul_pos (pow_pos (by linarith) _) h2
  have hpos' : 0 < normRepCount K (extP K 𝔭 ^ k) 1 (ι u) := by
    rw [← cnt_eq_normRepCount hF]
    exact_mod_cast hpos
  unfold normRepCount at hpos'
  obtain ⟨⟨x, y, hy, hsum⟩⟩ := (Nat.card_pos_iff.mp hpos').1
  refine ⟨y 0, ?_⟩
  rw [Fin.sum_univ_one] at hsum
  exact Ideal.Quotient.eq.mp hsum

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_frame (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (z : Fin (finrank K V) → ↥L) (g : Fin (finrank K V) → 𝓞 K),
      (∀ i j, i ≠ j → h (z i : V) (z j : V) = 0) ∧
      (∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) ∧ ∀ i, g i - 1 ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hPp := hP.isPrime
  have hda := LocF.aniso_of_totPosDef hd
  have hu := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  obtain ⟨x, hxM, hxo, hxu⟩ := LocF.exists_orth_unit_frame (WA.isHermSemilocal_locRing hK hP)
    (LocF.locRing_local hPp) hs hda (WA.isSelfDualMod_loc hL hPp hu)
  choose s hs' hsx using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
    (show x i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hxM i)
  choose u hu' using fun i => MeanB.exists_val hF hs hLi ⟨s i • x i, hsx i⟩
  have hunit : ∀ i, u i ∉ P.comap ι := by
    intro i
    have h1 : WA.IsUnitIn (WA.locRing P) (algebraMap (𝓞 K) K (ι (u i))) := by
      rw [MeanB.algebraMap_comp, ← hu' i]
      show WA.IsUnitIn (WA.locRing P) (h (s i • x i) (s i • x i))
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
      refine LocF.isUnitIn_mul ?_ (LocF.isUnitIn_mul ?_ (hxu i))
      · rw [← WA.algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact WA.conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    exact ((WA.mem_hcompl_iff hPp _).mp ((LocF.isUnitIn_algebraMap_iff hPp _).mp h1)).1
  choose u' hu'' using fun i => MeanA.exists_mul_sub_one_mem_pow h𝔭 (hunit i) k
  have hunit' : ∀ i, u' i ∉ P.comap ι := by
    intro i hmem
    have h1 : u' i * u i - 1 ∈ P.comap ι := Ideal.pow_le_self (by omega) (hu'' i)
    have h2 := sub_mem (Ideal.mul_mem_right (u i) _ hmem) h1
    rw [sub_sub_cancel] at h2
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  choose c hc using fun i => exists_norm hK hF h𝔭 hk (hunit' i)
  refine ⟨fun i => ⟨c i • s i • x i, L.smul_mem _ (hsx i)⟩, fun i => conjO K (c i) * c i * ι (u i),
    ?_, ?_, ?_⟩
  · intro i j hij
    show h (c i • s i • x i) (c j • s j • x j) = 0
    simp only [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hxo i j hij, mul_zero]
  · intro i
    show h (c i • s i • x i) (c i • s i • x i) = _
    have := hu' i
    simp only at this
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, this, map_mul, map_mul,
      WA.algebraMap_conjO, MeanB.algebraMap_comp]
    ring
  · intro i
    have e : conjO K (c i) * c i * ι (u i) - 1 =
        (conjO K (c i) * c i - ι (u' i)) * ι (u i) + ι (u' i * u i - 1) := by
      rw [map_sub, map_mul, map_one]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ (hc i)) ((idealPowerSpanBounds.mem_pow_iff _ _ _).2 (hu'' i))

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
