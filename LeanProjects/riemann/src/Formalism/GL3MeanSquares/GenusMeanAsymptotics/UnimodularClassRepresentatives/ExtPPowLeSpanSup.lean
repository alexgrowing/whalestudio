import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

section DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}

theorem pow_le_span_sup (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c : ℕ} (hg : g ∉ P ^ (c + 1)) (N : ℕ) :
    P ^ c ≤ Ideal.span {g} ⊔ P ^ N := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : Ideal.span {g} ⊔ P ^ N ∣ P ^ N := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr N).mp hdvd
  rw [associated_iff_eq] at hm
  have hgm : g ∈ P ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self g)
  have hmc : m ≤ c := by
    by_contra h
    exact hg (Ideal.pow_le_pow_right (by omega) hgm)
  rw [hm]
  exact Ideal.pow_le_pow_right hmc

private theorem not_pow_dvd_mul_of_not_pow_dvd_of_not_pow_dvd (hpr : Prime P) (i : ℕ) :
    ∀ (j : ℕ) (A B : Ideal R), ¬ P ^ (i + 1) ∣ A → ¬ P ^ (j + 1) ∣ B →
      ¬ P ^ (i + j + 1) ∣ A * B := by
  induction i with
  | zero =>
    intro j A B hA hB h
    apply hB
    have hA' : ¬ P ∣ A := by simpa using hA
    have h' : P ^ (j + 1) ∣ A * B := by simpa using h
    exact hpr.pow_dvd_of_dvd_mul_left (j + 1) hA' h'
  | succ i ih =>
    intro j A B hA hB h
    by_cases hPA : P ∣ A
    · obtain ⟨A1, rfl⟩ := hPA
      apply ih j A1 B
      · intro h1
        apply hA
        rw [pow_succ']
        exact mul_dvd_mul_left P h1
      · exact hB
      · have h2 : P * P ^ (i + j + 1) ∣ P * (A1 * B) := by
          rw [← pow_succ', ← mul_assoc]
          have e : i + j + 1 + 1 = i + 1 + j + 1 := by omega
          rw [e]
          exact h
        exact (mul_dvd_mul_iff_left hpr.ne_zero).mp h2
    · apply hB
      have h3 := hpr.pow_dvd_of_dvd_mul_left (i + 1 + j + 1) hPA h
      exact dvd_trans (pow_dvd_pow P (by omega)) h3

theorem mul_notMem (hP : P.IsPrime) (hP0 : P ≠ ⊥) {a b : R} {i j : ℕ} (ha : a ∉ P ^ (i + 1))
    (hb : b ∉ P ^ (j + 1)) : a * b ∉ P ^ (i + j + 1) := by
  intro hab
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  refine not_pow_dvd_mul_of_not_pow_dvd_of_not_pow_dvd hpr i j (Ideal.span {a}) (Ideal.span {b}) ?_ ?_ ?_
  · rwa [Ideal.dvd_span_singleton]
  · rwa [Ideal.dvd_span_singleton]
  · rwa [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]

theorem pow_le_span_mul_sup (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c k : ℕ} (hg : g ∉ P ^ (c + 1))
    (hck : c ≤ k) : P ^ k ≤ Ideal.span {g} * P ^ (k - c) ⊔ P ^ (k + 1) := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hP0 hP.ne_top (by omega : k - c < k - c + 1))
  have hdvd : Ideal.span {g} * P ^ (k - c) ⊔ P ^ (k + 1) ∣ P ^ (k + 1) :=
    Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr (k + 1)).mp hdvd
  rw [associated_iff_eq] at hm
  have hgx : g * x ∈ P ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hx)
  have hmk : m ≤ k := by
    by_contra h
    have h1 := mul_notMem hP hP0 hg hx'
    have e : c + (k - c) + 1 = k + 1 := by omega
    rw [e] at h1
    exact h1 (Ideal.pow_le_pow_right (by omega) hgx)
  rw [hm]
  exact Ideal.pow_le_pow_right hmk

theorem exists_fill (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c k : ℕ} (hg : g ∉ P ^ (c + 1))
    (hck : c ≤ k) {s : R} (hs : s ∈ P ^ k) : ∃ r ∈ P ^ (k - c), s - g * r ∈ P ^ (k + 1) := by
  have h := pow_le_span_mul_sup hP hP0 hg hck hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  refine ⟨r, hr, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end DedekindLFunctions

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem ne_bot {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)

theorem map_ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : extP K 𝔭 ≠ ⊥ := by
  intro h
  apply ne_bot h𝔭
  have h1 : Ideal.comap ι (Ideal.map ι 𝔭) = 𝔭 := Ideal.comap_map_eq_self_of_faithfullyFlat _
  have h3 : Ideal.comap ι (Ideal.map ι (⊥ : Ideal (𝓞 F))) = ⊥ :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [Ideal.map_bot] at h3
  change Ideal.map ι 𝔭 = ⊥ at h
  rw [← h1, h, h3]

theorem mem_pow_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 F) : ι a ∈ extP K 𝔭 ^ k ↔ a ∈ 𝔭 ^ k := by
  have h : Ideal.comap ι (Ideal.map ι (𝔭 ^ k)) = 𝔭 ^ k :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  change ι a ∈ (Ideal.map ι 𝔭) ^ k ↔ a ∈ 𝔭 ^ k
  rw [← Ideal.map_pow]
  constructor
  · intro ha
    rw [← h]
    exact Ideal.mem_comap.mpr ha
  · intro ha
    exact Ideal.mem_map_of_mem _ ha

private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : ((ι a : 𝓞 K) : K) = algebraMap F K (a : F) := by
  first
  | rfl
  | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K a).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K a)

private theorem coe_conjO_eq_star_coe (z : 𝓞 K) : ((conjO K z : 𝓞 K) : K) = star (z : K) := by
  first
  | rfl
  | (unfold conjO; rfl)

theorem conjO_map (hF : IsFixF K F) (a : 𝓞 F) : conjO K (ι a) = ι a := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star_coe, coe_iota_eq_algebraMap_coe]
  exact (hF _).mpr ⟨_, rfl⟩

theorem conjO_mem_pow (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    ∀ z ∈ extP K 𝔭 ^ k, conjO K z ∈ extP K 𝔭 ^ k := by
  intro z hz
  have hcomp : (conjO K).comp ι = ι := RingHom.ext (fun a => conjO_map hF a)
  have hJ : extP K 𝔭 ^ k = Ideal.map ι (𝔭 ^ k) := by
    rw [Ideal.map_pow]
    rfl
  rw [hJ] at hz ⊢
  have h1 := Ideal.mem_map_of_mem (conjO K) hz
  rwa [Ideal.map_map, hcomp] at h1

theorem map_pow_le_span_sup {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {c : ℕ}
    (hd : d ∉ 𝔭 ^ (c + 1)) (N : ℕ) : extP K 𝔭 ^ c ≤ Ideal.span {ι d} ⊔ extP K 𝔭 ^ N := by
  have h := pow_le_span_sup h𝔭.isPrime (ne_bot h𝔭) hd N
  have h2 := Ideal.map_mono (f := ι) h
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at h2
  exact h2

theorem exists_fillO {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {c k : ℕ}
    (hd : d ∉ 𝔭 ^ (c + 1)) (hck : c ≤ k) {s : 𝓞 K} (hs : s ∈ extP K 𝔭 ^ k) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), s - ι d * r ∈ extP K 𝔭 ^ (k + 1) := by
  have h := pow_le_span_mul_sup h𝔭.isPrime (ne_bot h𝔭) hd hck
  have h2 := Ideal.map_mono (f := ι) h
  simp only [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    Ideal.map_pow] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (h2 hs)
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  refine ⟨r, hr, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

theorem mem_of_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {v j : ℕ}
    (hd : d ∉ 𝔭 ^ (v + 1)) {z : 𝓞 K} (hz : ι d * z ∈ extP K 𝔭 ^ (v + j)) : z ∈ extP K 𝔭 ^ j := by
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime (ne_bot h𝔭) h𝔭.isPrime
  have hdvd : Ideal.span {d} ⊔ 𝔭 ^ (v + j) ∣ 𝔭 ^ (v + j) := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr (v + j)).mp hdvd
  rw [associated_iff_eq] at hm
  have hdm : d ∈ 𝔭 ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self d)
  have hmv : m ≤ v := by
    by_contra h
    exact hd (Ideal.pow_le_pow_right (by omega) hdm)
  have hS : Ideal.span {ι d} ⊔ extP K 𝔭 ^ (v + j) = extP K 𝔭 ^ m := by
    have h1 := congrArg (Ideal.map ι) hm
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at h1
    exact h1
  have hle : extP K 𝔭 ^ m * Ideal.span {z} ≤ extP K 𝔭 ^ (v + j) := by
    rw [← hS, Ideal.sup_mul]
    refine sup_le ?_ (by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right)
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
    exact hz
  have hdiv : extP K 𝔭 ^ m * extP K 𝔭 ^ (v + j - m) ∣ extP K 𝔭 ^ m * Ideal.span {z} := by
    rw [← pow_add, show m + (v + j - m) = v + j by omega]
    exact Ideal.dvd_iff_le.mpr hle
  have h0 : extP K 𝔭 ^ m ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  have h2 := (mul_dvd_mul_iff_left h0).mp hdiv
  exact Ideal.dvd_span_singleton.mp (dvd_trans (pow_dvd_pow _ (by omega)) h2)

private theorem exists_iota_eq_of_star_coe_eq (hF : IsFixF K F) (w : 𝓞 K) (hw : star (w : K) = (w : K)) :
    ∃ a : 𝓞 F, ι a = w := by
  obtain ⟨f, hf⟩ := (hF _).mp hw
  have hfi : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap F K f) := by
      rw [hf]
      exact RingOfIntegers.isIntegral_coe w
    exact (isIntegral_algHom_iff ((algebraMap F K).toIntAlgHom) (algebraMap F K).injective).mp h1
  refine ⟨⟨f, by
    first
    | exact hfi
    | exact (mem_integralClosure_iff ℤ F).mpr hfi
    | exact (NumberField.mem_ringOfIntegers F f).mpr hfi
    | simpa [integralClosure] using hfi⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_iota_eq_algebraMap_coe _).trans hf

theorem exists_tr (hF : IsFixF K F) (z : 𝓞 K) : ∃ a : 𝓞 F, ι a = z + conjO K z := by
  apply exists_iota_eq_of_star_coe_eq hF
  have e : ((z + conjO K z : 𝓞 K) : K) = (z : K) + star (z : K) := by
    rw [← coe_conjO_eq_star_coe]
    rfl
  rw [e, star_add, star_star, add_comm]

theorem ι_inj : Function.Injective (ι) := by
  intro a b hab
  have h : Ideal.comap ι (Ideal.map ι (⊥ : Ideal (𝓞 F))) = ⊥ :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [Ideal.map_bot] at h
  have h1 : a - b ∈ Ideal.comap ι (⊥ : Ideal (𝓞 K)) := by
    rw [Ideal.mem_comap, map_sub, hab, sub_self]
    exact Ideal.zero_mem _
  rw [h, Ideal.mem_bot, sub_eq_zero] at h1
  exact h1

def trf (hF : IsFixF K F) (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_tr hF z)

theorem trf_spec (hF : IsFixF K F) (z : 𝓞 K) : ι (trf hF z) = z + conjO K z := Classical.choose_spec (exists_tr hF z)

def trF (hF : IsFixF K F) : 𝓞 K →ₗ[𝓞 F] 𝓞 F where
  toFun z := trf hF z
  map_add' x y := by
    apply ι_inj (K := K)
    rw [map_add, trf_spec, trf_spec, trf_spec, map_add]
    ring
  map_smul' a x := by
    apply ι_inj (K := K)
    rw [RingHom.id_apply, smul_eq_mul, map_mul, trf_spec, trf_spec, Algebra.smul_def, map_mul,
      conjO_map hF]
    ring

theorem trF_spec (hF : IsFixF K F) (z : 𝓞 K) : ι (trF hF z) = z + conjO K z := trf_spec hF z

theorem trF_mem_pow (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    trF hF z ∈ 𝔭 ^ k := (mem_pow_iff (K := K) 𝔭 k _).mp (by
    rw [trF_spec]
    exact Ideal.add_mem _ hz (conjO_mem_pow hF 𝔭 k z hz))

theorem exists_theta (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ θ : 𝓞 K, Ideal.span {θ - conjO K θ} ⊔ extP K 𝔭 = ⊤ := by
  have hne : extP K 𝔭 ≠ ⊤ := by
    intro h
    have h1 : ι 1 ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one, h]
      exact Submodule.mem_top
    rw [mem_pow_iff, pow_one] at h1
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hK.2.2 P hPmax
  have htc : t = conjO K θ := by
    apply RingOfIntegers.ext
    rw [coe_conjO_eq_star_coe]
    exact ht
  subst htc
  refine ⟨θ, ?_⟩
  have hδc : ((θ - conjO K θ : 𝓞 K) : K) = (θ : K) - star (θ : K) := by
    rw [← coe_conjO_eq_star_coe]
    rfl
  have hfix : star (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) =
      (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) := by
    have e : (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) =
        ((θ - conjO K θ : 𝓞 K) : K) * ((θ - conjO K θ : 𝓞 K) : K) := rfl
    rw [e, hδc, star_mul, star_sub, star_star]
    ring
  obtain ⟨r, hr⟩ := exists_iota_eq_of_star_coe_eq hF _ hfix
  have hr𝔭 : r ∉ 𝔭 := by
    intro hr'
    have h1 : ι r ∈ P := hPle (Ideal.mem_map_of_mem _ hr')
    rw [hr] at h1
    exact hθt ((hPmax.isPrime.mem_or_mem h1).elim id id)
  have h1 : Ideal.span {r} ⊔ 𝔭 = ⊤ := by
    refine h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right (fun h => hr𝔭 ?_))
    rw [h]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self r)
  have h2 := congrArg (Ideal.map ι) h1
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top] at h2
  rw [hr] at h2
  refine eq_top_iff.mpr ?_
  rw [← h2]
  exact sup_le_sup_right
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)) _

theorem exists_inv_theta {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    ∃ e : 𝓞 K, δ * e - 1 ∈ extP K 𝔭 ^ N := by
  have h : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := by
    first
    | exact Ideal.sup_pow_eq_top hδ
    | exact Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hδ).pow_right)
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {δ} ⊔ extP K 𝔭 ^ N := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp h1
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨e, ?_⟩
  have e2 : δ * e - 1 = -w := by
    rw [← hyw]
    ring
  rw [e2]
  exact neg_mem hw

theorem mem_of_unit_mul_mem {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) {N : ℕ}
    {z : 𝓞 K} (hz : δ * z ∈ extP K 𝔭 ^ N) : z ∈ extP K 𝔭 ^ N := by
  obtain ⟨e, he⟩ := exists_inv_theta hδ N
  have e2 : z = e * (δ * z) - (δ * e - 1) * z := by ring
  rw [e2]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ e hz) (Ideal.mul_mem_right z _ he)

end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
