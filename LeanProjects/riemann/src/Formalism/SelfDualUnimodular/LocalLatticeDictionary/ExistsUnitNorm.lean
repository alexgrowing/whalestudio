import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def InJ (p : Ideal (𝓞 K)) (a : K) : Prop :=
  ∃ r s : 𝓞 K, s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ∧ r ∈ p ∧ r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ∧
    a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s

theorem inJ_of_fixed {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) (hfix : star a = a)
    (hnu : ¬ IsUnitIn (locRing p) a) : InJ p a := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)
  have hr : r ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := fun h => hnu ((isUnitIn_div_iff hp r hs).2 h)
  rw [mem_hcompl_iff hp] at hr
  have hs' := (mem_hcompl_iff hp s).1 hs
  have hcs := (mem_hcompl_iff hp _).1 (conjO_mem_hcompl hs)
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have hcs0 := algebraMap_ne_zero_of_mem_hcompl hp (conjO_mem_hcompl hs)
  have key : conjO K r * s = r * conjO K s := by
    apply RingOfIntegers.ext
    have e1 := hfix
    rw [star_div₀, ← algebraMap_conjO, ← algebraMap_conjO] at e1
    have e2 : algebraMap (𝓞 K) K (conjO K r) * algebraMap (𝓞 K) K s =
        algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K (conjO K s) := by
      rw [div_eq_div_iff hcs0 hs0] at e1
      exact e1
    simpa [map_mul] using e2
  refine ⟨r, s, hs, ?_, ?_, rfl⟩
  · by_contra hrp
    have hrc : r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
      by_contra h'; exact hr ⟨hrp, h'⟩
    rw [mem_conjIdeal_iff] at hrc
    have h1 : conjO K r * s ∈ p := p.mul_mem_right _ hrc
    rw [key] at h1
    rcases hp.mem_or_mem h1 with h | h
    · exact hrp h
    · exact hcs.1 h
  · by_contra hrc
    have hrp : r ∈ p := by
      by_contra h'; exact hr ⟨h', hrc⟩
    have h1 : r * conjO K s ∈ p := p.mul_mem_right _ hrp
    rw [← key] at h1
    rcases hp.mem_or_mem h1 with h | h
    · exact hrc ((mem_conjIdeal_iff p r).2 h)
    · exact hs'.1 h

theorem InJ.add {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a b : K} (ha : InJ p a) (hb : InJ p b) :
    InJ p (a + b) := by
  have hnz : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ≠ 0 := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact fun h => hx.1 (h ▸ p.zero_mem)
    | one => exact one_ne_zero
    | mul x y _ _ hx hy => exact mul_ne_zero hx hy
  obtain ⟨r, s, hs, hr1, hr2, rfl⟩ := ha
  obtain ⟨r', s', hs', hr1', hr2', rfl⟩ := hb
  refine ⟨r * s' + r' * s, s * s', mul_mem hs hs', p.add_mem (p.mul_mem_right _ hr1) (p.mul_mem_right _ hr1'),
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).add_mem (Ideal.mul_mem_right _ _ hr2) (Ideal.mul_mem_right _ _ hr2'), ?_⟩
  have h1 : algebraMap (𝓞 K) K s ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz s hs)
  have h2 : algebraMap (𝓞 K) K s' ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz s' hs')
  rw [div_add_div _ _ h1 h2, map_add, map_mul, map_mul, map_mul]
  ring

theorem InJ.mul {p : Ideal (𝓞 K)} (hp : p.IsPrime) {κ a : K} (hκ : κ ∈ locRing p) (ha : InJ p a) :
    InJ p (κ * a) := by
  have hnz : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ≠ 0 := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact fun h => hx.1 (h ▸ p.zero_mem)
    | one => exact one_ne_zero
    | mul x y _ _ hx hy => exact mul_ne_zero hx hy
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hκ
  obtain ⟨v, hv, hvk⟩ := hκ
  obtain ⟨u, hu⟩ := Submodule.mem_one.1 hvk
  obtain ⟨r, s, hs, hr1, hr2, rfl⟩ := ha
  refine ⟨u * r, v * s, mul_mem hv hs, p.mul_mem_left _ hr1, Ideal.mul_mem_left _ _ hr2, ?_⟩
  have h1 : algebraMap (𝓞 K) K v ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz v hv)
  have hκ' : κ = algebraMap (𝓞 K) K u / algebraMap (𝓞 K) K v := by
    rw [hu]
    field_simp
  rw [hκ', map_mul, map_mul, div_mul_div_comm]

theorem InJ.one_add {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : InJ p a) :
    IsUnitIn (locRing p) (1 + a) := by
  obtain ⟨r, s, hs, h1, h1', rfl⟩ := ha
  have e1 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have hs' := (mem_hcompl_iff hp s).1 hs
  have e : (1 : K) + algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s =
      algebraMap (𝓞 K) K (s + r) / algebraMap (𝓞 K) K s := by
    rw [map_add]; field_simp
  rw [e, isUnitIn_div_iff hp _ hs, mem_hcompl_iff hp]
  exact ⟨fun h => hs'.1 (by simpa using p.sub_mem h h1),
    fun h => hs'.2 (by simpa using Ideal.sub_mem _ h h1')⟩

variable {V : Type} [AddCommGroup V] [Module K V]

theorem norm_add_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) (κ : K) :
    h (x + κ • y) (x + κ • y) = h x x + κ * h x y + star κ * h y x + star κ * κ * h y y := by
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply]
  ring

theorem exists_unit_norm {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (x₀ : V) (hx₀ : x₀ ≠ 0) :
    ∃ e ∈ M, IsUnitIn (locRing p) (h e e) := by
  have hS := isHermSemilocal_locRing hK hp
  set S := locRing p with hSdef
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  obtain ⟨m, htM, hm0⟩ : ∃ m ∈ M, m ≠ 0 := by
    obtain ⟨t, ht0, htM⟩ := hM.span x₀
    exact ⟨t • x₀, htM, smul_ne_zero ht0 hx₀⟩
  obtain ⟨y, hy⟩ : ∃ y, h m y ≠ 0 := by
    by_contra hc; push Not at hc; exact hm0 (hnd m hc)
  obtain ⟨t', ht'0, ht'M⟩ := hM.span y
  let f : V →+ K :=
    { toFun := fun u => h u m
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ u, f u = h u m := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨u, hu, rfl⟩
    refine ⟨star c • u, hM.smul_mem _ (hS.star_mem _ hc) _ hu, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t' • y, ht'M, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hsym m y]
    exact mul_ne_zero (star_ne_zero.mpr ht'0) (star_ne_zero.mpr hy)
  have hb : ∀ a ∈ M.map f, (1 : K) * a ∈ S := by
    rintro _ ⟨u, hu, rfl⟩
    rw [one_mul]; exact hM.int u hu m htM
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨1, one_ne_zero, hb⟩
  rw [hf] at hα
  have hyM : α⁻¹ • m ∈ M := by
    apply hM.dual
    intro u hu
    have := hdiv _ ⟨u, hu, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hxy : h w₀ (α⁻¹ • m) = 1 := by
    rw [map_smul, smul_eq_mul, hα, inv_mul_cancel₀ hα0]
  have hyx : h (α⁻¹ • m) w₀ = 1 := by rw [← hsym, hxy, star_one]
  generalize α⁻¹ • m = y' at hyM hxy hyx
  by_cases hux : IsUnitIn S (h w₀ w₀)
  · exact ⟨w₀, hw₀, hux⟩
  by_cases huy : IsUnitIn S (h y' y')
  · exact ⟨y', hyM, huy⟩
  obtain ⟨κ, hκ, hκt⟩ := exists_trace_eq hS S.one_mem (star_one K)
  refine ⟨w₀ + κ • y', M.add_mem hw₀ (hM.smul_mem _ hκ _ hyM), ?_⟩
  have hJx := inJ_of_fixed hp.isPrime (hM.int _ hw₀ _ hw₀) (hsym w₀ w₀) hux
  have hJy := inJ_of_fixed hp.isPrime (hM.int _ hyM _ hyM) (hsym _ _) huy
  have e : h (w₀ + κ • y') (w₀ + κ • y') = 1 + (h w₀ w₀ + (star κ * κ) * h y' y') := by
    rw [norm_add_smul, hxy, hyx]
    linear_combination hκt
  rw [e]
  exact (hJx.add hp.isPrime (hJy.mul hp.isPrime (S.mul_mem (hS.star_mem _ hκ) hκ))).one_add hp.isPrime

theorem exists_norm_eq {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (e : V)
    (he : IsUnitIn (locRing p) (h e e)) :
    ∃ X ∈ M, h X X = h e e := by
  have hS := isHermSemilocal_locRing hK hp
  set S := locRing p with hSdef
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  set a := h e e with ha
  have hafix : star a = a := hsym e e
  obtain ⟨ha0, haS, hainv⟩ := he
  have he0 : e ≠ 0 := by rintro rfl; simp [a] at ha0
  obtain ⟨y, hy⟩ : ∃ y, h e y ≠ 0 := by
    by_contra hc; push Not at hc; exact he0 (hnd e hc)
  obtain ⟨t', ht'0, ht'M⟩ := hM.span y
  obtain ⟨t, ht0, htM⟩ := hM.span e
  let f : V →+ K :=
    { toFun := fun u => h u e
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ u, f u = h u e := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨u, hu, rfl⟩
    refine ⟨star c • u, hM.smul_mem _ (hS.star_mem _ hc) _ hu, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t' • y, ht'M, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hsym e y]
    exact mul_ne_zero (star_ne_zero.mpr ht'0) (star_ne_zero.mpr hy)
  have hb : ∀ a ∈ M.map f, t * a ∈ S := by
    rintro _ ⟨u, hu, rfl⟩
    have := hM.int u hu _ htM
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨t, ht0, hb⟩
  rw [hf] at hα
  have hyM : α⁻¹ • e ∈ M := by
    apply hM.dual
    intro u hu
    have := hdiv _ ⟨u, hu, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hyw : h (α⁻¹ • e) w₀ = 1 := by
    rw [map_smulₛₗ, LinearMap.smul_apply, ← hsym w₀ e, hα, starRingEnd_apply, smul_eq_mul,
      ← star_mul', inv_mul_cancel₀ hα0, star_one]
  have hyy : h (α⁻¹ • e) (α⁻¹ • e) = star α⁻¹ * α⁻¹ * a := by
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul, smul_eq_mul]
    ring
  let h' : V →ₗ⋆[K] V →ₗ[K] K := a⁻¹ • h
  have h'app : ∀ u v, h' u v = a⁻¹ * h u v := fun u v => by
    show (a⁻¹ • h) u v = _
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  have hs' : h'.IsSymm := by
    refine ⟨fun u v => ?_⟩
    rw [h'app, h'app, map_mul, starRingEnd_apply, starRingEnd_apply, star_inv₀, hafix, hsym u v]
  have hnorm : star α⁻¹ * α⁻¹ ∈ S := by
    have : star α⁻¹ * α⁻¹ = h (α⁻¹ • e) (α⁻¹ • e) * a⁻¹ := by rw [hyy]; field_simp
    rw [this]; exact S.mul_mem (hM.int _ hyM _ hyM) hainv
  obtain ⟨bb, hbb1, hbbS⟩ := exists_norm_one_mul_mem hS (a := α⁻¹) hnorm
  have hbb0 : bb ≠ 0 := by rintro rfl; simp at hbb1
  have hyy' : h' (α⁻¹ • e) (α⁻¹ • e) = star (α⁻¹ * bb) * (α⁻¹ * bb) := by
    rw [h'app, hyy, star_mul']
    calc a⁻¹ * (star α⁻¹ * α⁻¹ * a) = star α⁻¹ * α⁻¹ * (star bb * bb) := by
          rw [hbb1]; field_simp
      _ = _ := by ring
  have hwM : a • w₀ ∈ M := hM.smul_mem _ haS _ hw₀
  have hyw' : h' (α⁻¹ • e) (a • w₀) = 1 := by
    rw [h'app, map_smul, smul_eq_mul, hyw]; field_simp
  have hww : h' (a • w₀) (a • w₀) ∈ S := by
    rw [h'app, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
      hafix]
    have : a⁻¹ * (a * (a * h w₀ w₀)) = a * h w₀ w₀ := by field_simp
    rw [this]; exact S.mul_mem haS (hM.int _ hw₀ _ hw₀)
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs' hbbS
    (mul_ne_zero (inv_ne_zero hα0) hbb0) hyy' hyw' hww
  refine ⟨c • (a • w₀) + d • (α⁻¹ • e), M.add_mem (hM.smul_mem _ hc _ hwM) (hM.smul_mem _ hd _ hyM), ?_⟩
  rw [h'app] at hcd
  have := congrArg (fun u => a * u) hcd
  rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul, mul_one] at this
  exact this

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
