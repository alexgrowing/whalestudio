import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

namespace GlobalTheory.InvolutionTraceUnit

open Polynomial IsLocalRing

theorem ff_norm {k : Type} [Field k] [Finite k] (σ : k →+* k) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ x, σ x ≠ x) (u : k) (hu : σ u = u) : ∃ w, w * σ w = u := by
  classical
  let F : Subfield k := RingHom.eqLocusField σ (RingHom.id k)
  have hF : ∀ x : k, x ∈ F ↔ σ x = x := fun x => Iff.rfl
  let σ' : k ≃ₐ[F] k :=
    { toFun := σ, invFun := σ, left_inv := hσ, right_inv := hσ, map_mul' := σ.map_mul,
      map_add' := σ.map_add, commutes' := fun r => (hF r).1 r.2 }
  have hσ' : ∀ x, σ' x = σ x := fun _ => rfl
  have h1 : ∀ (τ : k ≃ₐ[F] k) (x : k), τ x = x ∨ τ x = σ x := by
    intro τ x
    have hs : τ (x + σ x) = x + σ x :=
      τ.commutes ⟨x + σ x, (hF _).2 (by rw [map_add, hσ, add_comm])⟩
    have hn : τ (x * σ x) = x * σ x :=
      τ.commutes ⟨x * σ x, (hF _).2 (by rw [map_mul, hσ, mul_comm])⟩
    rw [map_add] at hs
    rw [map_mul] at hn
    have : (τ x - x) * (τ x - σ x) = 0 := by
      linear_combination (τ x) * hs - hn
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have h2 : ∀ τ : k ≃ₐ[F] k, τ = 1 ∨ τ = σ' := by
    intro τ
    by_contra hc
    push Not at hc
    obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
      by_contra h; push Not at h
      exact hc.1 (AlgEquiv.ext h)
    obtain ⟨b, hb⟩ : ∃ b, τ b ≠ σ b := by
      by_contra h; push Not at h
      exact hc.2 (AlgEquiv.ext h)
    have ha' := (h1 τ a).resolve_left ha
    have hb' := (h1 τ b).resolve_right hb
    rcases h1 τ (a + b) with h | h
    · rw [map_add, hb'] at h
      exact ha (add_right_cancel h)
    · rw [map_add, map_add, ha'] at h
      exact hb (add_left_cancel h)
  have h3 : (1 : k ≃ₐ[F] k) ≠ σ' := by
    obtain ⟨x, hx⟩ := hne
    intro h
    apply hx
    rw [← hσ', ← h]; rfl
  have h4 : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ'} := by
    ext τ; simpa using h2 τ
  obtain ⟨w, hw⟩ := FiniteField.norm_surjective F k ⟨u, (hF u).2 hu⟩
  refine ⟨w, ?_⟩
  have := Algebra.norm_eq_prod_automorphisms F w
  rw [hw, h4, Finset.prod_pair h3] at this
  exact this.symm

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]

theorem mem_of_invol (s : O →+* O) (hs : ∀ x, s (s x) = x) {a : O} (ha : a ∈ maximalIdeal O) :
    s a ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro h
  exact ha (hs a ▸ h.map s)

theorem unit_of_not_mem {a : O} (ha : a ∉ maximalIdeal O) : IsUnit a := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at ha
  exact not_not.1 ha

theorem not_mem_of_unit {a : O} (ha : IsUnit a) : a ∉ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  exact not_not.2 ha

theorem exists_trace_unit (s : O →+* O) (hs : ∀ x, s (s x) = x) (θ : O)
    (hθ : θ - s θ ∉ maximalIdeal O) : ∃ t : O, IsUnit (t + s t) ∧ IsUnit (t * s t) := by
  by_cases h2 : (2 : O) ∈ maximalIdeal O
  · have hu : IsUnit θ := by
      apply unit_of_not_mem
      intro h
      exact hθ (sub_mem h (mem_of_invol s hs h))
    refine ⟨θ, unit_of_not_mem fun h => hθ ?_, hu.mul (hu.map s)⟩
    have : θ - s θ = (θ + s θ) - 2 * s θ := by ring
    rw [this]
    exact sub_mem h (Ideal.mul_mem_right _ _ h2)
  · refine ⟨1, ?_, by simp⟩
    rw [map_one, one_add_one_eq_two]
    exact unit_of_not_mem h2

theorem norm_principal [IsAdicComplete (maximalIdeal O) O] (s : O →+* O) (hs : ∀ x, s (s x) = x)
    (θ : O) (hθ : θ - s θ ∉ maximalIdeal O) (x : O) (hx : s x = x)
    (hx1 : 1 - x ∈ maximalIdeal O) : ∃ w, w * s w = x := by
  obtain ⟨t, hT, hN⟩ := exists_trace_unit s hs θ hθ
  obtain ⟨M, hM⟩ := hN.exists_right_inv
  have hMu : IsUnit M := IsUnit.of_mul_eq_one_right _ hM
  have H := IsAdicComplete.henselianRing O (maximalIdeal O)
  obtain ⟨a, ha, ha0⟩ := H.is_henselian
    (X ^ 2 + (C ((t + s t) * M) * X + C ((1 - x) * M)))
    (by
      apply Polynomial.monic_X_pow_add
      refine lt_of_le_of_lt (Polynomial.degree_linear_le) ?_
      norm_num)
    0 (by simpa using Ideal.mul_mem_right _ _ hx1)
    (by
      apply IsUnit.map
      simpa using And.intro hT hMu)
  rw [sub_zero] at ha0
  have e : a ^ 2 + ((t + s t) * M * a + (1 - x) * M) = 0 := by
    simpa [IsRoot] using ha
  have e1 : t * s t * a ^ 2 + (t + s t) * a + (1 - x) = 0 := by
    linear_combination (t * s t) * e - ((t + s t) * a + (1 - x)) * hM
  have e2 : t * s t * s a ^ 2 + (t + s t) * s a + (1 - x) = 0 := by
    have := congrArg s e1
    simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, hs, hx] at this
    linear_combination this
  have e3 : (a - s a) * (t * s t * (a + s a) + (t + s t)) = 0 := by
    linear_combination e1 - e2
  have e4 : s a = a := by
    rcases mul_eq_zero.1 e3 with h | h
    · exact (sub_eq_zero.1 h).symm
    · exfalso
      apply not_mem_of_unit hT
      have : t + s t = -(t * s t * (a + s a)) := by linear_combination h
      rw [this]
      exact neg_mem (Ideal.mul_mem_left _ _ (add_mem ha0 (mem_of_invol s hs ha0)))
  refine ⟨1 + a * t, ?_⟩
  rw [map_add, map_one, map_mul, e4]
  linear_combination e1

theorem norm_unit [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (θ : O) (hθ : θ - s θ ∉ maximalIdeal O) (u : O) (hu : IsUnit u)
    (hsu : s u = u) : ∃ w, w * s w = u := by
  haveI : IsLocalHom s := ⟨fun a ha => hs a ▸ ha.map s⟩
  obtain ⟨w', hw'⟩ := ff_norm (ResidueField.map s)
    (by
      intro x
      obtain ⟨x, rfl⟩ := residue_surjective x
      rw [ResidueField.map_residue, ResidueField.map_residue, hs])
    ⟨residue O θ, by
      rw [ResidueField.map_residue]
      intro h
      apply hθ
      rw [← residue_eq_zero_iff, map_sub, h, sub_self]⟩
    (residue O u) (by rw [ResidueField.map_residue, hsu])
  obtain ⟨w, rfl⟩ := residue_surjective w'
  rw [ResidueField.map_residue, ← map_mul] at hw'
  have hm : u - w * s w ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_sub, hw', sub_self]
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hsv : s v = v := by
    have := congrArg s hv
    rw [map_mul, hsu, map_one] at this
    linear_combination v * this - s v * hv
  have hwu : IsUnit (w * s w) := by
    apply unit_of_not_mem
    intro h
    apply not_mem_of_unit hu
    simpa using add_mem hm h
  have hw : IsUnit w := isUnit_of_mul_isUnit_left hwu
  obtain ⟨r, hr⟩ := hw.exists_right_inv
  have hr' : s w * s r = 1 := by rw [← map_mul, hr, map_one]
  obtain ⟨z, hz⟩ := norm_principal s hs θ hθ (u * (r * s r))
    (by rw [map_mul, map_mul, hs, hsu, mul_comm (s r)])
    (by
      have : 1 - u * (r * s r) = -((u - w * s w) * (r * s r)) := by
        linear_combination (-(s w * s r)) * hr - hr'
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ hm))
  refine ⟨w * z, ?_⟩
  rw [map_mul]
  linear_combination (w * s w) * hz + u * (s w * s r) * hr + u * hr'

end Local

section Lattice

variable {O E V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E]
  [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

theorem clear_denominator (L : Submodule O V) (y : V) (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ d : O, d ≠ 0 ∧ d • y ∈ L := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hx
    · rw [mul_smul]; exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective O a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O E q ≠ 0 := by simpa using hq0
    refine ⟨d * q, mul_ne_zero hd hq0, ?_⟩
    have : (d * q) • ((algebraMap O E p / algebraMap O E q) • x) = p • d • x := by
      rw [← algebraMap_smul E (d * q), ← algebraMap_smul E p, ← algebraMap_smul E d, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hx

theorem exists_unit_length (c : E →+* E) (s : O →+* O) (hs : ∀ x, s (s x) = x)
    (hcs : ∀ x, c (algebraMap O E x) = algebraMap O E (s x)) (θ : O)
    (hθ : θ - s θ ∉ maximalIdeal O) (h : V → V → E)
    (ha : ∀ y y' z, h (y + y') z = h y z + h y' z) (hm : ∀ (a : E) y z, h (a • y) z = a * h y z)
    (hc : ∀ y z, h z y = c (h y z)) (W : Submodule E V) (L : Submodule O V) (hfg : L.FG)
    (hne : L ≠ ⊥) (hLW : ∀ y ∈ L, y ∈ W)
    (hint : ∀ y ∈ L, ∀ z ∈ L, h y z ∈ (algebraMap O E).range)
    (hdual : ∀ y ∈ W, (∀ z ∈ L, h y z ∈ (algebraMap O E).range) → y ∈ L) :
    ∃ e ∈ L, ∃ u : O, IsUnit u ∧ algebraMap O E u = h e e := by
  by_contra hcon
  have inj := IsFractionRing.injective O E
  have h0 : ∀ e ∈ L, ∀ a : O, algebraMap O E a = h e e → a ∈ maximalIdeal O := by
    intro e he a hae
    by_contra hn
    exact hcon ⟨e, he, a, unit_of_not_mem hn, hae⟩
  have h1 : ∀ y ∈ L, ∀ z ∈ L, ∀ a : O, algebraMap O E a = h y z → a + s a ∈ maximalIdeal O := by
    intro y hy z hz a hayz
    obtain ⟨b, hb⟩ := hint y hy y hy
    obtain ⟨d, hd⟩ := hint z hz z hz
    have hsum : algebraMap O E (b + d + (a + s a)) = h (y + z) (y + z) := by
      have e1 : h y (y + z) = h y y + h y z := by
        rw [hc (y + z) y, ha, map_add, ← hc, ← hc]
      have e2 : h z (y + z) = h z y + h z z := by
        rw [hc (y + z) z, ha, map_add, ← hc, ← hc]
      rw [ha, e1, e2, hc y z, map_add, map_add, map_add, ← hcs, hb, hd, hayz]
      ring
    have := sub_mem (h0 _ (add_mem hy hz) _ hsum) (add_mem (h0 y hy b hb) (h0 z hz d hd))
    simpa using this
  have h2 : ∀ y ∈ L, ∀ z ∈ L, ∀ a : O, algebraMap O E a = h y z → a ∈ maximalIdeal O := by
    intro y hy z hz a hayz
    have k1 := h1 y hy z hz a hayz
    have k2 := h1 (θ • y) (L.smul_mem _ hy) z hz (θ * a)
      (by rw [← algebraMap_smul E θ y, hm, map_mul, hayz])
    have k3 : (θ - s θ) * a ∈ maximalIdeal O := by
      have : (θ - s θ) * a = (θ * a + s (θ * a)) - s θ * (a + s a) := by
        rw [map_mul]; ring
      rw [this]
      exact sub_mem k2 (Ideal.mul_mem_left _ _ k1)
    exact ((Ideal.IsMaximal.isPrime inferInstance).mem_or_mem k3).resolve_left hθ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O E ϖ ≠ 0 := by simpa using hϖ.ne_zero
  apply hne
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) L hfg
  · intro y hy
    have hy' : (algebraMap O E ϖ)⁻¹ • y ∈ L := by
      apply hdual _ (W.smul_mem _ (hLW y hy))
      intro z hz
      obtain ⟨a, hayz⟩ := hint y hy z hz
      have := h2 y hy z hz a hayz
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
      obtain ⟨b, rfl⟩ := this
      refine ⟨b, ?_⟩
      rw [hm, ← hayz, map_mul, inv_mul_cancel_left₀ hϖ0]
    have : y = ϖ • ((algebraMap O E ϖ)⁻¹ • y) := by
      rw [← algebraMap_smul E ϖ, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]
    rw [this]
    refine Submodule.smul_mem_smul ?_ hy'
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  · rw [jacobson_eq_maximalIdeal _ bot_ne_top]

theorem extend_family [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    [FiniteDimensional E V] (c : E →+* E) (s : O →+* O) (hs : ∀ x, s (s x) = x)
    (hcs : ∀ x, c (algebraMap O E x) = algebraMap O E (s x)) (θ : O)
    (hθ : θ - s θ ∉ maximalIdeal O) (h : V → V → E)
    (ha : ∀ y y' z, h (y + y') z = h y z + h y' z) (hm : ∀ (a : E) y z, h (a • y) z = a * h y z)
    (hc : ∀ y z, h z y = c (h y z)) (L : Submodule O V) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set V) = ⊤)
    (hdual : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap O E).range)
    (k : ℕ) (hk : k < Module.finrank E V) (v : Fin k → V) (hv : ∀ i, v i ∈ L)
    (hon : ∀ i j, h (v i) (v j) = if i = j then 1 else 0) :
    ∃ e ∈ L, h e e = 1 ∧ ∀ i, h e (v i) = 0 := by
  classical
  have inj := IsFractionRing.injective O E
  let B : V → V →ₗ[E] E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => ha y y' z,
      map_smul' := fun a y => hm a y z }
  have hB : ∀ z y, B z y = h y z := fun _ _ => rfl
  let φ : V →ₗ[E] (Fin k → E) := LinearMap.pi fun i => B (v i)
  have hφ : ∀ y, y ∈ LinearMap.ker φ ↔ ∀ i, h y (v i) = 0 := by
    intro y
    rw [LinearMap.mem_ker, funext_iff]
    rfl
  let L' : Submodule O V := L ⊓ (LinearMap.ker φ).restrictScalars O
  have hL' : ∀ y, y ∈ L' ↔ y ∈ L ∧ y ∈ LinearMap.ker φ := fun y => Iff.rfl
  have hker : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨y₀, hy₀, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  obtain ⟨d, hd, hdy⟩ := clear_denominator (E := E) L y₀ (by rw [hspan]; trivial)
  have hne : L' ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨d • y₀, (hL' _).2 ⟨hdy, ?_⟩, ?_⟩
    · rw [← algebraMap_smul E d]; exact Submodule.smul_mem _ _ hy₀
    · rw [← algebraMap_smul E d]; exact smul_ne_zero (by simpa using hd) hy0
  obtain ⟨e, he, u, hu, hue⟩ := exists_unit_length c s hs hcs θ hθ h ha hm hc (LinearMap.ker φ) L'
    (hfg.of_le inf_le_left) hne (fun y hy => hy.2)
    (fun y hy z hz => (hdual y).1 hy.1 z hz.1)
    (by
      intro y hy hyz
      refine (hL' y).2 ⟨(hdual y).2 fun z hz => ?_, hy⟩
      have hz' : z - ∑ i, h z (v i) • v i ∈ L' := by
        refine (hL' _).2 ⟨sub_mem hz (Submodule.sum_mem _ fun i _ => ?_), (hφ _).2 fun j => ?_⟩
        · obtain ⟨a, hai⟩ := (hdual z).1 hz (v i) (hv i)
          rw [← hai, algebraMap_smul]
          exact L.smul_mem _ (hv i)
        · rw [← hB, map_sub, map_sum]
          simp only [hB, hm, hon]
          simp
      have := hyz _ hz'
      have hvy : ∀ i, h (v i) y = 0 := fun i => by rw [hc, (hφ y).1 hy i, map_zero]
      rw [hc, ← hB, map_sub, map_sum] at this
      simp only [hB, hm, hvy, mul_zero, Finset.sum_const_zero, sub_zero] at this
      rw [hc]
      exact this)
  have hsu : s u = u := inj (by rw [← hcs, hue, ← hc])
  obtain ⟨w, hw⟩ := norm_unit s hs θ hθ u hu hsu
  have hwu : IsUnit w := isUnit_of_mul_isUnit_left (hw ▸ hu)
  obtain ⟨r, hr⟩ := hwu.exists_right_inv
  have hr' : s w * s r = 1 := by rw [← map_mul, hr, map_one]
  have key : r * (s r * u) = 1 := by
    linear_combination (-(r * s r)) * hw + (s w * s r) * hr + hr'
  refine ⟨r • e, L.smul_mem _ he.1, ?_, fun i => ?_⟩
  · rw [← algebraMap_smul E r, hm, hc, hm, map_mul, ← hc, hcs, ← hue, ← map_mul, ← map_mul, key,
      map_one]
  · rw [← algebraMap_smul E r, hm, (hφ e).1 he.2 i, mul_zero]

end Lattice

theorem exists_orthonormal {K : GlobalTheory.UnitLemma.UQ} (n : ℕ) (V : Type) [AddCommGroup V] [Module K.E V]
    [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E)
    (ha : ∀ y y' z, h (y + y') z = h y z + h y' z) (hm : ∀ (a : K.E) y z, h (a • y) z = a * h y z)
    (hc : ∀ y z, h z y = K.c (h y z)) (hn : Module.finrank K.E V = n) (L : Submodule K.O V)
    (hfg : L.FG) (hspan : Submodule.span K.E (L : Set V) = ⊤)
    (hdual : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ v : Fin n → V, (∀ i, v i ∈ L) ∧ ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
  have inj := IsFractionRing.injective K.O K.E
  choose f hf using K.c_int
  let s : K.O →+* K.O :=
    { toFun := f
      map_one' := inj (by rw [← hf]; simp)
      map_mul' := fun x y => inj (by simp [← hf])
      map_zero' := inj (by rw [← hf]; simp)
      map_add' := fun x y => inj (by simp [← hf]) }
  have hcs : ∀ x, (K.c : K.E →+* K.E) (algebraMap K.O K.E x) = algebraMap K.O K.E (s x) := hf
  have hs : ∀ x, s (s x) = x := fun x => inj (by rw [← hcs, ← hcs]; exact K.c_c _)
  obtain ⟨θ, θ', hθ', hθ⟩ := K.c_res
  obtain rfl : θ' = s θ := inj (by rw [← hθ', ← hcs]; rfl)
  have main : ∀ k ≤ n, ∃ v : Fin k → V, (∀ i, v i ∈ L) ∧
      ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨v, hv, hon⟩ := ih (by omega)
      obtain ⟨e, he, he1, he0⟩ := extend_family (K.c : K.E →+* K.E) s hs hcs θ hθ h ha hm hc L hfg
        hspan hdual k (by omega) v hv hon
      refine ⟨Fin.cons e v, fun i => ?_, fun i j => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using he
        · simpa using hv i
      · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simpa using he1
        · simpa [(Fin.succ_ne_zero j).symm] using he0 j
        · simp only [Fin.cons_succ, Fin.cons_zero, Fin.succ_ne_zero, if_false]
          rw [hc, he0, map_zero]
        · simpa using hon i j
  exact main n le_rfl

end GlobalTheory.InvolutionTraceUnit
