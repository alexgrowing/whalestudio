import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

theorem valuation_eq_iff_ord {x y : kˣ} : valuation k (x : k) = valuation k (y : k) ↔ ord k x = ord k y := by
  rw [le_antisymm_iff, valuation_le_iff_ord, valuation_le_iff_ord]; omega

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

theorem valuation_of_shell {c r : kˣ} {a : ℕ} (hr : ord k r = ord k c - a) :
    valuation k (c : k) = uniformizer k ^ a * valuation k (r : k) := by
  obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
  rw [← hp, ← map_mul, ← Units.val_mul, valuation_eq_iff_ord, ord_mul]; omega

theorem exists_shell (c : kˣ) (a : ℕ) : ∃ d : kˣ, ord k d = ord k c - a := by
  obtain ⟨p, -, hp'⟩ := exists_unit_pow k a
  refine ⟨c * p⁻¹, ?_⟩
  have := ord_mul k (c * p⁻¹) p
  rw [inv_mul_cancel_right] at this
  omega

theorem exists_hasExponent {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) : ∃ a, HasExponent χ a := by
  classical
  have h : ∃ a, ∀ x ∈ unitFilt k a, χ x = 1 := by
    obtain ⟨V, hV, hV'⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.1 hχ
    have h1 : (1 : k) ∈ V := by
      have : (1 : kˣ) ∈ Units.val ⁻¹' V := by rw [hV']; exact χ.ker.one_mem
      simpa using this
    have h2 : (fun z : k => z + 1) ⁻¹' V ∈ 𝓝 (0 : k) :=
      (hV.preimage (by fun_prop)).mem_nhds (by simpa using h1)
    obtain ⟨s, hs⟩ := exists_cball_subset h2
    obtain ⟨p, hp, hp'⟩ := exists_unit_pow k (ord k s).toNat
    refine ⟨(ord k s).toNat, fun x hx => ?_⟩
    have h3 : (x : k) - 1 ∈ cball s :=
      hx.2.trans (show _ ≤ valuation k (s : k) by rw [← hp, valuation_le_iff_ord]; omega)
    have h4 : x ∈ Units.val ⁻¹' V := by simpa using hs h3
    rw [hV'] at h4
    exact h4
  refine ⟨Nat.find h, Nat.find_spec h, fun b hb => ?_⟩
  have := Nat.find_min h hb
  push Not at this
  exact this

theorem exists_isShellReps (c : kˣ) (a : ℕ) : ∃ R, IsShellReps c a R := by
  classical
  obtain ⟨d, hd⟩ := exists_shell c a
  let B : AddSubgroup k :=
    { carrier := cball c
      add_mem' := add_mem_cball
      zero_mem' := by simp [cball]
      neg_mem' := neg_mem_cball }
  have : DiscreteTopology (k ⧸ B) := QuotientAddGroup.discreteTopology (isOpen_cball c)
  let S : Set kˣ := {y | ord k y = ord k c - a}
  let q : kˣ → k ⧸ B := fun y => QuotientAddGroup.mk (y : k)
  have hq : ∀ y r : kˣ, q r = q y ↔ valuation k ((y : k) - r) ≤ valuation k (c : k) := fun y r => by
    simp only [q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]; rfl
  have hfin : (q '' S).Finite := by
    refine (((isCompact_cball d).image QuotientAddGroup.continuous_mk).finite_of_discrete).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, (valuation_eq_iff_ord.2 (hy.trans hd.symm)).le, rfl⟩
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_bijOn S q
  have hTfin : T.Finite := Set.Finite.of_finite_image (hT.image_eq ▸ hfin) hT.injOn
  refine ⟨hTfin.toFinset, fun r hr => hTS (by simpa using hr), fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hT.surjOn ⟨y, hy, rfl⟩
  refine ⟨r, ⟨by simpa using hr, (hq y r).1 hry⟩, fun r' hr' => ?_⟩
  exact hT.injOn (by simpa using hr'.1) hr (((hq y r').2 hr'.2).trans hry.symm)

theorem IsShellReps.sum_eq {c : kˣ} {a : ℕ} {R R' : Finset kˣ} (h : IsShellReps c a R) (h' : IsShellReps c a R')
    {g : kˣ → ℂ} (hg : ∀ y r : kˣ, ord k y = ord k c - a → ord k r = ord k c - a →
      valuation k ((y : k) - r) ≤ valuation k (c : k) → g y = g r) :
    ∑ r ∈ R, g r = ∑ r ∈ R', g r := by
  choose i hi hi' using fun r hr => h'.2 r (h.1 r hr)
  refine Finset.sum_bij i (fun r hr => (hi r hr).1) (fun r₁ h₁ r₂ h₂ e => ?_) (fun r' hr' => ?_)
    (fun r hr => hg _ _ (h.1 r hr) (h'.1 _ (hi r hr).1) (hi r hr).2)
  · refine (h.2 _ (h'.1 _ (hi r₁ h₁).1)).unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · rw [Valuation.map_sub_swap]; exact (hi r₁ h₁).2
    · rw [Valuation.map_sub_swap, e]; exact (hi r₂ h₂).2
  · obtain ⟨r, hr, -⟩ := h.2 r' (h'.1 r' hr')
    exact ⟨r, hr.1, (hi' r hr.1 r' ⟨hr', by rw [Valuation.map_sub_swap]; exact hr.2⟩).symm⟩

open Classical in

theorem IsShellReps.image_mul {c : kˣ} {a : ℕ} {R : Finset kˣ} (h : IsShellReps c a R) {u : kˣ}
    (hu : valuation k (u : k) = 1) : IsShellReps c a (R.image (u * ·)) := by
  have h0 := ord_eq_zero hu
  refine ⟨fun r hr => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
    rw [ord_mul, h0, zero_add, h.1 s hs]
  · have h1 : ord k (u⁻¹ * y) = ord k c - a := by
      have := ord_mul k u (u⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      omega
    have h2 : ∀ r : kˣ, valuation k ((y : k) - (u * r : kˣ)) = valuation k (((u⁻¹ * y : kˣ) : k) - r) := fun r => by
      have : (y : k) - (u * r : kˣ) = u * (((u⁻¹ * y : kˣ) : k) - r) := by simp [mul_sub]
      rw [this, map_mul, hu, one_mul]
    obtain ⟨r, hr, hr'⟩ := h.2 _ h1
    refine ⟨u * r, ⟨Finset.mem_image_of_mem _ hr.1, (h2 r).trans_le hr.2⟩, ?_⟩
    rintro _ ⟨hm, hv⟩
    obtain ⟨r', hm', rfl⟩ := Finset.mem_image.1 hm
    rw [hr' r' ⟨hm', (h2 r').symm.trans_le hv⟩]

variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

theorem addChar_eq_of_sub (hψ : HasConductor ψ c) {y z : k} (h : valuation k (y - z) ≤ valuation k (c : k)) :
    ψ y = ψ z := by
  have : y = z + (y - z) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.eq_one h, mul_one]

theorem gaussTerm_eq (hψ : HasConductor ψ c) (hχ : HasExponent χ a) {x : k} (hx : valuation k x ≤ 1) (y r : kˣ)
    (hy : ord k y = ord k c - a) (hr : ord k r = ord k c - a)
    (h : valuation k ((y : k) - r) ≤ valuation k (c : k)) :
    (((χ y)⁻¹ : ℂˣ) : ℂ) * (ψ (x * y) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  have h1 : ψ (x * y) = ψ (x * r) := addChar_eq_of_sub hψ (by
    rw [← mul_sub, map_mul]
    exact (mul_le_mul' hx h).trans_eq (one_mul _))
  have hr0 : 0 < valuation k (r : k) := by simp [zero_lt_iff]
  have h2 : χ (y * r⁻¹) = 1 := hχ.1 _ ⟨by
    rw [Units.val_mul, map_mul, valuation_eq_iff_ord.2 (hy.trans hr.symm), ← map_mul]; simp, by
    have : ((y * r⁻¹ : kˣ) : k) - 1 = ((y : k) - r) * (r : k)⁻¹ := by simp [sub_mul]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ hr0, ← valuation_of_shell hr]
    exact h⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h1, h2]

theorem gaussSum_mul_unit (hψ : HasConductor ψ c) (hχ : HasExponent χ a) (h : IsShellReps c a R) {x : k}
    (hx : valuation k x ≤ 1) {u : kˣ} (hu : valuation k (u : k) = 1) :
    ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * u * r) : ℂ) =
      χ u * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  classical
  rw [h.sum_eq (h.image_mul hu) (gaussTerm_eq hψ hχ hx),
    Finset.sum_image (fun _ _ _ _ e => mul_left_cancel e), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [map_mul, mul_inv, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]

theorem gaussSum_eq_zero (hψ : HasConductor ψ c) (hχ : HasExponent χ (a + 1)) (h : IsShellReps c (a + 1) R) {x : k}
    (hx : valuation k x < 1) : ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) = 0 := by
  obtain ⟨u, hu, hu'⟩ := hχ.2 a (Nat.lt_succ_self a)
  have h1 := gaussSum_mul_unit hψ hχ h hx.le hu.1
  have h2 : ∀ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * u * r) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
    intro r hr
    rw [addChar_eq_of_sub hψ (y := x * u * r) (z := x * r)]
    have : x * u * r - x * r = ((u : k) - 1) * x * r := by ring
    rw [this, map_mul, map_mul, valuation_of_shell (h.1 r hr), pow_succ]
    exact mul_le_mul' (mul_le_mul' hu.2 (le_uniformizer_iff.2 hx)) le_rfl
  rw [Finset.sum_congr rfl h2] at h1
  by_contra h0
  exact hu' (Units.ext (by simpa using ((mul_eq_right₀ h0).1 h1.symm)))

theorem gaussSum_ne_zero_of_ramified (hψ : HasConductor ψ c) (hχ : HasExponent χ (a + 1))
    (h : IsShellReps c (a + 1) R) : ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) ≠ 0 := by
  intro h0
  have h1 : ∀ x : k, valuation k x ≤ 1 → ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) = 0 := by
    intro x hx
    rcases hx.lt_or_eq with hx | hx
    · exact gaussSum_eq_zero hψ hχ h hx
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have := gaussSum_mul_unit hψ hχ h (x := 1) (by simp) (u := Units.mk0 x hx0) hx
      simp only [one_mul, Units.val_mk0] at this
      rw [this, h0, mul_zero]
  let φ : R → Multiplicative 𝒪[k] →* ℂ := fun r =>
    { toFun := fun x => ψ ((x.toAdd : k) * (r.1 : k))
      map_one' := by simp
      map_mul' := fun x y => by simp [add_mul, AddChar.map_add_eq_mul] }
  have hφ : Function.Injective φ := by
    intro r r' e
    refine Subtype.ext ((h.2 r (h.1 r r.2)).unique ⟨r.2, by simp⟩ ⟨r'.2, ?_⟩)
    refine (hψ _).1 fun y hy => ?_
    by_cases h2 : (r.1 : k) - r'.1 = 0
    · rw [h2, map_zero, le_zero_iff, map_eq_zero] at hy
      simp [hy]
    have h3 : valuation k (y / ((r.1 : k) - r'.1)) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hy zero_le
    have h4 : ψ (y / ((r.1 : k) - r'.1) * r.1) = ψ (y / ((r.1 : k) - r'.1) * r'.1) :=
      Circle.ext (DFunLike.congr_fun e (Multiplicative.ofAdd (⟨y / ((r.1 : k) - r'.1), h3⟩ : 𝒪[k])))
    rw [← div_mul_cancel₀ y h2, mul_sub, AddChar.map_sub_eq_div, h4, div_self']
  have hli := (linearIndependent_monoidHom (Multiplicative 𝒪[k]) ℂ).comp φ hφ
  obtain ⟨d, hd⟩ := exists_shell c (a + 1)
  obtain ⟨r, hr, -⟩ := h.2 d hd
  refine Units.ne_zero (χ r)⁻¹ (Fintype.linearIndependent_iff.1 hli (fun r => (((χ r)⁻¹ : ℂˣ) : ℂ)) ?_ ⟨r, hr.1⟩)
  funext x
  rw [Finset.sum_apply, Pi.zero_apply, ← h1 x.toAdd x.toAdd.2, ← Finset.sum_coe_sort R]
  rfl

theorem IsTateEps.unique {e e' : ℂ} (h : IsTateEps ψ χ e) (h' : IsTateEps ψ χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [IsShellReps, valuation_eq_iff_ord.1 h1, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this]

theorem IsTateEps.ne_zero {e : ℂ} (h : IsTateEps ψ χ e) : e ≠ 0 := by
  obtain ⟨c, a, R, hc, ha, hR, he⟩ := id h
  cases a with
  | zero =>
    rw [h.unique (isTateEps_of_isUnram hc (hasExponent_zero_iff.1 ha))]
    exact Units.ne_zero _
  | succ a =>
    rw [he]
    refine mul_ne_zero ?_ (gaussSum_ne_zero_of_ramified hc ha hR)
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne')

theorem existsUnique_isTateEps (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : (∃! e : ℂ, IsTateEps ψ χ e) ∧ ∀ e : ℂ, IsTateEps ψ χ e → e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨a, ha⟩ := exists_hasExponent hχ
  obtain ⟨R, hR⟩ := exists_isShellReps c a
  exact ⟨existsUnique_of_exists_of_unique ⟨_, c, a, R, hc, ha, hR, rfl⟩ fun _ _ => IsTateEps.unique,
    fun _ => IsTateEps.ne_zero⟩

end GlobalTheory.LocLanglands
