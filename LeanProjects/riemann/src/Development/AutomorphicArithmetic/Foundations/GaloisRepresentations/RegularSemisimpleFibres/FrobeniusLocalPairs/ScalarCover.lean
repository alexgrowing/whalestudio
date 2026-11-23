import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt

open ValuativeRel UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.InertialTypesAlt.L

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem val_of_near {r : ValueGroupWithZero E} (h1 : r < 1) {x a : E} (hx : valuation E x = 1)
    (h : valuation E (x - a) ≤ r) : valuation E a = 1 := by
  have h2 : valuation E (x - a) < valuation E x := by
    rw [hx]
    exact lt_of_le_of_lt h h1
  have h3 := (valuation E).map_sub_eq_of_lt_left h2
  rwa [sub_sub_cancel, hx] at h3

private theorem units_cover (r : ValueGroupWithZero E) (h0 : 0 < r) (h1 : r < 1) :
    ∃ W : Finset Eˣ, ∀ x : Eˣ, valuation E (x : E) = 1 →
      ∃ t ∈ W, ∃ s : Eˣ, valuation E ((s : E) - 1) ≤ r ∧ x = t * s := by
  classical
  have hK := IsNonarchimedeanLocalField.isCompact_closedBall E 1
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun c => {y | valuation E (y - c) < r})
    (fun c _ => (IsValuativeTopology.hasBasis_nhds' c).mem_of_mem h0.ne')
  let f : E → Eˣ := fun c => if hc : c = 0 then 1 else Units.mk0 c hc
  refine ⟨t.image f, fun x hx => ?_⟩
  have hxm : (x : E) ∈ {y : E | valuation E y ≤ 1} := by simp [hx]
  obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.mp (ht hxm)
  have hc' : valuation E ((x : E) - c) < r := hc
  have hvc : valuation E c = 1 := val_of_near h1 hx hc'.le
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hvc
    exact zero_ne_one hvc
  have hfc : f c = Units.mk0 c hc0 := dif_neg hc0
  refine ⟨f c, Finset.mem_image_of_mem f hct, (f c)⁻¹ * x, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [hfc]
  have e : (((Units.mk0 c hc0)⁻¹ * x : Eˣ) : E) - 1 = c⁻¹ * ((x : E) - c) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [mul_sub, inv_mul_cancel₀ hc0]
  rw [e, map_mul, map_inv₀, hvc, inv_one, one_mul]
  exact hc'.le

private theorem iter_val (σ : E ≃+* E) (j : ℕ) (x : Eˣ) :
    (((Units.map (σ : E →* E))^[j] x : Eˣ) : E) = σ^[j] (x : E) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    simp [Units.coe_map]

private theorem iter_isom {σ : E ≃+* E} (hσ : Isom σ) (j : ℕ) (x : E) : valuation E (σ^[j] x) = valuation E x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, hσ]

private theorem scalar_cover {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) (r : ValueGroupWithZero E) (h0 : 0 < r) (h1 : r < 1) :
    ∃ T : Finset Eˣ, ∀ x : Eˣ, ∃ t ∈ T, ∃ p s : Eˣ, Units.map (σ : E →* E) p = p ∧
      valuation E ((s : E) - 1) ≤ r ∧ x = t * p * s := by
  classical
  obtain ⟨W, hW⟩ := units_cover r h0 h1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero E)ˣ)
  obtain ⟨π, hπ⟩ := ValuativeRel.valuation_surjective (g : ValueGroupWithZero E)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact g.ne_zero hπ.symm
  obtain ⟨πu, hπu⟩ : ∃ u : Eˣ, (u : E) = π := ⟨Units.mk0 π hπ0, rfl⟩
  let V : Eˣ →* (ValueGroupWithZero E)ˣ := Units.map (valuation E).toMonoidWithZeroHom.toMonoidHom
  have hV : ∀ u : Eˣ, ((V u : (ValueGroupWithZero E)ˣ) : ValueGroupWithZero E) = valuation E (u : E) :=
    fun u => rfl
  have hq := hσ.pos
  obtain ⟨P, hP⟩ : ∃ P : Eˣ, P = ∏ j ∈ Finset.range q, (Units.map (σ : E →* E))^[j] πu := ⟨_, rfl⟩
  have hf : ∀ j, V ((Units.map (σ : E →* E))^[j] πu) = g := fun j => Units.ext (by
    rw [hV, iter_val, iter_isom hσ.isom, hπu, hπ])
  have hVP : V P = g ^ q := by
    rw [hP, map_prod]
    simp [hf]
  have key : (∏ j ∈ Finset.range q, (Units.map (σ : E →* E))^[j + 1] πu) * πu =
      (∏ j ∈ Finset.range q, (Units.map (σ : E →* E))^[j] πu) * (Units.map (σ : E →* E))^[q] πu :=
    (Finset.prod_range_succ' (fun j => (Units.map (σ : E →* E))^[j] πu) q).symm.trans
      (Finset.prod_range_succ _ q)
  have hqe : (Units.map (σ : E →* E))^[q] πu = πu := Units.ext (by rw [iter_val, hπu, hσ.ord])
  have hPfix : Units.map (σ : E →* E) P = P := by
    rw [hP, map_prod]
    simp only [← Function.iterate_succ_apply']
    exact mul_right_cancel (key.trans (by rw [hqe]))
  refine ⟨(Finset.range q ×ˢ W).image (fun it => πu ^ it.1 * it.2), fun x => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (V x))
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = m % q :=
    ⟨(m % q).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')⟩
  have hiq : i < q := by
    have := Int.emod_lt_of_pos m hq0
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = m / q := ⟨_, rfl⟩
  have hm' : m = (i : ℤ) + q * k := by
    rw [hi, hk]
    have := Int.mul_ediv_add_emod m q
    linarith
  obtain ⟨y, hy⟩ : ∃ y : Eˣ, y = x * (πu ^ i)⁻¹ * (P ^ k)⁻¹ := ⟨_, rfl⟩
  have hVπ : V πu = g := hf 0
  have hVy : V y = 1 := by
    rw [hy, map_mul, map_mul, map_inv, map_inv, map_pow, map_zpow, hVπ, hVP, ← hm, hm']
    group
  have hvy : valuation E (y : E) = 1 := by
    rw [← hV, hVy, Units.val_one]
  obtain ⟨t, ht, s, hs, hyts⟩ := hW y hvy
  refine ⟨πu ^ i * t, Finset.mem_image.mpr ⟨(i, t), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hiq, ht⟩, rfl⟩, P ^ k, s, by rw [map_zpow, hPfix], hs, ?_⟩
  have hx : x = y * P ^ k * πu ^ i := by
    rw [hy]
    simp
  rw [hx, hyts]
  ac_rfl

private theorem near_scalar {r : ValueGroupWithZero E} (h1 : r < 1) {a b : Eˣ} (ha : valuation E ((a : E) - 1) ≤ r)
    (hb : valuation E ((b : E) - 1) ≤ r) :
    valuation E (((a * b : Eˣ) : E) - 1) ≤ r ∧ valuation E (((a⁻¹ : Eˣ) : E) - 1) ≤ r := by
  have hva : valuation E (a : E) = 1 :=
    val_of_near h1 (x := 1) (by simp) (by rw [Valuation.map_sub_swap]; exact ha)
  constructor
  · have e : ((a * b : Eˣ) : E) - 1 = (a : E) * ((b : E) - 1) + ((a : E) - 1) := by
      push_cast
      ring
    rw [e]
    refine (valuation E).map_add_le ?_ ha
    rw [map_mul, hva, one_mul]
    exact hb
  · have e : ((a⁻¹ : Eˣ) : E) - 1 = ((a⁻¹ : Eˣ) : E) * (1 - (a : E)) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    have hvi : valuation E ((a⁻¹ : Eˣ) : E) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hva, inv_one]
    rw [e, map_mul, Valuation.map_sub_swap, hvi, one_mul]
    exact ha

private theorem near_mul {r : ValueGroupWithZero E} (h1 : r < 1) {a b : Fin n → Eˣ} (ha : Near r a) (hb : Near r b) :
    Near r (a * b) := fun i => (near_scalar h1 (ha i) (hb i)).1

private theorem near_inv {r : ValueGroupWithZero E} (h1 : r < 1) {a : Fin n → Eˣ} (ha : Near r a) : Near r a⁻¹ :=
  fun i => (near_scalar h1 (ha i) (ha i)).2

private theorem near_one (r : ValueGroupWithZero E) : Near r (1 : Fin n → Eˣ) := fun i => by simp

private theorem near_sg {σ : E ≃+* E} (hσ : Isom σ) {r : ValueGroupWithZero E} {a : Fin n → Eˣ} (ha : Near r a) :
    Near r (sgT σ a) := fun i => by
  have h := hσ ((a i : E) - 1)
  rw [map_sub, map_one] at h
  simpa [sgT, h] using ha i

private theorem sgT_mul (σ : E ≃+* E) (a b : Fin n → Eˣ) : sgT σ (a * b) = sgT σ a * sgT σ b := by
  funext i
  simp [sgT]

private theorem sgT_inv (σ : E ≃+* E) (a : Fin n → Eˣ) : sgT σ a⁻¹ = (sgT σ a)⁻¹ := by
  funext i
  simp [sgT]

private theorem sgT_one (σ : E ≃+* E) : sgT σ (1 : Fin n → Eˣ) = 1 := by
  funext i
  simp [sgT]

private def fixNear (σ : E ≃+* E) (r : ValueGroupWithZero E) (h1 : r < 1) : Subgroup (Fin n → Eˣ) where
  carrier := {m | ∃ p s, sgT σ p = p ∧ Near r s ∧ m = p * s}
  one_mem' := ⟨1, 1, sgT_one σ, near_one r, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨p, s, hp, hs, rfl⟩ ⟨p', s', hp', hs', rfl⟩
    exact ⟨p * p', s * s', by rw [sgT_mul, hp, hp'], near_mul h1 hs hs', mul_mul_mul_comm ..⟩
  inv_mem' := by
    rintro _ ⟨p, s, hp, hs, rfl⟩
    exact ⟨p⁻¹, s⁻¹, by rw [sgT_inv, hp], near_inv h1 hs, mul_inv _ _⟩

private theorem rel_iff {σ : E ≃+* E} {r : ValueGroupWithZero E} (h1 : r < 1) {u ρ : Fin n → Eˣ} :
    Rel σ r u ρ ↔ ρ⁻¹ * u ∈ fixNear σ r h1 := by
  show (∃ p s, sgT σ p = p ∧ Near r s ∧ u = ρ * p * s) ↔
    ∃ p s, sgT σ p = p ∧ Near r s ∧ ρ⁻¹ * u = p * s
  constructor
  · rintro ⟨p, s, hp, hs, h⟩
    exact ⟨p, s, hp, hs, by rw [h]; group⟩
  · rintro ⟨p, s, hp, hs, h⟩
    refine ⟨p, s, hp, hs, ?_⟩
    rw [mul_assoc, ← h]
    group

private theorem fixNear_near {σ : E ≃+* E} (hσ : Isom σ) {r : ValueGroupWithZero E} (h1 : r < 1) {m : Fin n → Eˣ}
    (hm : m ∈ fixNear σ r h1) : Near r (sgT σ m / m) := by
  obtain ⟨p, s, hp, hs, rfl⟩ := hm
  rw [sgT_mul, hp, mul_div_mul_left_eq_div, div_eq_mul_inv]
  exact near_mul h1 (near_sg hσ hs) (near_inv h1 hs)

private theorem near_tw_mul {σ : E ≃+* E} (hσ : Isom σ) {r : ValueGroupWithZero E} (h1 : r < 1) {u m : Fin n → Eˣ}
    (hu : Near r (sgT σ u / u)) (hm : m ∈ fixNear σ r h1) : Near r (sgT σ (u * m) / (u * m)) := by
  rw [sgT_mul, mul_div_mul_comm]
  exact near_mul h1 hu (fixNear_near hσ h1 hm)

private theorem finite_quot {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) (r : ValueGroupWithZero E) (h0 : 0 < r) (h1 : r < 1) :
    Finite ((Fin n → Eˣ) ⧸ (fixNear σ r h1 : Subgroup (Fin n → Eˣ))) := by
  classical
  obtain ⟨T, hT⟩ := scalar_cover hσ r h0 h1
  refine Finite.of_surjective (fun t : Fin n → T =>
    (QuotientGroup.mk (fun i => (t i : Eˣ)) : (Fin n → Eˣ) ⧸ fixNear σ r h1)) ?_
  intro c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective c
  choose t ht p s hp hs hm using fun i => hT (m i)
  refine ⟨fun i => ⟨t i, ht i⟩, ?_⟩
  have hrel : Rel σ r m (fun i => t i) := by
    unfold Rel
    exact ⟨p, s, funext fun i => hp i, fun i => hs i, funext fun i => hm i⟩
  exact QuotientGroup.eq.mpr ((rel_iff h1).mp hrel)

theorem reps : Reps := by
  classical
  intro E _ _ _ _ n σ q hσ r h0 h1
  have hσi := hσ.isom
  haveI := finite_quot (n := n) hσ r h0 h1
  have hS1 : ∀ {u m : Fin n → Eˣ}, Near r (sgT σ u / u) → m ∈ fixNear σ r h1 →
      Near r (sgT σ (u * m) / (u * m)) := fun hu hm => near_tw_mul hσi h1 hu hm
  have hfin : {ρ : Fin n → Eˣ | ρ ∈ Set.range (Quotient.out : (Fin n → Eˣ) ⧸ fixNear σ r h1 → _) ∧
      Near r (sgT σ ρ / ρ)}.Finite := (Set.finite_range _).subset (fun ρ h => h.1)
  have hout : ∀ u : Fin n → Eˣ,
      u⁻¹ * Quotient.out (QuotientGroup.mk u : (Fin n → Eˣ) ⧸ fixNear σ r h1) ∈ fixNear σ r h1 :=
    fun u => QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have hout' : ∀ u : Fin n → Eˣ,
      (Quotient.out (QuotientGroup.mk u : (Fin n → Eˣ) ⧸ fixNear σ r h1))⁻¹ * u ∈ fixNear σ r h1 :=
    fun u => QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
  have hS_out : ∀ u : Fin n → Eˣ, Near r (sgT σ u / u) →
      Near r (sgT σ (Quotient.out (QuotientGroup.mk u : (Fin n → Eˣ) ⧸ fixNear σ r h1)) /
        Quotient.out (QuotientGroup.mk u : (Fin n → Eˣ) ⧸ fixNear σ r h1)) := fun u hu => by
    have h := hS1 hu (hout u)
    rw [mul_inv_cancel_left] at h
    exact h
  refine ⟨hfin.toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Quotient.out (QuotientGroup.mk 1 : (Fin n → Eˣ) ⧸ fixNear σ r h1),
      hfin.mem_toFinset.mpr ⟨⟨_, rfl⟩, hS_out 1 ?_⟩⟩
    rw [sgT_one, div_one]
    exact near_one r
  · intro u
    constructor
    · intro hu
      exact ⟨_, hfin.mem_toFinset.mpr ⟨⟨_, rfl⟩, hS_out u hu⟩, (rel_iff h1).mpr (hout' u)⟩
    · rintro ⟨ρ, hρ, hr⟩
      have h := hS1 (hfin.mem_toFinset.mp hρ).2 ((rel_iff h1).mp hr)
      rw [mul_inv_cancel_left] at h
      exact h
  · intro ρ hρ ρ' hρ' hr
    obtain ⟨⟨c, rfl⟩, -⟩ := hfin.mem_toFinset.mp hρ
    obtain ⟨⟨c', rfl⟩, -⟩ := hfin.mem_toFinset.mp hρ'
    have h := QuotientGroup.eq.mpr ((rel_iff h1).mp hr)
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro a b ha hb
    exact ⟨near_mul h1 ha hb, near_inv h1 ha⟩
  · intro z u ρ
    rw [rel_iff h1, rel_iff h1]
    have e : (z * ρ)⁻¹ * (z * u) = ρ⁻¹ * u := by group
    rw [e]

end UpperTheory.Gal.InertialTypesAlt.L
