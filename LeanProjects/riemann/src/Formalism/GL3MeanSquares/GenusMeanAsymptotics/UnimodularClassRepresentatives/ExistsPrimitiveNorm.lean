import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormRepresentation

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

structure IsLatIn (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (M : AddSubgroup V) : Prop where
  le : ∀ m ∈ M, m ∈ W
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  span : ∀ x ∈ W, ∃ t : K, t ≠ 0 ∧ t • x ∈ M

structure IsSD (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (M : AddSubgroup V) : Prop extends IsLatIn S h W M where
  dual : ∀ x ∈ W, (∀ m ∈ M, h m x ∈ S) → x ∈ M

structure IsASD (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (M : AddSubgroup V) (z : V) : Prop extends IsLatIn S h W M where
  z_mem : z ∈ M
  z_norm : IsUnitIn S (h z z * π⁻¹)
  z_rad : ∀ m ∈ M, Dv S π (h z m)
  dual : ∀ x ∈ W, h z x = 0 → (∀ m ∈ M, h m x ∈ S) → x ∈ M

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem exists_primitive (hS : IsHermSemilocal S) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l • ξ ∈ M ∧ ∀ c : K, c • ξ ∈ M → c * l⁻¹ ∈ S := by
  obtain ⟨t, ht0, htM⟩ := hM.span ξ hξ
  have hξξ : h ξ ξ ≠ 0 := fun h0 => hξ0 (hd ξ h0)
  let A : AddSubgroup K :=
    { carrier := {c | c • ξ ∈ M}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_smul] at *
        exact M.add_mem ha hb
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_smul]; exact M.zero_mem
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, neg_smul] at *
        exact M.neg_mem ha }
  have hA : ∀ c, c ∈ A ↔ c • ξ ∈ M := fun c => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun s hs a ha => (hA _).2 (by rw [mul_smul]; exact hM.smul_mem s hs _ ((hA a).1 ha)))
    ⟨t, (hA t).2 htM, ht0⟩
    ⟨star t * h ξ ξ, mul_ne_zero (star_ne_zero.2 ht0) hξξ, fun a ha => by
      have h1 := hM.int _ htM _ ((hA a).1 ha)
      simp only [LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply, smul_eq_mul] at h1
      convert h1 using 1
      ring⟩
  exact ⟨α, hα0, (hA α).1 hαA, fun c hc => hα c ((hA c).2 hc)⟩

theorem not_inv_mem (hπ : IsUnif S π) : π⁻¹ ∉ S := by
  intro hinv
  refine unit_not_dv hπ ⟨hπ.ne, hπ.mem, hinv⟩ ?_
  show π * π⁻¹ ∈ S
  rw [mul_inv_cancel₀ hπ.ne]
  exact S.one_mem

theorem exists_primitive_norm (hS : IsHermSemilocal S) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K} (hu : IsUnitIn S u) (hξu : h ξ ξ = u) :
    ∃ y ∈ M, y ≠ 0 ∧ (∃ l : K, y = l • ξ) ∧ (∀ c : K, c • y ∈ M → c ∈ S) ∧
      ∃ a ∈ S, h y y = star a * a * u := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hu.1
    rw [← hξu]
    simp
  obtain ⟨l, hl0, hlM, hl⟩ := exists_primitive hS hd hM hξ hξ0
  have hyy : h (l • ξ) (l • ξ) = star l * l * u := by
    simp only [LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply, smul_eq_mul, hξu]
    ring
  have hN : star l * l ∈ S := by
    have h1 := hM.int _ hlM _ hlM
    rw [hyy] at h1
    have h2 := S.mul_mem h1 hu.2.2
    rwa [mul_assoc, mul_inv_cancel₀ hu.1, mul_one] at h2
  obtain ⟨b, hb1, hbS⟩ := WA.exists_norm_one_mul_mem hS hN
  refine ⟨l • ξ, hlM, smul_ne_zero hl0 hξ0, ⟨l, rfl⟩, fun c hc => ?_, l * b, hbS, ?_⟩
  · have h1 := hl (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at h1
  · rw [hyy, star_mul]
    calc star l * l * u = star l * l * (star b * b) * u := by rw [hb1, mul_one]
      _ = star b * star l * (l * b) * u := by ring

theorem IsSD.exists_not_dv (hπ : IsUnif S π) (hM : IsSD S h W M) {y : V} (hy : y ∈ M)
    (hprim : ∀ c : K, c • y ∈ M → c ∈ S) : ∃ w ∈ M, ¬ Dv S π (h w y) := by
  by_contra hcon
  push_neg at hcon
  have hmem : π⁻¹ • y ∈ M := hM.dual _ (W.smul_mem _ (hM.le y hy)) (fun m hm => by
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hcon m hm)
  exact not_inv_mem hπ (hprim _ hmem)

private theorem star_apply_eq_apply_swap_of_isSymm' (hs : h.IsSymm) (x y : V) : star (h x y) = h y x := by
  have h1 := hs.eq x y
  rwa [starRingEnd_apply] at h1

theorem IsSD.exists_norm (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, _, ⟨l, rfl⟩, hprim, a, ha, hyy⟩ :=
    exists_primitive_norm hS hd hM.toIsLatIn hξ hu hξu
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hy hprim
  have huf : star u = u := by rw [← hξu]; exact star_apply_eq_apply_swap_of_isSymm' hs ξ ξ
  exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn

theorem IsSD.exists_unit_norm (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨l, hl0, hlM, hl⟩ := exists_primitive hS hd hM.toIsLatIn hξ hξ0
  have hprim : ∀ c : K, c • (l • ξ) ∈ M → c ∈ S := fun c hc => by
    have h1 := hl (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at h1
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hlM hprim
  exact Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw hn

theorem IsASD.exists_unit_norm (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) {z : V} (hM : IsASD S π h W M z) {ξ : V} (hξ : ξ ∈ W)
    (hξ0 : ξ ≠ 0) (hzξ : h z ξ = 0) : ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨l, hl0, hlM, hl⟩ := exists_primitive hS hd hM.toIsLatIn hξ hξ0
  by_cases hex : ∃ w ∈ M, ¬ Dv S π (h w (l • ξ))
  · obtain ⟨w, hw, hn⟩ := hex
    exact Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw hn
  · push_neg at hex
    exfalso
    have hmem : π⁻¹ • (l • ξ) ∈ M := hM.dual _ (W.smul_mem _ (W.smul_mem _ hξ))
      (by rw [map_smul, map_smul, hzξ, smul_zero, smul_zero])
      (fun m hm => by
        rw [map_smul, smul_eq_mul, mul_comm]
        exact hex m hm)
    have h1 := hl (π⁻¹ * l) (by rwa [mul_smul])
    rw [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at h1
    exact not_inv_mem hπ h1

theorem IsASD.z_norm_ne {z : V} (hM : IsASD S π h W M z) : h z z ≠ 0 :=
  fun h0 => hM.z_norm.1 (by rw [h0, zero_mul])

theorem mul_inv_mem_of_dv (hπ : IsUnif S π) {a b : K} (ha : Dv S π a)
    (hb : IsUnitIn S (b * π⁻¹)) : a * b⁻¹ ∈ S := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb.1 (zero_mul _)
  have e : a * b⁻¹ = (a * π⁻¹) * (b * π⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv]
    field_simp [hπ.ne]
  rw [e]
  exact S.mul_mem ha hb.2.2

theorem IsASD.decomp (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {z : V}
    (hM : IsASD S π h W M z) {y : V} (hy : y ∈ M) (hall : ∀ w ∈ M, Dv S π (h w y)) :
    ∃ n₀ ∈ M, ∃ t ∈ S, h z n₀ = 0 ∧ y = π • n₀ + t • z := by
  have hzz : h z z ≠ 0 := hM.z_norm_ne
  have htS : h z y * (h z z)⁻¹ ∈ S := mul_inv_mem_of_dv hπ (hall z hM.z_mem) hM.z_norm
  have hzn : h z (π⁻¹ • (y - (h z y * (h z z)⁻¹) • z)) = 0 := by
    simp only [map_smul, map_sub, smul_eq_mul]
    rw [mul_assoc (h z y), inv_mul_cancel₀ hzz, mul_one, sub_self, mul_zero]
  refine ⟨π⁻¹ • (y - (h z y * (h z z)⁻¹) • z), ?_, h z y * (h z z)⁻¹, htS, hzn, ?_⟩
  · refine hM.dual _ (W.smul_mem _ (W.sub_mem (hM.le y hy) (W.smul_mem _ (hM.le z hM.z_mem))))
      hzn ?_
    intro m hm
    have h1 : h m y * π⁻¹ ∈ S := hall m hm
    have h2 : h m z * π⁻¹ ∈ S := by
      have h3 := Dv.star hS hπ (hM.z_rad m hm)
      rw [star_apply_eq_apply_swap_of_isSymm' hs] at h3
      exact h3
    have e : h m (π⁻¹ • (y - (h z y * (h z z)⁻¹) • z)) =
        h m y * π⁻¹ - (h z y * (h z z)⁻¹) * (h m z * π⁻¹) := by
      simp only [map_smul, map_sub, smul_eq_mul]
      ring
    rw [e]
    exact S.sub_mem h1 (S.mul_mem htS h2)
  · rw [smul_smul, mul_inv_cancel₀ hπ.ne, one_smul, sub_add_cancel]

theorem isUnitIn_of_coprime (hS : IsHermSemilocal S) (hπ : IsUnif S π) {t : K} (ht : t ∈ S)
    (hc : ∀ d : K, d ≠ 0 → t * d⁻¹ ∈ S → π * d⁻¹ ∈ S → d⁻¹ ∈ S) : IsUnitIn S t := by
  let A : AddSubgroup K :=
    { carrier := {x | ∃ s ∈ S, ∃ r ∈ S, x = s * t + r * π}
      add_mem' := by
        rintro _ _ ⟨s, hs, r, hr, rfl⟩ ⟨s', hs', r', hr', rfl⟩
        exact ⟨s + s', S.add_mem hs hs', r + r', S.add_mem hr hr', by ring⟩
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by ring⟩
      neg_mem' := by
        rintro _ ⟨s, hs, r, hr, rfl⟩
        exact ⟨-s, S.neg_mem hs, -r, S.neg_mem hr, by ring⟩ }
  have hAm : ∀ x, x ∈ A ↔ ∃ s ∈ S, ∃ r ∈ S, x = s * t + r * π := fun x => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun c hc' a ha => by
      obtain ⟨s, hs, r, hr, rfl⟩ := (hAm a).1 ha
      exact (hAm _).2 ⟨c * s, S.mul_mem hc' hs, c * r, S.mul_mem hc' hr, by ring⟩)
    ⟨π, (hAm π).2 ⟨0, S.zero_mem, 1, S.one_mem, by ring⟩, hπ.ne⟩
    ⟨1, one_ne_zero, fun a ha => by
      obtain ⟨s, hs, r, hr, rfl⟩ := (hAm a).1 ha
      rw [one_mul]
      exact S.add_mem (S.mul_mem hs ht) (S.mul_mem hr hπ.mem)⟩
  have htα := hα t ((hAm t).2 ⟨1, S.one_mem, 0, S.zero_mem, by ring⟩)
  have hπα := hα π ((hAm π).2 ⟨0, S.zero_mem, 1, S.one_mem, by ring⟩)
  have hαinv : α⁻¹ ∈ S := hc α hα0 htα hπα
  obtain ⟨s, hs, r, hr, hαe⟩ := (hAm α).1 hαA
  have hunit : IsUnitIn S (1 + π * (-(r * α⁻¹))) := hπ.rad _ (S.neg_mem (S.mul_mem hr hαinv))
  have he : s * t * α⁻¹ = 1 + π * (-(r * α⁻¹)) := by
    have h1 : (s * t + r * π) * α⁻¹ = 1 := by rw [← hαe, mul_inv_cancel₀ hα0]
    linear_combination h1
  rw [← he] at hunit
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hunit.1 (by ring)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hunit.1 (by ring)
  refine ⟨ht0, ht, ?_⟩
  have e : t⁻¹ = s * α⁻¹ * (s * t * α⁻¹)⁻¹ := by
    field_simp
  rw [e]
  exact S.mul_mem (S.mul_mem hs hαinv) hunit.2.2

theorem IsASD.exists_norm (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) {z : V} (hM : IsASD S π h W M z) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) {w₀ : V} (hw₀ : w₀ ∈ M)
    (hw₀u : IsUnitIn S (h w₀ w₀)) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, _, _, hprim, a, ha, hyy⟩ := exists_primitive_norm hS hd hM.toIsLatIn hξ hu hξu
  have huf : star u = u := by rw [← hξu]; exact star_apply_eq_apply_swap_of_isSymm' hs ξ ξ
  by_cases hex : ∃ w ∈ M, ¬ Dv S π (h w y)
  · obtain ⟨w, hw, hn⟩ := hex
    exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn
  push_neg at hex
  obtain ⟨n₀, hn₀, t, ht, hzn, hye⟩ := hM.decomp hS hπ hs hy hex
  have htu : IsUnitIn S t := isUnitIn_of_coprime hS hπ ht (fun d _ htd hπd => hprim d⁻¹ (by
    rw [hye, smul_add, smul_smul, smul_smul]
    exact M.add_mem (hM.smul_mem _ (by rwa [mul_comm]) _ hn₀)
      (hM.smul_mem _ (by rwa [mul_comm]) _ hM.z_mem)))
  have hnz : h n₀ z = 0 := by rw [← star_apply_eq_apply_swap_of_isSymm' hs z n₀, hzn, star_zero]
  have hexp : h y y = π * π * h n₀ n₀ + star t * t * h z z := by
    rw [hye]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply,
      smul_eq_mul, hzn, hnz, hπ.fix]
    ring
  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ hπ.ne
  have hyyU : IsUnitIn S (h y y * π⁻¹) := by
    have e : h y y * π⁻¹ = star t * t * (h z z * π⁻¹) + π * h n₀ n₀ := by
      linear_combination π⁻¹ * hexp + (π * h n₀ n₀) * hpi
    rw [e]
    exact unit_add_dv hπ (unit_mul (unit_mul (unit_star hS htu) htu) hM.z_norm)
      (dv_self_mul hπ (hM.int _ hn₀ _ hn₀))
  have hna : ¬ Dv S π a := by
    intro hda
    obtain ⟨r, hr, rfl⟩ := Dv.eq hπ hda
    have e : h y y * π⁻¹ = π * (star r * r * u) := by
      rw [hyy, star_mul, hπ.fix]
      linear_combination (π * star r * r * u) * hpi
    refine unit_not_dv hπ hyyU ?_
    rw [e]
    exact dv_self_mul hπ (S.mul_mem (S.mul_mem (hS.star_mem r hr) hr) hu.2.1)
  have hN : Dv S π (star a * a) := by
    have huinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.1
    have e : star a * a * π⁻¹ = (h y y * π⁻¹) * u⁻¹ := by
      rw [hyy]
      linear_combination (-(star a * a * π⁻¹)) * huinv
    show star a * a * π⁻¹ ∈ S
    rw [e]
    exact S.mul_mem hyyU.2.1 hu.2.2
  have hyy0 : h y y ≠ 0 := fun h0 => hyyU.1 (by rw [h0, zero_mul])
  have hdv : Dv S π (h y w₀) := by
    have h1 := Dv.star hS hπ (hex w₀ hw₀)
    rw [star_apply_eq_apply_swap_of_isSymm' hs] at h1
    exact h1
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = h y w₀ * (h y y)⁻¹ := ⟨_, rfl⟩
  have hcS : c ∈ S := by rw [hcdef]; exact mul_inv_mem_of_dv hπ hdv hyyU
  have hsc : star c = h w₀ y * (h y y)⁻¹ := by
    rw [hcdef, star_mul, star_inv₀, star_apply_eq_apply_swap_of_isSymm' hs, star_apply_eq_apply_swap_of_isSymm' hs, mul_comm]
  have hwM : w₀ - c • y ∈ M := M.sub_mem hw₀ (hM.smul_mem c hcS y hy)
  have hwy : h (w₀ - c • y) y = 0 := by
    simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, starRingEnd_apply,
      smul_eq_mul]
    rw [hsc, mul_assoc, inv_mul_cancel₀ hyy0, mul_one, sub_self]
  have hsc_mul : star c * h y y = h w₀ y := by
    rw [hsc, mul_assoc, inv_mul_cancel₀ hyy0, mul_one]
  have hscS : star c ∈ S := by rw [hsc]; exact mul_inv_mem_of_dv hπ (hex w₀ hw₀) hyyU
  have hww : h (w₀ - c • y) (w₀ - c • y) = h w₀ w₀ + (-(star c * h y w₀)) := by
    simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply,
      smul_eq_mul]
    rw [hsc_mul]
    ring
  have hwwU : IsUnitIn S (h (w₀ - c • y) (w₀ - c • y)) := by
    rw [hww]
    refine unit_add_dv hπ hw₀u ?_
    show -(star c * h y w₀) * π⁻¹ ∈ S
    rw [show -(star c * h y w₀) * π⁻¹ = -(star c * (h y w₀ * π⁻¹)) by ring]
    exact S.neg_mem (S.mul_mem hscS hdv)
  exact exists_norm_of_orth hS hπ hs hM.smul_mem hy hwM ha hu huf hyy hna hN hwy hwwU

end Formalism.HermitianLattices.Ext.L3.U0
