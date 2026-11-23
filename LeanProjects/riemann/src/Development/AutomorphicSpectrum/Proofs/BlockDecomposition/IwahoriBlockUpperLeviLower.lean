import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUdlOfIsUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrincipalCongruence

open Matrix

namespace GlobalTheory.CompanionTheory.BlockIwahoriUML

variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]

def Cong (v : Valuation k Γ) (r : Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i j, v (A i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r

theorem exists_udl (v : Valuation k Γ) {r : Γ} (hr : r < 1) (n : ℕ)
    (g : Matrix (Fin n) (Fin n) k) (hg : Cong v r g) :
    ∃ u d l : Matrix (Fin n) (Fin n) k, Cong v r u ∧ Cong v r l ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  classical
  let I : Ideal v.integer :=
    { carrier := {x | v (x : k) ≤ r}
      add_mem' := fun {a b} ha hb => by
        have := Valuation.map_add_le v ha hb
        simpa using this
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hc : v (c : k) ≤ 1 := c.2
        have hx' : v (x : k) ≤ r := hx
        show v ((c * x : v.integer) : k) ≤ r
        rw [Subring.coe_mul, map_mul]
        calc v (c : k) * v (x : k) ≤ 1 * r := mul_le_mul' hc hx'
          _ = r := one_mul r }
  have hImem : ∀ x : v.integer, x ∈ I ↔ v (x : k) ≤ r := fun x => Iff.rfl
  have hI : ∀ x ∈ I, IsUnit (1 + x) := by
    intro x hx
    have hx' : v (x : k) < 1 := lt_of_le_of_lt ((hImem x).1 hx) hr
    have h1 : v (1 + (x : k)) = 1 := Valuation.map_one_add_of_lt v hx'
    have h0 : (1 + (x : k)) ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (1 + (x : k))⁻¹ ∈ v.integer := by
      show v _ ≤ 1
      rw [map_inv₀, h1, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨(1 + (x : k))⁻¹, hmem⟩, Subtype.ext ?_⟩
    simpa using mul_inv_cancel₀ h0
  have hone : ∀ i j, v ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ i j, v (g i j) ≤ 1 := by
    intro i j
    have := Valuation.map_add_le v ((hg i j).trans hr.le) (hone i j)
    simpa using this
  let g' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨g i j, hint i j⟩
  have hone' : ∀ i j, (((1 : Matrix (Fin n) (Fin n) v.integer) i j : v.integer) : k) =
      (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hg' : ∀ i j, g' i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I := by
    intro i j
    rw [hImem, AddSubgroupClass.coe_sub, hone']
    exact hg i j
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := IwahoriUDL.exists_udl_of_isUnit I hI n g' hg'
  have back : ∀ a : Matrix (Fin n) (Fin n) v.integer,
      (∀ i j, a i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I) →
        Cong v r (a.map v.integer.subtype) := by
    intro a ha i j
    have := (hImem _).1 (ha i j)
    rw [AddSubgroupClass.coe_sub, hone'] at this
    exact this
  refine ⟨u.map v.integer.subtype, d.map v.integer.subtype, l.map v.integer.subtype,
    back u hu.1, back l hl.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [hu.2.1 i j hij]
  · intro i
    simp [hu.2.2 i]
  · intro i j hij
    simp [hd.2 i j hij]
  · intro i j hij
    simp [hl.2.1 i j hij]
  · intro i
    simp [hl.2.2 i]
  · have hgg : g = g'.map v.integer.subtype := by
      ext i j
      rfl
    rw [hgg, h, Matrix.map_mul, Matrix.map_mul]

theorem up_split (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (u : Matrix (Fin n) (Fin n) k) (hu : Cong v r u)
    (hu0 : ∀ i j, j < i → u i j = 0) (hu1 : ∀ i, u i i = 1) :
    ∃ a m : Matrix (Fin n) (Fin n) k, a.det = 1 ∧ m.det = 1 ∧ Cong v r a ∧ Cong v r m ∧
      (∀ i j, β j ≤ β i → a i j = (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → m i j = 0) ∧ u = a * m := by
  classical
  let m : Matrix (Fin n) (Fin n) k := fun i j => if β i = β j then u i j else 0
  have hmb : ∀ i j, β i ≠ β j → m i j = 0 := fun i j h => if_neg h
  have hmu : ∀ i j, β i = β j → m i j = u i j := fun i j h => if_pos h
  have hm0 : ∀ i j, j < i → m i j = 0 := by
    intro i j h
    by_cases hb : β i = β j
    · rw [hmu i j hb, hu0 i j h]
    · exact hmb i j hb
  have hm1 : ∀ i, m i i = 1 := fun i => by rw [hmu i i rfl, hu1]
  have hdet : ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, j < i → A i j = 0) → (∀ i, A i i = 1) →
      A.det = 1 := by
    intro A h0 h1
    rw [Matrix.det_of_upperTriangular (fun i j h => h0 i j h)]
    simp [h1]
  have hmd : m.det = 1 := hdet m hm0 hm1
  have hud : u.det = 1 := hdet u hu0 hu1
  have hmC : Cong v r m := by
    intro i j
    by_cases hb : β i = β j
    · rw [hmu i j hb]
      exact hu i j
    · have hij : i ≠ j := fun e => hb (by rw [e])
      rw [hmb i j hb, Matrix.one_apply_ne hij]
      simp
  have hmU : IsUnit m.det := by simp [hmd]
  have huU : IsUnit u.det := by simp [hud]
  haveI : Invertible m := Matrix.invertibleOfIsUnitDet m hmU
  have hmw : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hmU
  have hwm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hmU
  have hbu : BlockTriangular u β := by
    intro i j h
    refine hu0 i j ?_
    by_contra hc
    exact absurd (hβ (not_lt.1 hc)) (not_le.2 h)
  have hbm : BlockTriangular m β := fun i j h => hmb i j h.ne'
  have hbw : BlockTriangular m⁻¹ β := Matrix.blockTriangular_inv_of_blockTriangular hbm
  have hK : Cong v r (u * m⁻¹) := by
    let ug : GL (Fin n) k := Matrix.nonsingInvUnit u huU
    let mg : GL (Fin n) k := Matrix.nonsingInvUnit m hmU
    have hugK : ug ∈ PrincipalCongruence.principalCongruence v r hr := hu
    have hmgK : mg ∈ PrincipalCongruence.principalCongruence v r hr := hmC
    have hag := mul_mem hugK (inv_mem hmgK)
    have hcoe : ((ug * mg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = u * m⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv]
      rfl
    intro i j
    have := hag i j
    rwa [hcoe] at this
  refine ⟨u * m⁻¹, m, ?_, hmd, hK, hmC, ?_, hmb, ?_⟩
  · rw [Matrix.det_mul, hud, Matrix.det_nonsing_inv, hmd]
    simp
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · have hne : i ≠ j := fun e => h.ne (by rw [e])
      rw [Matrix.one_apply_ne hne]
      exact (hbu.mul hbw) h
    · have key : (u * m⁻¹) i j = (m * m⁻¹) i j := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases lt_trichotomy (β x) (β i) with hx | hx | hx
        · rw [hbu hx, hbm hx]
        · rw [hmu i x hx.symm]
        · have : m⁻¹ x j = 0 := hbw (by rw [h]; exact hx)
          rw [this, mul_zero, mul_zero]
      rw [key, hmw]
  · rw [Matrix.mul_assoc, hwm, Matrix.mul_one]

theorem cong_transpose (v : Valuation k Γ) {r : Γ} {n : ℕ} {A : Matrix (Fin n) (Fin n) k}
    (hA : Cong v r A) : Cong v r Aᵀ := by
  intro i j
  have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) j i := by
    simp [Matrix.one_apply, eq_comm]
  rw [h1, Matrix.transpose_apply]
  exact hA j i

theorem units_conj {M : Type*} [Monoid M] (p q : Mˣ) (x : M) :
    ((p⁻¹ : Mˣ) : M) * ((p : M) * x * (q : M)) * ((q⁻¹ : Mˣ) : M) = x := by
  simp [mul_assoc]

theorem blockDiag_mul {n : ℕ} (β : Fin n → ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) (hB : ∀ i j, β i ≠ β j → B i j = 0) :
    ∀ i j, β i ≠ β j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : β i = β x
  · rw [hB x j (fun e => hij (hx.trans e)), mul_zero]
  · rw [hA i x hx, zero_mul]

theorem factor (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (g : GL (Fin n) k) (hg : Cong v r (g : Matrix (Fin n) (Fin n) k)) :
    ∃ nm : GL (Fin n) k, Cong v r (nm : Matrix (Fin n) (Fin n) k) ∧
    ∃ l : GL (Fin n) k, Cong v r (l : Matrix (Fin n) (Fin n) k) ∧
    ∃ np : GL (Fin n) k, Cong v r (np : Matrix (Fin n) (Fin n) k) ∧
      (∀ i j, β i ≤ β j → (nm : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → (l : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      (∀ i j, β j ≤ β i → (np : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧ g = np * l * nm := by
  classical
  obtain ⟨u, d, t, hu, ht, hu0, hu1, hd0, ht0, ht1, hudt⟩ := exists_udl v hr n _ hg
  obtain ⟨a, m, had, hmd, haC, hmC, hab, hmb, huam⟩ := up_split v hr β hβ u hu hu0 hu1
  have htC : Cong v r tᵀ := cong_transpose v ht
  obtain ⟨b, c, hbd, hcd, hbC, hcC, hbb, hcb, htbc⟩ :=
    up_split v hr β hβ tᵀ htC (fun i j h => ht0 j i h) ht1
  have htt : t = cᵀ * bᵀ := by
    rw [← Matrix.transpose_mul, ← htbc, Matrix.transpose_transpose]
  have hbtC : Cong v r bᵀ := cong_transpose v hbC
  let npg : GL (Fin n) k := Matrix.nonsingInvUnit a (by simp [had])
  let nmg : GL (Fin n) k := Matrix.nonsingInvUnit bᵀ (by simp [hbd])
  have hnpK : npg ∈ PrincipalCongruence.principalCongruence v r hr := haC
  have hnmK : nmg ∈ PrincipalCongruence.principalCongruence v r hr := hbtC
  have hgK : g ∈ PrincipalCongruence.principalCongruence v r hr := hg
  have hlK := mul_mem (mul_mem (inv_mem hnpK) hgK) (inv_mem hnmK)
  have hprod : (g : Matrix (Fin n) (Fin n) k) =
      (npg : Matrix (Fin n) (Fin n) k) * (m * d * cᵀ) * (nmg : Matrix (Fin n) (Fin n) k) := by
    show (g : Matrix (Fin n) (Fin n) k) = a * (m * d * cᵀ) * bᵀ
    rw [hudt, huam, htt]
    simp only [Matrix.mul_assoc]
  have hlev : ((npg⁻¹ * g * nmg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = m * d * cᵀ := by
    rw [Units.val_mul, Units.val_mul, hprod]
    exact units_conj npg nmg _
  refine ⟨nmg, hnmK, npg⁻¹ * g * nmg⁻¹, hlK, npg, hnpK, ?_, ?_, hab, by group⟩
  · intro i j hij
    show bᵀ i j = _
    rw [Matrix.transpose_apply, hbb j i hij, ← Matrix.transpose_apply (1 : Matrix (Fin n) (Fin n) k) j i, Matrix.transpose_one]
  · rw [hlev]
    refine blockDiag_mul β (blockDiag_mul β hmb ?_) ?_
    · intro i j hij
      exact hd0 i j (fun e => hij (by rw [e]))
    · intro i j hij
      exact hcb j i hij.symm

theorem iwahori_block_upper_levi_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (β : Fin N → ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Monotone β → ∀ g ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ nm ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ l ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ np ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, (∀ i j, β i ≤ β j → (nm : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ (∀ i j, β i ≠ β j → (l : Matrix (Fin N) (Fin N) k) i j = 0) ∧ (∀ i j, β j ≤ β i → (np : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ g = np * l * nm := by
  intro k _ _ _ _ N ϖ m β _ hϖ _ hm hβ g hg
  have hr : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hϖ (by omega)
  exact factor (ValuativeRel.valuation k) hr β hβ g hg

end GlobalTheory.CompanionTheory.BlockIwahoriUML
