import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GordanIntegerMultiple.ExistsIntMultiple
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

set_option autoImplicit false

namespace GlobalTheory.MinkWeylReal

open Finset GordanGenProof

noncomputable def dotR {n : ℕ} (a : Fin n → ℚ) (x : Fin n → ℝ) : ℝ := ∑ i, (a i : ℝ) * x i

noncomputable def castR {n : ℕ} (w : Fin n → ℚ) : Fin n → ℝ := fun i => (w i : ℝ)

def rcone {n : ℕ} (T : Finset (Fin n → ℚ)) : Set (Fin n → ℝ) :=
  {x | ∃ c : (Fin n → ℚ) → ℝ, (∀ y ∈ T, 0 ≤ c y) ∧ x = ∑ y ∈ T, c y • castR y}

theorem dotR_castR {n : ℕ} (a w : Fin n → ℚ) : dotR a (castR w) = ((a ⬝ᵥ w : ℚ) : ℝ) := by
  simp [dotR, castR, dotProduct]

theorem dotR_smul {n : ℕ} (a : Fin n → ℚ) (r : ℝ) (x : Fin n → ℝ) : dotR a (r • x) = r * dotR a x := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotR_sub {n : ℕ} (a : Fin n → ℚ) (x y : Fin n → ℝ) : dotR a (x - y) = dotR a x - dotR a y := by
  simp [dotR, mul_sub, Finset.sum_sub_distrib]

theorem dotR_zero {n : ℕ} (a : Fin n → ℚ) : dotR a 0 = 0 := by simp [dotR]

theorem dotR_lsum {n : ℕ} (X : Finset (Fin n → ℚ)) (l : (Fin n → ℚ) → ℚ) (x : Fin n → ℝ) :
    dotR (∑ a ∈ X, l a • a) x = ∑ a ∈ X, (l a : ℝ) * dotR a x := by
  simp only [dotR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem fm_scalarR {κ : Type*} (P : Finset κ) (u c : κ → ℝ) :
    (∃ t : ℝ, ∀ p ∈ P, 0 ≤ u p + c p * t) ↔
      (∀ p ∈ P, c p = 0 → 0 ≤ u p) ∧
      (∀ p ∈ P, ∀ q ∈ P, 0 < c p → c q < 0 → 0 ≤ c p * u q - c q * u p) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun p hp h0 => by simpa [h0] using ht p hp, fun p hp q hq hcp hcq => ?_⟩
    have h1 := mul_nonneg hcp.le (ht q hq)
    have h2 := mul_nonneg (neg_nonneg.mpr hcq.le) (ht p hp)
    have e : c p * u q - c q * u p = c p * (u q + c q * t) + (-c q) * (u p + c p * t) := by ring
    rw [e]
    exact add_nonneg h1 h2
  · rintro ⟨h0, h2⟩
    by_cases hL : (P.filter (fun p => 0 < c p)).Nonempty
    · obtain ⟨p₀, hp₀, hmax⟩ := Finset.exists_max_image _ (fun p => -u p / c p) hL
      rw [Finset.mem_filter] at hp₀
      have hne₀ : c p₀ ≠ 0 := hp₀.2.ne'
      refine ⟨-u p₀ / c p₀, fun p hp => ?_⟩
      rcases lt_trichotomy (c p) 0 with hn | hz | hpos
      · have key := h2 p₀ hp₀.1 p hp hp₀.2 hn
        have e : c p₀ * (u p + c p * (-u p₀ / c p₀)) = c p₀ * u p - c p * u p₀ := by
          field_simp
          ring
        rw [← e] at key
        exact (mul_nonneg_iff_of_pos_left hp₀.2).mp key
      · simpa [hz] using h0 p hp hz
      · have hle : -u p / c p ≤ -u p₀ / c p₀ := hmax p (Finset.mem_filter.mpr ⟨hp, hpos⟩)
        have hne : c p ≠ 0 := hpos.ne'
        have e : c p * (-u p / c p) = -u p := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hle hpos.le]
    · have hL' : ∀ p ∈ P, c p ≤ 0 := fun p hp => by
        by_contra h
        exact hL ⟨p, Finset.mem_filter.mpr ⟨hp, lt_of_not_ge h⟩⟩
      by_cases hU : (P.filter (fun p => c p < 0)).Nonempty
      · obtain ⟨q₀, -, hmin⟩ := Finset.exists_min_image _ (fun p => -u p / c p) hU
        refine ⟨-u q₀ / c q₀, fun p hp => ?_⟩
        rcases (hL' p hp).lt_or_eq with hn | hz
        · have hle : -u q₀ / c q₀ ≤ -u p / c p := hmin p (Finset.mem_filter.mpr ⟨hp, hn⟩)
          have hne : c p ≠ 0 := hn.ne
          have e : c p * (-u p / c p) = -u p := by field_simp
          nlinarith [mul_le_mul_of_nonpos_left hle hn.le]
        · simpa [hz] using h0 p hp hz
      · refine ⟨0, fun p hp => ?_⟩
        have hz : c p = 0 := by
          rcases (hL' p hp).lt_or_eq with hn | hz
          · exact absurd ⟨p, Finset.mem_filter.mpr ⟨hp, hn⟩⟩ hU
          · exact hz
        simpa [hz] using h0 p hp hz

theorem dotR_fm {n : ℕ} (a b : ℚ) (u v : Fin n → ℚ) (x : Fin n → ℝ) :
    dotR (a • u - b • v) x = (a : ℝ) * dotR u x - (b : ℝ) * dotR v x := by
  simp only [dotR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sub, Rat.cast_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem fm_vecR {n : ℕ} (P : Finset ((Fin n → ℚ) × ℚ)) (x : Fin n → ℝ) :
    (∃ t : ℝ, ∀ p ∈ P, 0 ≤ dotR p.1 x + (p.2 : ℝ) * t) ↔ ∀ a ∈ fmSet P, 0 ≤ dotR a x := by
  rw [fm_scalarR P (fun p => dotR p.1 x) (fun p => (p.2 : ℝ))]
  constructor
  · rintro ⟨h0, h2⟩ a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      rw [Finset.mem_filter] at hp
      exact h0 p hp.1 (by simp [hp.2])
    · obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp ha
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hpq
      rw [dotR_fm]
      exact h2 p hpq.1.1 q hpq.2.1 (Rat.cast_pos.mpr hpq.1.2) (Rat.cast_lt_zero.mpr hpq.2.2)
  · intro h
    refine ⟨fun p hp hz => ?_, fun p hp q hq hcp hcq => ?_⟩
    · have hz' : p.2 = 0 := by exact_mod_cast hz
      exact h p.1 (Finset.mem_union_left _
        (Finset.mem_image_of_mem Prod.fst (Finset.mem_filter.mpr ⟨hp, hz'⟩)))
    · have hm : (p.2 • q.1 - q.2 • p.1) ∈ fmSet P :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p, q),
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp, Rat.cast_pos.mp hcp⟩,
            Finset.mem_filter.mpr ⟨hq, Rat.cast_lt_zero.mp hcq⟩⟩, rfl⟩)
      have := h _ hm
      rw [dotR_fm] at this
      exact this

theorem mem_rcone_insert {n : ℕ} {T : Finset (Fin n → ℚ)} {w : Fin n → ℚ} (hw : w ∉ T)
    (x : Fin n → ℝ) :
    x ∈ rcone (insert w T) ↔ ∃ t : ℝ, 0 ≤ t ∧ x - t • castR w ∈ rcone T := by
  classical
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c w, hc w (Finset.mem_insert_self w T), c,
      fun i hi => hc i (Finset.mem_insert_of_mem hi), ?_⟩
    rw [Finset.sum_insert hw]
    abel
  · rintro ⟨t, ht, c, hc, hx⟩
    have hne : ∀ i ∈ T, i ≠ w := fun i hi h => hw (h ▸ hi)
    refine ⟨Function.update c w t, fun i hi => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hi with h | h
      · subst h
        simpa using ht
      · rw [Function.update_of_ne (hne i h)]
        exact hc i h
    · rw [Finset.sum_insert hw, Function.update_self]
      have e : ∑ i ∈ T, Function.update c w t i • castR i = ∑ i ∈ T, c i • castR i :=
        Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (hne i hi)]
      rw [e, ← hx]
      abel

theorem mem_rcone_empty {n : ℕ} (x : Fin n → ℝ) : x ∈ rcone (∅ : Finset (Fin n → ℚ)) ↔ x = 0 := by
  constructor
  · rintro ⟨c, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun _ => 0, fun _ _ => le_rfl, by simp⟩

theorem stdIneq_R (n : ℕ) (x : Fin n → ℝ) : (∀ a ∈ stdIneq n, 0 ≤ dotR a x) ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have a := h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem
      (fun i : Fin n => (Pi.single i 1 : Fin n → ℚ)) (Finset.mem_univ i)))
    have b := h _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun i : Fin n => -(Pi.single i 1 : Fin n → ℚ)) (Finset.mem_univ i)))
    have ea : dotR (Pi.single i 1 : Fin n → ℚ) x = x i := by
      simp [dotR, Pi.single_apply, apply_ite (fun q : ℚ => (q : ℝ)), ite_mul]
    have eb : dotR (-(Pi.single i 1 : Fin n → ℚ)) x = -x i := by
      simp [dotR, Pi.single_apply, apply_ite (fun q : ℚ => (q : ℝ)), ite_mul]
    rw [ea] at a
    rw [eb] at b
    simp only [Pi.zero_apply]
    linarith
  · rintro rfl a _
    simp [dotR_zero]

theorem minkR {n : ℕ} (T : Finset (Fin n → ℚ)) :
    ∃ A : Finset (Fin n → ℚ), ∀ x : Fin n → ℝ, x ∈ rcone T ↔ ∀ a ∈ A, 0 ≤ dotR a x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨stdIneq n, fun x => ?_⟩
    rw [stdIneq_R, mem_rcone_empty]
  | @insert w T hw ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨fmSet (insert ((0 : Fin n → ℚ), (1 : ℚ)) (A.image fun a => (a, -(a ⬝ᵥ w)))), fun x => ?_⟩
    rw [← fm_vecR, mem_rcone_insert hw]
    apply exists_congr
    intro t
    rw [Finset.forall_mem_insert, hA]
    have e : ∀ a : Fin n → ℚ, dotR a (x - t • castR w) = dotR a x + ((-(a ⬝ᵥ w) : ℚ) : ℝ) * t :=
      fun a => by
        rw [dotR_sub, dotR_smul, dotR_castR]
        push_cast
        ring
    have e0 : dotR (0 : Fin n → ℚ) x = 0 := by simp [dotR]
    constructor
    · rintro ⟨ht, hx⟩
      refine ⟨by simpa [e0] using ht, fun p hp => ?_⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      have := hx a ha
      rw [e] at this
      exact this
    · rintro ⟨ht, hx⟩
      refine ⟨by simpa [e0] using ht, fun a ha => ?_⟩
      have := hx _ (Finset.mem_image_of_mem (fun a => (a, -(a ⬝ᵥ w))) ha)
      rw [e]
      exact this

theorem farkasQ {n : ℕ} (X : Finset (Fin n → ℚ)) (f : Fin n → ℚ)
    (hf : ∀ x ∈ hcone X id, 0 ≤ f ⬝ᵥ x) : f ∈ gcone X id := by
  obtain ⟨B, hB⟩ := minkowskiQ X
  rw [hB]
  intro b hb
  have hb' : b ∈ hcone X id := fun x hx => by
    have hx' : x ∈ hcone B id := by
      rw [← hB]
      exact mem_gcone (f := id) hx
    have := hx' b hb
    simp only [id] at this ⊢
    rw [dotProduct_comm]
    exact this
  have := hf b hb'
  simp only [id]
  rw [dotProduct_comm]
  exact this

theorem core {n : ℕ} (X : Finset (Fin n → ℚ)) :
    ∃ Y : Finset (Fin n → ℚ), hcone X id = gcone Y id ∧
      ∀ t : Fin n → ℝ, (∀ a ∈ X, 0 ≤ dotR a t) → t ∈ rcone Y := by
  classical
  obtain ⟨Y, hY⟩ := weylQ X
  obtain ⟨F, hF⟩ := minkR Y
  refine ⟨Y, hY, fun t ht => (hF t).mpr fun f hf => ?_⟩
  have hfY : ∀ y ∈ Y, 0 ≤ f ⬝ᵥ y := fun y hy => by
    have hm : castR y ∈ rcone Y :=
      ⟨fun z => if z = y then 1 else 0, fun z _ => by dsimp only; split_ifs <;> norm_num,
        by simp [ite_smul, hy]⟩
    have := (hF _).mp hm f hf
    rw [dotR_castR] at this
    exact_mod_cast this
  have hfX : ∀ x ∈ hcone X id, 0 ≤ f ⬝ᵥ x := by
    intro x hx
    rw [hY] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [dotProduct_sum]
    exact Finset.sum_nonneg fun y hy => by
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_nonneg (hc y hy) (hfY y hy)
  obtain ⟨l, hl, rfl⟩ := farkasQ X f hfX
  simp only [id]
  rw [dotR_lsum]
  exact Finset.sum_nonneg fun a ha => mul_nonneg (by exact_mod_cast hl a ha) (ht a ha)

theorem eqsFin (n : ℕ) (V : Set (Fin n → ℤ)) :
    ∃ G : Finset (Fin n → ℤ), ∀ (R : Type) [CommRing R] (t : Fin n → R),
      (∀ b ∈ V, ∑ i, (b i : R) * t i = 0) ↔ ∀ g ∈ G, ∑ i, (g i : R) * t i = 0 := by
  classical
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (IsNoetherian.noetherian (Submodule.span ℤ V))
  refine ⟨hSfin.toFinset, fun R _ t => ?_⟩
  let φ : (Fin n → ℤ) →ₗ[ℤ] R :=
    { toFun := fun b => ∑ i, (b i : R) * t i
      map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro m x; simp [Finset.mul_sum, mul_assoc, zsmul_eq_mul] }
  have key : ∀ s : Set (Fin n → ℤ),
      (∀ b ∈ s, ∑ i, (b i : R) * t i = 0) ↔ Submodule.span ℤ s ≤ LinearMap.ker φ := fun s => by
    rw [Submodule.span_le]
    rfl
  have e : (∀ g ∈ hSfin.toFinset, ∑ i, (g i : R) * t i = 0) ↔ ∀ g ∈ S, ∑ i, (g i : R) * t i = 0 := by
    simp only [Set.Finite.mem_toFinset]
  rw [e, key V, key S, hS]

noncomputable def sysX {n : ℕ} (A G : Finset (Fin n → ℤ)) : Finset (Fin n → ℚ) :=
  ((Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → ℚ)) ∪
    (A.image fun a => -GordanCones.toQ a)) ∪ (G.image GordanCones.toQ) ∪
    (G.image fun g => -GordanCones.toQ g)

theorem sysX_iff {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}
    (A G : Finset (Fin n → ℤ)) (t : Fin n → R) :
    (∀ x ∈ sysX A G, 0 ≤ ∑ i, ((x i : ℚ) : R) * t i) ↔
      (∀ i, 0 ≤ t i) ∧ (∀ a ∈ A, ∑ i, (a i : R) * t i ≤ 0) ∧
        (∀ g ∈ G, ∑ i, (g i : R) * t i = 0) := by
  classical
  have e1 : ∀ i, ∑ j, (((Pi.single i 1 : Fin n → ℚ) j : ℚ) : R) * t j = t i := fun i => by
    simp [Pi.single_apply, apply_ite (fun q : ℚ => (q : R)), ite_mul]
  have e2 : ∀ z : Fin n → ℤ, ∑ j, ((GordanCones.toQ z j : ℚ) : R) * t j = ∑ j, (z j : R) * t j :=
    fun z => by simp [GordanCones.toQ]
  have e3 : ∀ z : Fin n → ℤ,
      ∑ j, (((-GordanCones.toQ z) j : ℚ) : R) * t j = -∑ j, (z j : R) * t j :=
    fun z => by simp [GordanCones.toQ, Finset.sum_neg_distrib]
  simp only [sysX, Finset.forall_mem_union, Finset.forall_mem_image, e1, e2, e3,
    Finset.mem_univ, true_implies, neg_nonneg]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, fun g hg => le_antisymm (h4 hg) (h3 hg)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, fun g hg => (h3 g hg).ge⟩, fun g hg => (h3 g hg).le⟩

theorem sum_reindex {M : Type*} [AddCommMonoid M] {n : ℕ} (Y : Finset (Fin n → ℚ))
    (g : (Fin n → ℚ) → M) : ∑ k : Fin Y.card, g (Y.equivFin.symm k) = ∑ y ∈ Y, g y := by
  rw [← Finset.sum_coe_sort Y g]
  exact Equiv.sum_comp Y.equivFin.symm (fun y : Y => g y)

theorem cone_orthant_fg : ∀ (n : ℕ) (A V : Set (Fin n → ℤ)), A.Finite → ∃ (r : ℕ) (v : Fin r → Fin n → ℕ),
    (∀ t : Fin n → ℝ, ((∀ i, 0 ≤ t i) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * t i ≤ 0) ∧
        (∀ b ∈ V, ∑ i, (b i : ℝ) * t i = 0)) ↔
      ∃ c : Fin r → ℝ, (∀ k, 0 ≤ c k) ∧ t = ∑ k, c k • fun i => (v k i : ℝ)) ∧
    ∀ t : Fin n → ℕ, (∀ a ∈ A, ∑ i, a i * (t i : ℤ) ≤ 0) → (∀ b ∈ V, ∑ i, b i * (t i : ℤ) = 0) →
      ∃ (k : ℕ) (c : Fin r → ℕ), 0 < k ∧ k • t = ∑ j, c j • v j := by
  intro n A V hA
  classical
  obtain ⟨G, hG⟩ := eqsFin n V
  obtain ⟨X, hXdef⟩ : ∃ X, X = sysX hA.toFinset G := ⟨_, rfl⟩
  have hcond : ∀ (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (t : Fin n → R),
      ((∀ i, 0 ≤ t i) ∧ (∀ a ∈ A, ∑ i, (a i : R) * t i ≤ 0) ∧
        (∀ b ∈ V, ∑ i, (b i : R) * t i = 0)) ↔
      ∀ x ∈ X, 0 ≤ ∑ i, ((x i : ℚ) : R) * t i := by
    intro R _ _ _ t
    rw [hXdef, sysX_iff, hG R t]
    simp only [Set.Finite.mem_toFinset]
  obtain ⟨Y, hYq, hYr⟩ := core X
  obtain ⟨w, hw⟩ : ∃ w : Fin Y.card → Fin n → ℚ, ∀ k, w k = (Y.equivFin.symm k : Fin n → ℚ) :=
    ⟨_, fun _ => rfl⟩
  have hwX' : ∀ k, ∀ x ∈ X, 0 ≤ x ⬝ᵥ w k := fun k x hx => by
    have hk : w k ∈ hcone X id := by
      rw [hYq, hw]
      exact mem_gcone (f := id) (Y.equivFin.symm k).2
    exact hk x hx
  have hw0 : ∀ k i, 0 ≤ w k i := fun k =>
    ((hcond ℚ (w k)).mpr (fun x hx => by simpa [dotProduct] using hwX' k x hx)).1
  obtain ⟨v, hv⟩ : ∃ v : Fin Y.card → Fin n → ℕ, ∀ k i, v k i = (intOf (w k) i).toNat :=
    ⟨_, fun _ _ => rfl⟩
  have hvQ : ∀ k i, ((v k i : ℕ) : ℚ) = mulOf (w k) * w k i := by
    intro k i
    have h := congrFun (toQ_intOf (w k)) i
    simp only [GordanCones.toQ, Pi.smul_apply, smul_eq_mul] at h
    have hnn : 0 ≤ intOf (w k) i := by
      have : (0 : ℚ) ≤ (intOf (w k) i : ℚ) := by
        rw [h]
        exact mul_nonneg (mulOf_pos _).le (hw0 k i)
      exact_mod_cast this
    calc ((v k i : ℕ) : ℚ) = (((intOf (w k) i).toNat : ℤ) : ℚ) := by rw [hv, Int.cast_natCast]
      _ = (intOf (w k) i : ℚ) := by rw [Int.toNat_of_nonneg hnn]
      _ = _ := h
  have hvR : ∀ k i, ((v k i : ℕ) : ℝ) = ((mulOf (w k) : ℚ) : ℝ) * ((w k i : ℚ) : ℝ) := by
    intro k i
    have := congrArg (fun q : ℚ => (q : ℝ)) (hvQ k i)
    simpa using this
  have hvdot : ∀ k, ∀ x ∈ X, 0 ≤ ∑ i, ((x i : ℚ) : ℝ) * ((v k i : ℕ) : ℝ) := by
    intro k x hx
    have e : ∑ i, ((x i : ℚ) : ℝ) * ((v k i : ℕ) : ℝ) = ((mulOf (w k) * (x ⬝ᵥ w k) : ℚ) : ℝ) := by
      simp only [hvR, dotProduct, Rat.cast_mul, Rat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact_mod_cast mul_nonneg (mulOf_pos (w k)).le (hwX' k x hx)
  refine ⟨Y.card, v, fun t => ?_, fun t hAt hVt => ?_⟩
  · rw [hcond ℝ t]
    constructor
    · intro ht
      obtain ⟨c, hc, hct⟩ := hYr t (fun a ha => ht a ha)
      refine ⟨fun k => c (w k) / ((mulOf (w k) : ℚ) : ℝ), fun k => div_nonneg
        (by rw [hw]; exact hc _ (Y.equivFin.symm k).2) (by exact_mod_cast (mulOf_pos _).le), ?_⟩
      rw [hct]
      refine (sum_reindex Y (fun y => c y • castR y)).symm.trans ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      funext i
      have hm : ((mulOf (w k) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (mulOf_pos (w k)).ne'
      simp only [Pi.smul_apply, smul_eq_mul, castR, hvR, ← hw]
      field_simp
    · rintro ⟨c, hc, rfl⟩ x hx
      have e : ∑ i, ((x i : ℚ) : ℝ) * (∑ k, c k • fun i => ((v k i : ℕ) : ℝ)) i =
          ∑ k, c k * ∑ i, ((x i : ℚ) : ℝ) * ((v k i : ℕ) : ℝ) := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (hvdot k x hx)
  · have htq : ∀ x ∈ X, 0 ≤ ∑ i, ((x i : ℚ) : ℚ) * ((t i : ℕ) : ℚ) := by
      refine (hcond ℚ (fun i => (t i : ℚ))).mp ⟨fun i => Nat.cast_nonneg _, fun a ha => ?_, fun b hb => ?_⟩
      · have h := hAt a ha
        have : ((∑ i, a i * (t i : ℤ) : ℤ) : ℚ) ≤ 0 := by exact_mod_cast h
        push_cast at this
        exact this
      · have h := hVt b hb
        have : ((∑ i, b i * (t i : ℤ) : ℤ) : ℚ) = 0 := by exact_mod_cast h
        push_cast at this
        exact this
    have hmem : (fun i => (t i : ℚ)) ∈ gcone Y id := by
      rw [← hYq]
      intro x hx
      simpa [dotProduct] using htq x hx
    obtain ⟨c, hc, hct⟩ := hmem
    have hct' : (fun i => (t i : ℚ)) = ∑ k, c (w k) • w k := by
      rw [hct]
      refine (sum_reindex Y (fun y => c y • id y)).symm.trans ?_
      exact Finset.sum_congr rfl fun k _ => by rw [hw]; rfl
    obtain ⟨d, hd⟩ : ∃ d : Fin Y.card → ℚ, ∀ k, d k = c (w k) / mulOf (w k) := ⟨_, fun _ => rfl⟩
    have hd0 : ∀ k, 0 ≤ d k := fun k => by
      rw [hd]
      exact div_nonneg (by rw [hw]; exact hc _ (Y.equivFin.symm k).2) (mulOf_pos _).le
    have htd : ∀ i, (t i : ℚ) = ∑ k, d k * (v k i : ℚ) := by
      intro i
      have h1 := congrFun hct' i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hm : mulOf (w k) ≠ 0 := (mulOf_pos (w k)).ne'
      rw [hd, hvQ]
      field_simp
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ∏ k, (d k).den := ⟨_, rfl⟩
    obtain ⟨cN, hcN⟩ : ∃ cN : Fin Y.card → ℕ, ∀ k, cN k = (d k).num.toNat * (K / (d k).den) :=
      ⟨_, fun _ => rfl⟩
    have hcNQ : ∀ k, (cN k : ℚ) = K * d k := by
      intro k
      have hdvd : (d k).den ∣ K := hK ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      have hnum : 0 ≤ (d k).num := Rat.num_nonneg.mpr (hd0 k)
      have h1 : (((d k).num.toNat : ℕ) : ℚ) = ((d k).num : ℚ) := by
        have : (((d k).num.toNat : ℕ) : ℤ) = (d k).num := Int.toNat_of_nonneg hnum
        exact_mod_cast this
      have hden : ((d k).den : ℚ) ≠ 0 := by exact_mod_cast (d k).den_ne_zero
      rw [hcN, Nat.cast_mul, Nat.cast_div hdvd hden, h1]
      calc ((d k).num : ℚ) * ((K : ℚ) / (d k).den) = K * (((d k).num : ℚ) / (d k).den) := by ring
        _ = K * d k := by rw [Rat.num_div_den]
    refine ⟨K, cN, hK ▸ Finset.prod_pos fun k _ => (d k).den_pos, ?_⟩
    funext i
    refine Nat.cast_injective (R := ℚ) ?_
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Nat.cast_mul, Nat.cast_sum, hcNQ]
    rw [htd i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.MinkWeylReal
