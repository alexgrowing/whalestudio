import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact

open Matrix

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ}

local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def WB (k r : ℕ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), ¬ (inW k r i ∧ inW k r j) → a i j = if i = j then 1 else 0

theorem wb_of_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {h : 𝕄} (hh : h ∈ UWset k r z) : WB k r h :=
  fun i j hij => uw_block hh i j hij

theorem nc_conj {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1) (hm : NC k r m) :
    NC k r (a * m * b) := by
  intro i j hj hi
  by_cases hjr : j.val < r
  ·
    have hjW : ¬ inW k r j := by unfold inW; omega
    have hji : j.val ≤ i.val := by omega
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hb j j (fun h => hjW h.2), if_pos rfl, mul_one, Matrix.mul_apply,
        Finset.sum_eq_single j]
      · rw [hm j j hj (by omega), if_pos rfl, mul_one]
        exact ha i j (fun h => hjW h.2)
      · intro p _ hpj
        by_cases hp : j.val ≤ p.val
        · rw [hm p j hj (by omega), if_neg hpj, mul_zero]
        · have hpW : ¬ inW k r p := by unfold inW; omega
          have hip : i ≠ p := by intro e; subst e; omega
          rw [ha i p (fun h => hpW h.2), if_neg hip, zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro q _ hqj
      rw [hb q j (fun h => hjW h.2), if_neg hqj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  ·
    have hjW : inW k r j := by unfold inW; omega
    have hir : r ≤ i.val := by omega
    have key : ∀ q : Fin (2 * r + k + 1), (a * m) i q * b q j = a i q * b q j := by
      intro q
      by_cases hqW : inW k r q
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single q]
        · rw [hm q q hqW.2 (by unfold inW at hqW; omega), if_pos rfl, mul_one]
        · intro p _ hpq
          by_cases hp : r ≤ p.val
          · rw [hm p q hqW.2 (by unfold inW at hqW; omega), if_neg hpq, mul_zero]
          · have hpW : ¬ inW k r p := by unfold inW; omega
            have hip : i ≠ p := by intro e; subst e; omega
            rw [ha i p (fun h => hpW h.2), if_neg hip, zero_mul]
        · intro h; exact absurd (Finset.mem_univ q) h
      · have hqj : q ≠ j := by intro e; subst e; exact hqW hjW
        rw [hb q j (fun h => hqW h.1), if_neg hqj, mul_zero, mul_zero]
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun q _ => key q), ← Matrix.mul_apply, hab,
      Matrix.one_apply]

theorem conj_mem_N {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1)
    (haU : a ∈ UH (Hpk k r)) (hbU : b ∈ UH (Hpk k r)) (hm : m ∈ Nset k r) :
    a * m * b ∈ Nset k r := by
  rw [mem_Nset_iff] at hm ⊢
  exact ⟨mul_mem_UH (mul_mem_UH haU hm.1) hbU, nc_conj ha hb hab hm.2⟩

theorem isClosed_NC : IsClosed {g : 𝕄 | NC k r g} := by
  have e : {g : 𝕄 | NC k r g} = ⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
      {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} := by
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : j.val ≤ r + k ∧ min j.val r ≤ i.val
  · have e2 : {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        {g : 𝕄 | g i j = if i = j then 1 else 0} := by
      ext g; simp only [Set.mem_ofPred_eq, h.1, h.2, forall_const]
    rw [e2]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have e2 : {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        Set.univ := by
      ext g; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e2]; exact isClosed_univ

theorem isClosed_Nset : IsClosed (Nset k r) := by
  have e : Nset k r = UH (Hpk k r) ∩ {g : 𝕄 | NC k r g} := by
    ext g; rw [mem_Nset_iff]; rfl
  rw [e]
  exact (unitary_hermitian_group k r).1.inter isClosed_NC

variable {z : Fin (2 * r + k + 1) → ℂ}

theorem mem_Sset_iff (g : 𝕄) : g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, h⁻¹ * g ∈ Nset k r := by
  constructor
  · rintro ⟨h, hh, m, hm, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]
    exact hm
  · rintro ⟨h, hh, hm⟩
    refine ⟨h, hh, h⁻¹ * g, hm, ?_⟩
    rw [← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]

theorem isClosed_Sset (hz : inWb k r z) (hT : 0 < Tz k r z) : IsClosed (Sset k r z) := by
  haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.1 (unitary_weyl_compact k r z hz hT)
  have hc : Continuous fun p : UWset k r z × 𝕄 => Hpk k r * (p.1 : 𝕄)ᴴ * Hpk k r * p.2 :=
    (((continuous_const.matrix_mul
      (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose).matrix_mul
        continuous_const).matrix_mul continuous_snd)
  have hT' : IsClosed {p : UWset k r z × 𝕄 | Hpk k r * (p.1 : 𝕄)ᴴ * Hpk k r * p.2 ∈ Nset k r} :=
    isClosed_Nset.preimage hc
  have e : Sset k r z = Prod.snd '' {p : UWset k r z × 𝕄 |
      Hpk k r * (p.1 : 𝕄)ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
    ext g
    rw [mem_Sset_iff]
    constructor
    · rintro ⟨h, hh, hm⟩
      refine ⟨(⟨h, hh⟩, g), ?_, rfl⟩
      show Hpk k r * hᴴ * Hpk k r * g ∈ Nset k r
      rw [← inv_eq_UH hh.1]; exact hm
    · rintro ⟨⟨⟨h, hh⟩, g'⟩, hm, rfl⟩
      refine ⟨h, hh, ?_⟩
      show h⁻¹ * g' ∈ Nset k r
      rw [inv_eq_UH hh.1]; exact hm
  rw [e]
  exact isClosedMap_snd_of_compactSpace _ hT'

theorem one_mem_Sset : (1 : 𝕄) ∈ Sset k r z :=
  ⟨1, one_mem_UW, 1, (nilpotent_subgroup k r).1, (Matrix.one_mul 1).symm⟩

theorem mul_mem_Sset {a b : 𝕄} (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) :
    a * b ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := hb
  have hconj : h'⁻¹ * m * h' ∈ Nset k r :=
    conj_mem_N (wb_of_mem_UW (inv_mem_UW hh')) (wb_of_mem_UW hh') (inv_mul_UH' hh'.1)
      (inv_mem_UH hh'.1) hh'.1 hm
  refine ⟨h * h', mul_mem_UW hh hh', h'⁻¹ * m * h' * m', (nilpotent_subgroup k r).2.1 _ hconj _ hm', ?_⟩
  calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
        rw [mul_inv_UH hh'.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [Matrix.mul_assoc]

theorem inv_mem_Sset {a : 𝕄} (ha : a ∈ Sset k r z) : a⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  have hmi : m⁻¹ ∈ Nset k r := ((nilpotent_subgroup k r).2.2 m hm)
  have hconj : h * m⁻¹ * h⁻¹ ∈ Nset k r :=
    conj_mem_N (wb_of_mem_UW hh) (wb_of_mem_UW (inv_mem_UW hh)) (mul_inv_UH hh.1)
      hh.1 (inv_mem_UH hh.1) hmi
  refine ⟨h⁻¹, inv_mem_UW hh, h * m⁻¹ * h⁻¹, hconj, ?_⟩
  rw [Matrix.mul_inv_rev]
  calc m⁻¹ * h⁻¹ = (h⁻¹ * h) * m⁻¹ * h⁻¹ := by rw [inv_mul_UH' hh.1, Matrix.one_mul]
    _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]

theorem stabilizer_closed_matrix_group : SsetGroup := by
  intro k r z hz hT
  refine ⟨isClosed_Sset hz hT, one_mem_Sset, fun a ha b hb => mul_mem_Sset ha hb,
    fun a ha => ⟨inv_mem_Sset ha, ?_⟩⟩
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  exact mul_inv_UH (mul_mem_UH hh.1 hm.1)

end CompanionTheory.D.Upq.QuotSetU
