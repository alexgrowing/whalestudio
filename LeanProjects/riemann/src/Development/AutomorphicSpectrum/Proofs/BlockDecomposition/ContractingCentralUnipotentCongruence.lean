import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ZjContract

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal
open GroundTheory.Automorphic.Iwasawa ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diagGL_conj_mem {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α} {m : ℕ}
    (D : Fin n → kˣ)
    (hlt : ∀ i l, β i < β l → valuation k ((D i : k) * ((D l)⁻¹ : kˣ)) ≤ 1)
    (heq : ∀ i l, β i = β l → D i = D l)
    {u : GL (Fin n) k} (hu : u ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β) :
    diagGL k n D * u * (diagGL k n D)⁻¹ ∈
      congruenceSubgroup k n m ⊓ unipotentRadical k n β := by
  have hb : ∀ w ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β, ∀ i l,
      valuation k ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l -
        (1 : Matrix (Fin n) (Fin n) k) i l) ≤
          valuation k ((uniformizer k : 𝒪[k]) : k) ^ m := by
    intro w hw i l
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨hwP, hw1⟩ := mem_unipotentRadical.1 hwN
    rw [diagGL_conj_apply]
    rcases lt_trichotomy (β i) (β l) with h | h | h
    · have hil : i ≠ l := fun e => h.ne (by rw [e])
      have hK := ((mem_congruenceSubgroup_iff k n).1 hwK).2 i l
      rw [one_apply_ne hil, sub_zero] at hK ⊢
      have e : (D i : k) * w i l * (((D l)⁻¹ : kˣ) : k) =
          ((D i : k) * (((D l)⁻¹ : kˣ) : k)) * w i l := by ring
      rw [e, map_mul]
      exact (mul_le_mul' (hlt i l h) hK).trans (by rw [one_mul])
    · rw [hw1 i l h, heq i l h]
      have : (D l : k) * (1 : Matrix (Fin n) (Fin n) k) i l * (((D l)⁻¹ : kˣ) : k) =
          (1 : Matrix (Fin n) (Fin n) k) i l := by
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [this, sub_self, map_zero]
      exact zero_le
    · have hil : i ≠ l := fun e => h.ne' (by rw [e])
      have h0 : w i l = 0 := hwP h
      rw [h0, mul_zero, zero_mul, one_apply_ne hil, sub_zero, map_zero]
      exact zero_le
  have hP : diagGL k n D ∈ blockUpper k n β := levi_le_blockUpper (diagGL_mem_levi D)
  refine Subgroup.mem_inf.2 ⟨mem_congruenceSubgroup_of_le (hb u hu) ?_,
    conj_mem_unipotentRadical hP (Subgroup.mem_inf.1 hu).2⟩
  have : (diagGL k n D * u * (diagGL k n D)⁻¹)⁻¹ =
      diagGL k n D * u⁻¹ * (diagGL k n D)⁻¹ := by group
  rw [this]
  exact hb _ (Subgroup.inv_mem _ hu)

def zjDiag {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) : Fin N → kˣ :=
  fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1

theorem leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = diagGL k N (zjDiag d hd t j) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  rw [coe_diagGL]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    have hb : Zl.JC.blockIdx d hd (stdBlocks d hd ⟨a, i⟩) = a := by simp [Zl.JC.blockIdx]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = t := by
          simp only [zjDiag, hb, if_pos hj]
        rw [hz, hD]
        simp
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = 1 := by
          simp only [zjDiag, hb, if_neg hj]
        rw [hz, hD]
        simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        rw [hz]
        simp [hil]
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        rw [hz]
        simp [hil]
  · rw [leviEmb_apply_ne k _ _ hab, diagonal_apply_ne]
    intro e
    exact hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))

theorem zjDiag_ratio {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {t : kˣ}
    (ht : valuation k (t : k) ≤ 1) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i < Zl.JC.blockIdx d hd l) :
    valuation k ((zjDiag d hd t j i : k) * (((zjDiag d hd t j l)⁻¹ : kˣ) : k)) ≤ 1 := by
  unfold zjDiag
  by_cases hi : Zl.JC.blockIdx d hd i ≤ j
  · by_cases hl : Zl.JC.blockIdx d hd l ≤ j
    · simp [if_pos hi, if_pos hl]
    · simpa [if_pos hi, if_neg hl] using ht
  · have hl : ¬ Zl.JC.blockIdx d hd l ≤ j := fun e => hi (hil.le.trans e)
    simp [if_neg hi, if_neg hl]

theorem zjDiag_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l) :
    zjDiag d hd t j i = zjDiag d hd t j l := by
  simp only [zjDiag, hil]

theorem zj_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  intro k _ _ _ _ h N d hd t ht j m
  rw [leviEmb_zj]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · exact diagGL_conj_mem _ (fun i l hil => zjDiag_ratio d hd ht j hil)
      (fun i l hil => zjDiag_eq d hd t j hil) hu
  · have key := diagGL_conj_mem (β := OrderDual.toDual ∘ Zl.JC.blockIdx d hd)
      (zjDiag d hd t j)⁻¹
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd l < Zl.JC.blockIdx d hd i := hil
        have := zjDiag_ratio d hd ht j hil'
        simpa [Pi.inv_apply, mul_comm] using this)
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l := hil
        simp only [Pi.inv_apply, zjDiag_eq d hd t j hil'])
      (u := z) hz
    rw [map_inv, inv_inv] at key
    exact key

end GlobalTheory.CompanionTheory.ZjContract

end
