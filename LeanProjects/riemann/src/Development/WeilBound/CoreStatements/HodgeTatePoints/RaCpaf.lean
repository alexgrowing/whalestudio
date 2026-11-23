import Development.WeilBound.CoreStatements.HodgeTatePoints.RaChar
import Development.WeilBound.CoreStatements.HodgeTatePoints.RaTlog

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma mem_pInt_iff [CharZero C] (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (z : C) :
    z ∈ pInt (C := C) R p ↔ v z ≤ v (p : C) := by
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
  · intro h
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := z / p)
      (by rw [map_div₀]; exact div_le_one_of_le₀ h zero_le)
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ hp0]⟩

lemma pow_mem_order {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) (k : ℕ) :
    f ^ k ∈ A.carrier := by
  induction k with
  | zero => simpa using A.one_mem
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hf

lemma tl_mem_order (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (hp : v (p : C) < 1)
    {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) :
    (fun x => tl p (f x)) ∈ A.carrier := by
  have : (fun x => tl p (f x)) =
      ∑ k ∈ Finset.Ico 1 p, fun x => (-1) ^ (k - 1) * (f x - 1) ^ k / (k : C) := by
    funext x; rw [Finset.sum_apply]; rfl
  rw [this]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := (-1) ^ (k - 1) / (k : C)) (by
    rw [map_div₀, val_nat_eq v p hp k h1 h2, map_pow, Valuation.map_neg, map_one, one_pow, div_one])
  have h3 := A.carrier.smul_mem r (pow_mem_order A (A.carrier.sub_mem hf A.one_mem) k)
  convert h3 using 1
  funext x
  simp only [Pi.smul_apply, Algebra.smul_def, hr, Pi.pow_apply, Pi.sub_apply, Pi.one_apply]
  ring

end

theorem cpaf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ μ : N →+ ZMod p, ∃ g ∈ afFun p AA.carrier, ∃ ε : R, v (algebraMap R C ε) ^ (p - 1) = v (p : C) ∧ g 0 = 0 ∧ ∀ x, g x - algebraMap R C ε * ((μ x).val : C) ∈ pInt (C := C) R p ∧ v (g x - algebraMap R C ε * ((μ x).val : C)) < v (algebraMap R C ε) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ AA μ
  have hpp : p.Prime := Fact.out
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hpp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  let ψ : AddChar N C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom μ
  have hψ : ∀ x, ψ x = ζ ^ (μ x).val := fun x => rfl
  have hψp : ∀ x, ψ x ^ p = 1 := fun x => by
    rw [hψ, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζ1 := val_root v p hpp.ne_zero hζ.pow_eq_one
  have hε := val_tl_prim v p hp hζ
  obtain ⟨ε, hεe⟩ := hv.exists_of_le_one (r := tl p ζ) (hε.le.trans (val_prim_lt v p hp hζ).le)
  refine ⟨fun x => tl p (ψ x), ⟨tl_mem_order hv p hp AA (charmem p C v R hv hp N AA ψ), ?_⟩,
    ε, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · intro x y
    rw [mem_pInt_iff hv]
    simp only [AddChar.map_add_eq_mul]
    exact val_tl_add v p hp (hψp x) (hψp y)
  · rw [hεe, hε, val_prim v p hζ]
  · simp only [AddChar.map_zero_eq_one, tl_one]
  · rw [mem_pInt_iff hv, hεe]
    exact (val_tl_pow v p hp hζ1 _).trans (val_prim_pow_le v p hp hζ)
  · rw [hεe, hε]
    exact (val_tl_pow v p hp hζ1 _).trans_lt (val_prim_pow_lt v p hp hζ p hpp.one_lt)

lemma form_add {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] (p : ℕ) [Fact p.Prime]
    {ι : Type} [Fintype ι] (l : ι → R) (x y : ι → ZMod p) :
    algebraMap R C (∑ i, l i * (((x + y) i).val : R)) - algebraMap R C (∑ i, l i * ((x i).val : R))
      - algebraMap R C (∑ i, l i * ((y i).val : R)) ∈ pInt (C := C) R p := by
  simp only [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h := Nat.mod_add_div ((x i).val + (y i).val) p
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → C) h
  rw [pInt, Submodule.mem_span_singleton]
  refine ⟨-(l i * ((((x i).val + (y i).val) / p : ℕ) : R)), ?_⟩
  simp only [Algebra.smul_def, map_neg, map_mul, map_natCast, Pi.add_apply]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h'
  linear_combination (-algebraMap R C (l i)) * h'

theorem lifts : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ (l : ι → R) (ε : R), ε • l ∈ afLat p AA.carrier → v (p : C) ≤ v (algebraMap R C ε) ^ (p - 1) → ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧ (∀ x, v (u x) ≤ 1) ∧ ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA l ε hl hε
  have hpp : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
  have hp0 : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
  have hε0 : v (algebraMap R C ε) ≠ 0 := by
    intro h
    rw [h, zero_pow hp1] at hε
    exact hp0 (le_antisymm hε zero_le)
  have hε0' : algebraMap R C ε ≠ 0 := (Valuation.ne_zero_iff v).1 hε0
  suffices h : ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧
      ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 by
    obtain ⟨u, h1, h2⟩ := h
    refine ⟨u, h1, fun x => ?_, h2⟩
    rw [← sub_add_cancel (u x) (algebraMap R C (∑ i, l i * ((x i).val : R)))]
    exact v.map_add_le (h2 x).le (hv.map_le_one _)
  rcases lt_or_ge (v (p : C)) (v (algebraMap R C ε)) with hlt | hge
  · obtain ⟨g, hg, h⟩ := hl
    refine ⟨fun x => g x / algebraMap R C ε, ?_, fun x => ?_⟩
    · simp only [mul_div_cancel₀ _ hε0']
      refine ⟨hg, fun x y => ?_⟩
      have := Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (h (x + y)) (h x)) (h y))
        (form_add (C := C) p (ε • l) x y)
      convert this using 1
      ring
    · have h1 := (mem_pInt_iff hv p _).1 (h x)
      have h2 : g x / algebraMap R C ε - algebraMap R C (∑ i, l i * ((x i).val : R)) =
          (g x - algebraMap R C (∑ i, (ε • l) i * ((x i).val : R))) / algebraMap R C ε := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, map_mul]
        field_simp
      rw [h2, map_div₀, div_lt_one₀ (pos_iff_ne_zero.2 hε0)]
      exact h1.trans_lt hlt
  · have hc := fun i => cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    choose g hg e he _ hge' using hc
    have hee : ∀ i, v (algebraMap R C ε) ≤ v (algebraMap R C (e i)) := by
      intro i
      refine hge.trans ?_
      rw [← he i]
      exact pow_le_of_le_one zero_le (hv.map_le_one _) hp1
    have he0 : ∀ i, v (algebraMap R C (e i)) ≠ 0 := fun i h =>
      hε0 (le_antisymm (h ▸ hee i) zero_le)
    have he0' : ∀ i, algebraMap R C (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff v).1 (he0 i)
    choose r hr using fun i => hv.dvd_of_le (hee i)
    refine ⟨fun x => ∑ i, algebraMap R C (l i) * (g i x / algebraMap R C (e i)), ?_, fun x => ?_⟩
    · have := Submodule.sum_mem (afFun p AA.carrier) (t := Finset.univ)
        fun i _ => Submodule.smul_mem _ (l i * r i) (hg i)
      convert this using 1
      funext x
      rw [Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h0 := he0' i
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      conv_lhs => rw [hr i, map_mul]
      field_simp
    · rw [map_sum, ← Finset.sum_sub_distrib]
      refine v.map_sum_lt one_ne_zero fun i _ => ?_
      have h0 := he0' i
      have h2 : algebraMap R C (l i) * (g i x / algebraMap R C (e i)) -
          algebraMap R C (l i * ((x i).val : R)) = algebraMap R C (l i) *
          ((g i x - algebraMap R C (e i) * ((x i).val : C)) / algebraMap R C (e i)) := by
        rw [map_mul, map_natCast]
        field_simp
      rw [h2, map_mul, map_div₀]
      refine mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le ?_
      rw [div_lt_one₀ (pos_iff_ne_zero.2 (he0 i))]
      exact (hge' i x).2

end PositivityTheory.HtPt.Ra
