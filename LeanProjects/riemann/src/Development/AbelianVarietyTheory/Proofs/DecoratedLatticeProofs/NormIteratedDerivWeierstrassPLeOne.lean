import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

noncomputable section

namespace GlobalTheory.Klein

variable {p : ℕ} [Fact p.Prime]

def intAt (ι : ℂ ≃+* ℂ_[p]) : Subring ℂ where
  carrier := {c | ‖ι c‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_intAt (ι : ℂ ≃+* ℂ_[p]) (c : ℂ) : c ∈ intAt ι ↔ ‖ι c‖ ≤ 1 := Iff.rfl

theorem half_mem_intAt (ι : ℂ ≃+* ℂ_[p]) (hp : p ≠ 2) : (2⁻¹ : ℂ) ∈ intAt ι := by
  have hc : Nat.Coprime p 2 := (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hc
  have h2 : ‖((2 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', h]
  have h3 : ι 2 = ((2 : ℕ) : ℂ_[p]) := by
    rw [← map_natCast ι]; simp
  rw [mem_intAt, map_inv₀, norm_inv, h3, h2]; simp

theorem mem_intAt_of_sq (ι : ℂ ≃+* ℂ_[p]) {c : ℂ} (h : c ^ 2 ∈ intAt ι) : c ∈ intAt ι := by
  rw [mem_intAt, map_pow, norm_pow] at h
  rw [mem_intAt]
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

def intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : Subring (ℂ → ℂ) :=
  Subring.closure ({fun z => L.weierstrassP z - r, L.derivWeierstrassP} ∪ {f | ∃ c ∈ intAt ι, f = fun _ => c})

theorem const_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {c : ℂ} (hc : c ∈ intAt ι) :
    (fun _ => c) ∈ intFun ι L r :=
  Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem x_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) :
    (fun z => L.weierstrassP z - r) ∈ intFun ι L r :=
  Subring.subset_closure (Or.inl (Or.inl rfl))

theorem y_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : L.derivWeierstrassP ∈ intFun ι L r :=
  Subring.subset_closure (Or.inl (Or.inr rfl))

theorem derivWeierstrassP_mem_intAt {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (hg : Good ι L r)
    (hz : Red ι L r z) : L.derivWeierstrassP z ∈ intAt ι := by
  obtain ⟨-, h1, h2, h3, -⟩ := hg
  obtain ⟨hz, hx⟩ := hz
  rw [← mem_intAt] at h1 h2 h3 hx
  apply mem_intAt_of_sq
  have e : L.derivWeierstrassP z ^ 2 = ((4 : ℕ) : ℂ) * (L.weierstrassP z - r) ^ 3 + 12 * r * (L.weierstrassP z - r) ^ 2
      + (12 * r ^ 2 - L.g₂) * (L.weierstrassP z - r) + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by
    rw [L.derivWeierstrassP_sq z hz]; push_cast; ring
  rw [e]
  exact add_mem (add_mem (add_mem (mul_mem (natCast_mem _ 4) (pow_mem hx 3)) (mul_mem h1 (pow_mem hx 2)))
    (mul_mem h2 hx)) h3

theorem apply_mem_intAt {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (hg : Good ι L r)
    (hz : Red ι L r z) {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) : f z ∈ intAt ι := by
  have : intFun ι L r ≤ (intAt ι).comap (Pi.evalRingHom (fun _ : ℂ => ℂ) z) := by
    refine Subring.closure_le.2 ?_
    rintro f ((rfl | rfl) | ⟨c, hc, rfl⟩)
    · exact hz.2
    · exact derivWeierstrassP_mem_intAt hg hz
    · exact hc
  exact this hf

theorem exists_hasDerivAt_intFun {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r)
    {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) :
    ∃ g ∈ intFun ι L r, ∀ w ∉ L.lattice, HasDerivAt f (g w) w := by
  induction hf using Subring.closure_induction with
  | mem f hf =>
    rcases hf with (rfl | rfl) | ⟨c, hc, rfl⟩
    · exact ⟨_, y_mem_intFun ι L r, fun w hw => (GlobalTheory.hasDerivAt_weierstrassP L hw).sub_const r⟩
    · obtain ⟨hp, h1, h2, -, -⟩ := hg
      rw [← mem_intAt] at h1 h2
      have hx := x_mem_intFun ι L r
      refine ⟨_, add_mem (add_mem (mul_mem (const_mem_intFun ι L r (natCast_mem _ 6)) (mul_mem hx hx))
        (mul_mem (const_mem_intFun ι L r h1) hx))
        (const_mem_intFun ι L r (mul_mem h2 (half_mem_intAt ι hp))), fun w hw => ?_⟩
      convert GlobalTheory.hasDerivAt_derivWeierstrassP L hw using 1
      simp only [Pi.add_apply, Pi.mul_apply]
      push_cast; ring
    · exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w c⟩
  | zero => exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w 0⟩
  | one => exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w 1⟩
  | add f f' _ _ h h' =>
    obtain ⟨g, hg1, hg2⟩ := h
    obtain ⟨g', hg1', hg2'⟩ := h'
    exact ⟨g + g', add_mem hg1 hg1', fun w hw => (hg2 w hw).add (hg2' w hw)⟩
  | neg f _ h =>
    obtain ⟨g, hg1, hg2⟩ := h
    exact ⟨-g, neg_mem hg1, fun w hw => (hg2 w hw).neg⟩
  | mul f f' hf hf' h h' =>
    obtain ⟨g, hg1, hg2⟩ := h
    obtain ⟨g', hg1', hg2'⟩ := h'
    exact ⟨g * f' + f * g', add_mem (mul_mem hg1 hf') (mul_mem hf hg1'),
      fun w hw => (hg2 w hw).mul (hg2' w hw)⟩

theorem exists_iteratedDeriv_eq_intFun {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r) (k : ℕ) :
    ∃ f ∈ intFun ι L r, ∀ w ∉ L.lattice, iteratedDeriv (k + 1) L.weierstrassP w = f w := by
  induction k with
  | zero =>
    exact ⟨_, y_mem_intFun ι L r, fun w hw => by
      rw [zero_add, iteratedDeriv_one]; exact (GlobalTheory.hasDerivAt_weierstrassP L hw).deriv⟩
  | succ k ih =>
    obtain ⟨f, hf, hfe⟩ := ih
    obtain ⟨g, hg1, hg2⟩ := exists_hasDerivAt_intFun hg hf
    refine ⟨g, hg1, fun w hw => ?_⟩
    have he : iteratedDeriv (k + 1) L.weierstrassP =ᶠ[nhds w] f := by
      filter_upwards [GlobalTheory.eventually_notMem_periodLattice L hw] with u hu using hfe u hu
    rw [iteratedDeriv_succ, he.deriv_eq, (hg2 w hw).deriv]

theorem norm_iteratedDeriv_weierstrassP_le_one : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → ∀ z, Red ι L r z → ∀ k : ℕ, ‖ι (iteratedDeriv (k + 1) L.weierstrassP z)‖ ≤ 1 := by
  intro p _ ι L r hg z hz k
  obtain ⟨f, hf, hfe⟩ := exists_iteratedDeriv_eq_intFun hg k
  rw [hfe z hz.1]
  exact apply_mem_intAt hg hz hf

end GlobalTheory.Klein
