import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpOnto

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def Cj1 (M₁ : IntermediateField ℚ ℂ) (ρ₁ : M₁ →ₐ[ℚ] ℂ) (x x' : ℂ) : Prop :=
  ∃ hx : x ∈ M₁, ρ₁ ⟨x, hx⟩ = x'

section cj1

variable {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}

theorem conj_add_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x + y) (x' + y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.add_mem hx hy, ?_⟩
  rw [← map_add]
  rfl

theorem conj_sub_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x - y) (x' - y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.sub_mem hx hy, ?_⟩
  rw [← map_sub]
  rfl

theorem conj_mul_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x * y) (x' * y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.mul_mem hx hy, ?_⟩
  rw [← map_mul]
  rfl

theorem conj_pow_alt {x x' : ℂ} (h : Cj1 M₁ ρ₁ x x') (n : ℕ) : Cj1 M₁ ρ₁ (x ^ n) (x' ^ n) := by
  obtain ⟨hx, rfl⟩ := h
  refine ⟨pow_mem hx n, ?_⟩
  rw [← map_pow]
  rfl

theorem conj_natCast_alt (n : ℕ) : Cj1 M₁ ρ₁ (n : ℂ) (n : ℂ) :=
  ⟨IntermediateField.natCast_mem M₁ n, by
    rw [show (⟨(n : ℂ), IntermediateField.natCast_mem M₁ n⟩ : M₁) = (n : M₁) from
      Subtype.ext (by simp), map_natCast]⟩

theorem conj_sum_alt {ι : Type*} (s : Finset ι) (f f' : ι → ℂ) (h : ∀ i ∈ s, Cj1 M₁ ρ₁ (f i) (f' i)) :
    Cj1 M₁ ρ₁ (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨M₁.zero_mem, map_zero ρ₁⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact conj_add_alt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem conj_unique_alt {x a b : ℂ} (h : Cj1 M₁ ρ₁ x a) (k : Cj1 M₁ ρ₁ x b) : a = b := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hx', rfl⟩ := k
  rfl

theorem conj_eq_alt {x y a b : ℂ} (h : Cj1 M₁ ρ₁ x a) (k : Cj1 M₁ ρ₁ y b) (e : x = y) : a = b := by
  subst e
  exact conj_unique_alt h k

theorem conj_weierstrassP {L L' : PeriodPair} {t t' : ℂ} (h : St L L' M₁ ρ₁ t t') (ht : t ∉ L.lattice) :
    Cj1 M₁ ρ₁ (L.weierstrassP t) (L'.weierstrassP t') ∧
      Cj1 M₁ ρ₁ (L.derivWeierstrassP t) (L'.derivWeierstrassP t') := by
  rcases h with ⟨a, -⟩ | ⟨-, -, hx, hy, e1, e2⟩
  · exact absurd a ht
  · exact ⟨⟨hx, e1.symm⟩, ⟨hy, e2.symm⟩⟩

end cj1

theorem tors_of_ker {L : PeriodPair} {c P : ℂ} (hc0 : c ≠ 0) (hc : MulStable L c)
    (hP : c * P ∈ L.lattice) : ∃ m : ℕ, 0 < m ∧ (m : ℂ) * P ∈ L.lattice := by
  obtain ⟨t, n, ht, hn, -⟩ := mulStableIntegral L c hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h1 : (n : ℂ) = (Complex.normSq c : ℂ) := by rw [← hn, Complex.mul_conj]
    have h2 : (n : ℝ) = Complex.normSq c := by exact_mod_cast h1
    rw [h2]
    exact Complex.normSq_pos.mpr hc0
  have hn0' : 0 < n := by exact_mod_cast hn0
  refine ⟨n.toNat, by omega, ?_⟩
  have e : ((n.toNat : ℕ) : ℂ) * P = (t : ℤ) • (c * P) - c * (c * P) := by
    have : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
      have : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn0'.le
      exact_mod_cast this
    rw [this, ← hn, zsmul_eq_mul]
    have hconj : (starRingEnd ℂ) c = (t : ℂ) - c := by rw [← ht]; ring
    rw [hconj]
    ring
  rw [e]
  exact L.lattice.sub_mem (L.lattice.smul_mem _ hP) (hc _ hP)

theorem mul_notMem {L : PeriodPair} {c z : ℂ} {S : Finset ℂ} (hS : IsKerReps L c S)
    (hz : z ∉ L.lattice) (hzP : ∀ P ∈ S, z + P ∉ L.lattice) :
    c * z ∉ L.lattice := by
  intro hcz
  obtain ⟨Q, hQ, hzQ⟩ := hS.2.2 z hcz hz
  have h1 : c * (-Q) ∈ L.lattice := by
    rw [mul_neg]; exact L.lattice.neg_mem (hS.1 Q hQ).1
  have h2 : -Q ∉ L.lattice := fun h => (hS.1 Q hQ).2 (by simpa using L.lattice.neg_mem h)
  obtain ⟨P, hP, hQP⟩ := hS.2.2 (-Q) h1 h2
  apply hzP P hP
  have := L.lattice.sub_mem hzQ hQP
  rwa [show z - Q - (-Q - P) = z + P by ring] at this

theorem isOpen_veluU (L : PeriodPair) (S : Finset ℂ) : IsOpen (veluU L S) := by
  have e : veluU L S = {z | z ∉ L.lattice} ∩ ⋂ P ∈ S, {z | z + P ∉ L.lattice} := by
    ext z; simp [veluU]
  rw [e]
  refine IsOpen.inter L.isClosed_lattice.isOpen_compl (isOpen_biInter_finset fun P _ => ?_)
  exact L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)

theorem continuousOn_veluF (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluF L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.weierstrassP z := (L.analyticOnNhd_weierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.weierstrassP (z + P) - L.weierstrassP P) z := by
      intro P hP
      have h1 : ContinuousAt L.weierstrassP (z + P) :=
        (L.analyticOnNhd_weierstrassP _ (hz.2 P hP)).continuousAt
      have h2 : ContinuousAt (fun z => L.weierstrassP (z + P)) z :=
        ContinuousAt.comp (g := L.weierstrassP) (f := fun x => x + P) (x := z) h1
          (continuous_add_const P).continuousAt
      exact h2.sub continuousAt_const
    exact tendsto_finsetSum S this
  exact h0.add hs

theorem continuousOn_veluD (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluD L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.derivWeierstrassP z :=
    (L.analyticOnNhd_derivWeierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, L.derivWeierstrassP (z + P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.derivWeierstrassP (z + P)) z := by
      intro P hP
      have h1 : ContinuousAt L.derivWeierstrassP (z + P) :=
        (L.analyticOnNhd_derivWeierstrassP _ (hz.2 P hP)).continuousAt
      exact ContinuousAt.comp (g := L.derivWeierstrassP) (f := fun x => x + P) (x := z) h1
        (continuous_add_const P).continuousAt
    exact tendsto_finsetSum S this
  exact h0.add hs

end PI.GalTorsConj.W

end
