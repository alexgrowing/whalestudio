import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def LetterCoprime (x z : LetA O n) : Prop :=
  ∃ m : ℕ, ∃ r ∈ W.AΔ, ∃ s ∈ W.AΔ, lA W ^ m = r * x + s * z

theorem l_pow_mem_invariants (m : ℕ) : lA W ^ m ∈ W.AΔ :=
  W.AΔ.pow_mem (W.AΔ.natCast_mem _) m

theorem Coprime_symm {x z : LetA O n} (h : LetterCoprime W x z) : LetterCoprime W z x := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, s, hs, r, hr, by rw [e]; ring⟩

theorem Coprime_mul {x y z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h1 : LetterCoprime W x z) (h2 : LetterCoprime W y z) : LetterCoprime W (x * y) z := by
  obtain ⟨a, r, hr, s, hs, e1⟩ := h1
  obtain ⟨b, r', hr', s', hs', e2⟩ := h2
  refine ⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩
  · have hy : r' * y ∈ W.AΔ := by
      have : r' * y = lA W ^ b - s' * z := by rw [e2]; ring
      rw [this]; exact W.AΔ.sub_mem (l_pow_mem_invariants W b) (W.AΔ.mul_mem hs' hz)
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_)
      (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)
    rw [mul_assoc]; exact W.AΔ.mul_mem hs hy
  · rw [pow_add, e1, e2]; ring

theorem Coprime_pow {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h : LetterCoprime W x z) : ∀ N : ℕ, LetterCoprime W (x ^ N) z := by
  intro N
  induction N with
  | zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih => rw [pow_succ]; exact Coprime_mul W (W.AΔ.pow_mem hx N) hz ih h

theorem Coprime_prod (s : Finset ℕ) (x : ℕ → LetA O n) {z : LetA O n}
    (hx : ∀ i, x i ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : ∀ i ∈ s, LetterCoprime W (x i) z) :
    LetterCoprime W (∏ i ∈ s, x i) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact Coprime_mul W (W.AΔ.prod_mem fun i _ => hx i) hz
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s))

theorem level_mem_invariants (s : ℕ) : ps W s ∈ W.AΔ :=
  Formalism.MainNotions.UnusedSlot80.UnivC.ps_mem W s

theorem exists_partition_of_l_pow_levels (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    ∃ m : ℕ, ∃ ε : ℕ → LetA O n, (∀ s, ε s ∈ W.AΔ) ∧
      (∀ s ∈ S, ∃ r ∈ W.AΔ, ε s = (∏ t ∈ S.erase s, ps W t ^ N) * r) ∧
      ∑ s ∈ S, ε s = lA W ^ m := by
  have hps := level_mem_invariants W
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with h0 | hne
    · subst h0
      refine ⟨0, fun _ => 1, fun _ => W.AΔ.one_mem, fun t ht => ⟨1, W.AΔ.one_mem, ?_⟩, ?_⟩
      · have h1 : t = a := by simpa using ht
        subst h1; simp
      · simp
    obtain ⟨m, ε, hεΔ, hεd, hsum⟩ := ih hne
    set P := ∏ t ∈ s, ps W t ^ N with hP
    have hPΔ : P ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) N
    have hcop : LetterCoprime W (ps W a ^ N) P := by
      refine Coprime_symm W (Coprime_prod W s _ (fun t => W.AΔ.pow_mem (hps t) N)
        (W.AΔ.pow_mem (hps a) N) fun t ht => ?_)
      have hta : t ≠ a := fun h => ha (h ▸ ht)
      obtain ⟨κ, x, hx, y, hy, hxy⟩ := hC t a hta
      have h1 : LetterCoprime W (ps W t) (ps W a) := ⟨κ, x, hx, y, hy, hxy⟩
      have h2 := Coprime_pow W (hps t) (hps a) h1 N
      exact Coprime_symm W
        (Coprime_pow W (hps a) (W.AΔ.pow_mem (hps t) N) (Coprime_symm W h2) N)
    obtain ⟨m', r, hr, q, hq, he⟩ := hcop
    refine ⟨m + m', fun t => if t = a then lA W ^ m * q * P else ε t * r * ps W a ^ N, ?_, ?_, ?_⟩
    · intro t
      by_cases h : t = a
      · simp only [h, if_true]
        exact W.AΔ.mul_mem (W.AΔ.mul_mem (l_pow_mem_invariants W m) hq) hPΔ
      · simp only [h, if_false]
        exact W.AΔ.mul_mem (W.AΔ.mul_mem (hεΔ t) hr) (W.AΔ.pow_mem (hps a) N)
    · intro t ht
      by_cases h : t = a
      · subst h
        refine ⟨lA W ^ m * q, W.AΔ.mul_mem (l_pow_mem_invariants W m) hq, ?_⟩
        simp only [if_true, Finset.erase_insert ha]
        ring
      · have hts : t ∈ s := by
          rcases Finset.mem_insert.1 ht with h' | h'
          · exact absurd h' h
          · exact h'
        obtain ⟨r₁, hr₁, he₁⟩ := hεd t hts
        refine ⟨r₁ * r, W.AΔ.mul_mem hr₁ hr, ?_⟩
        have hat : a ∉ s.erase t := fun h' => ha (Finset.mem_of_mem_erase h')
        simp only [h, if_false, Finset.erase_insert_of_ne (Ne.symm h), Finset.prod_insert hat, he₁]
        ring
    · rw [Finset.sum_insert ha]
      simp only [if_true]
      have hs2 : ∑ t ∈ s, (if t = a then lA W ^ m * q * P else ε t * r * ps W a ^ N) =
          ∑ t ∈ s, ε t * r * ps W a ^ N :=
        Finset.sum_congr rfl fun t ht => by
          have : t ≠ a := fun h' => ha (h' ▸ ht)
          simp [this]
      rw [hs2, ← Finset.sum_mul, ← Finset.sum_mul, hsum, pow_add, he]
      ring

theorem isUnit_algebraMap_ps_of_ringP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have := Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s)
  simpa [ps, qA, lA] using this

theorem toNat_add_neg_identity (x : ℤ) (N : ℕ) :
    (x + N).toNat + (-x).toNat = x.toNat + N + (-(x + N)).toNat := by
  omega

theorem inId_shift_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : ZMod n} {e s N : ℕ}
    (hs : s < e) {α : ℕ → ℤ} {g : W.EE} (hg : InId W a e α g) {x : LetA O n} (hx : x ∈ W.AΔ) :
    InId W a e (fun t => if t = s then α t else α t + N)
      (algebraMap (LetA O n) W.EE ((∏ t ∈ (Finset.range e).erase s, ps W t ^ N) * x) * g) := by
  obtain ⟨u, hu, he⟩ := hg
  set α' : ℕ → ℤ := fun t => if t = s then α t else α t + N with hα'
  set D := ∏ t ∈ Finset.range e, ps W t ^ (-(α t)).toNat with hD
  set Nm := ∏ t ∈ Finset.range e, ps W t ^ (α t).toNat with hNm
  set D' := ∏ t ∈ Finset.range e, ps W t ^ (-(α' t)).toNat with hD'
  set Nm' := ∏ t ∈ Finset.range e, ps W t ^ (α' t).toNat with hNm'
  set Pz := ∏ t ∈ (Finset.range e).erase s, ps W t ^ N with hPzDef
  have hδ : ∏ t ∈ Finset.range e, ps W t ^ (if t = s then 0 else N) = Pz := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs)]
    simp only [if_true, pow_zero, one_mul]
    exact Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  have key : Nm' * D = Nm * Pz * D' := by
    rw [← hδ, hNm', hD, hNm, hD', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    simp only [hα']
    by_cases h : t = s
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
      exact toNat_add_neg_identity (α t) N
  have hDU : IsUnit (algebraMap (LetA O n) W.EE D) := by
    rw [hD, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun t _ => by
      rw [map_pow]; exact (isUnit_algebraMap_ps_of_ringP W hR t).pow _
  show ∃ u ∈ W.AΔ, algebraMap (LetA O n) W.EE D' * (algebraMap (LetA O n) W.EE (Pz * x) * g) =
    algebraMap (LetA O n) W.EE (letE a * Nm' * u)
  refine ⟨x * u, W.AΔ.mul_mem hx hu, ?_⟩
  apply hDU.mul_left_cancel
  have e1 : algebraMap (LetA O n) W.EE D * (algebraMap (LetA O n) W.EE D' *
      (algebraMap (LetA O n) W.EE (Pz * x) * g)) =
      algebraMap (LetA O n) W.EE D' * algebraMap (LetA O n) W.EE (Pz * x) *
        (algebraMap (LetA O n) W.EE D * g) := by ring
  rw [e1, he]
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  linear_combination (-(letE a * x * u)) * key

end Core

end Formalism.MainNotions.N.Ln17
