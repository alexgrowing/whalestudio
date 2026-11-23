import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPartitionOfLPowLevels

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

theorem section_in_ideal_of_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) (he : 1 ≤ e) {d : ℕ} (b : Fin d → W.DD T)
    (h : Fin d → W.EE)
    (hlev : ∀ s < e, ∃ κ : ℕ, SecIn W a e
      (fun α c₀ => dvO W T e b c₀ ∈ FilS W T a s (-(α s))) (fun k => lE W κ * h k))
    (hlow : ∀ t < e, ∃ U : ℤ, ∀ u ≤ U, ∀ c₀ : Fin d → O, dvO W T e b c₀ ∈ FilS W T a t u) :
    ∃ κ : ℕ, SecIn W a e (condNN W T a e b) (fun k => lE W κ * h k) := by
  have hlev' : ∀ s : ℕ, ∃ κ : ℕ, ∃ I : ℕ, ∃ g : Fin I → W.EE, ∃ c₀ : Fin I → Fin d → O,
      ∃ α : Fin I → ℕ → ℤ, s < e →
        (∀ i, InId W a e (α i) (g i) ∧ dvO W T e b (c₀ i) ∈ FilS W T a s (-(α i s))) ∧
        ∀ k, lE W κ * h k = ∑ i, g i * algebraMap O W.EE (c₀ i k) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨κ, I, g, c₀, α, h1, h2⟩ := hlev s hs
      exact ⟨κ, I, g, c₀, α, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun h' => absurd h' hs⟩
  choose κs I g c₀ α hsec using hlev'
  have hlow' : ∀ t : ℕ, ∃ U : ℤ, t < e → ∀ u ≤ U, ∀ c : Fin d → O, dvO W T e b c ∈ FilS W T a t u := by
    intro t
    by_cases ht : t < e
    · obtain ⟨U, hU⟩ := hlow t ht
      exact ⟨U, fun _ => hU⟩
    · exact ⟨0, fun h' => absurd h' ht⟩
  choose U hU using hlow'
  set N : ℕ := ∑ s ∈ Finset.range e, ∑ i : Fin (I s), ∑ t ∈ Finset.range e,
    ((U t).natAbs + (α s i t).natAbs) with hN
  set κ : ℕ := ∑ s ∈ Finset.range e, κs s with hκ
  obtain ⟨m, ε, -, hεd, hsum⟩ :=
    exists_partition_of_l_pow_levels W hC N (Finset.range e) ⟨0, Finset.mem_range.2 (by omega)⟩
  choose! r hr hεr using hεd
  have hlE : ∀ j, lE W j = algebraMap (LetA O n) W.EE (lA W ^ j) := by
    intro j; simp [lE, lA]
  have hκs : ∀ s < e, κs s ≤ κ := fun s hs =>
    Finset.single_le_sum (f := κs) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  let σ := Σ s : Fin e, Fin (I s)
  let eqv := Fintype.equivFin σ
  let G' : σ → W.EE := fun p => algebraMap (LetA O n) W.EE
    ((∏ t ∈ (Finset.range e).erase (p.1 : ℕ), ps W t ^ N) * (r p.1 * lA W ^ (κ - κs p.1))) * g p.1 p.2
  let C' : σ → Fin d → O := fun p => c₀ p.1 p.2
  let A' : σ → ℕ → ℤ := fun p t => if t = (p.1 : ℕ) then α p.1 p.2 t else α p.1 p.2 t + N
  have hmono : ∀ p : σ, InId W a e (A' p) (G' p) ∧ condNN W T a e b (A' p) (C' p) := by
    rintro ⟨⟨s, hs⟩, i⟩
    have hx : r s * lA W ^ (κ - κs s) ∈ W.AΔ :=
      W.AΔ.mul_mem (hr s (Finset.mem_range.2 hs)) (l_pow_mem_invariants W _)
    refine ⟨inId_shift_levels W hR hs ((hsec s hs).1 i).1 hx, fun t ht => ?_⟩
    by_cases hts : t = s
    · subst hts
      simp only [A', if_true]
      exact ((hsec t hs).1 i).2
    · simp only [A', hts, if_false]
      refine hU t ht _ ?_ _
      have h1 : (U t).natAbs + (α s i t).natAbs ≤
          ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) :=
        Finset.single_le_sum (f := fun t' => (U t').natAbs + (α s i t').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 ht)
      have h2 : ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) ≤
          ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) :=
        Finset.single_le_sum (f := fun i' => ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h3 : ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) ≤ N :=
        Finset.single_le_sum (f := fun s' => ∑ i' : Fin (I s'), ∑ t' ∈ Finset.range e,
          ((U t').natAbs + (α s' i' t').natAbs)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
      have hN' : (((U t).natAbs : ℕ) : ℤ) + (((α s i t).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast h1.trans (h2.trans h3)
      rw [Int.natCast_natAbs, Int.natCast_natAbs] at hN'
      have e1 := neg_abs_le (U t)
      have e2 := neg_abs_le (α s i t)
      linarith
  refine ⟨m + κ, Fintype.card σ, fun j => G' (eqv.symm j), fun j => C' (eqv.symm j),
    fun j => A' (eqv.symm j), fun j => hmono (eqv.symm j), fun k => ?_⟩
  rw [Equiv.sum_comp eqv.symm (fun p => G' p * algebraMap O W.EE (C' p k)), Fintype.sum_sigma]
  calc lE W (m + κ) * h k
      = (∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s)) * (lE W κ * h k) := by
        rw [← map_sum, hsum, ← hlE, lE, lE, lE, pow_add]; ring
    _ = ∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : lE W κ = lE W (κ - κs s) * lE W (κs s) := by
          rw [lE, lE, lE, ← pow_add, Nat.sub_add_cancel (hκs s (Finset.mem_range.1 hs))]
        rw [this]; ring
    _ = ∑ s : Fin e, ∑ i : Fin (I s), G' ⟨s, i⟩ * algebraMap O W.EE (C' ⟨s, i⟩ k) := by
        rw [Finset.sum_range (fun s => algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k))]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [(hsec s s.2).2 k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [G', C']
        rw [hεr s (Finset.mem_range.2 s.2), hlE]
        simp only [map_mul]
        ring

end Core

end Formalism.MainNotions.N.Ln17
