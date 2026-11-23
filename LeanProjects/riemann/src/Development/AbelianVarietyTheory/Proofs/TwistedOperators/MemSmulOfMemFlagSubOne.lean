import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.mul_inv_q (q : _root_.GlobalTheory.LatPair.Unif k) :
    (q.1 : k) * q.inv = 1 :=
  mul_inv_cancel₀ q.ne_zero

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in

theorem _root_.GlobalTheory.LevelUnfold.mem_gluedS {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {y : n ⊕ Fin c → k} :
    y ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val = 0 → y (Sum.inr i) = q.inv * s) ∧
        (0 < i.val → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, _root_.GlobalTheory.LatPair.mem_gluedLat]
  refine exists_congr fun s => and_congr_right fun _ => forall_congr' fun i => ?_
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨fun h => h2 (by omega), fun h => h3 (by omega)⟩
  · rintro ⟨h2, h3⟩
    exact ⟨fun h => absurd h (by omega), fun h => h2 (by omega), fun h => h3 (by omega)⟩

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in

theorem _root_.GlobalTheory.LevelUnfold.gluedS_le_iff {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {M : Submodule 𝒪[k] (n ⊕ Fin c → k)} :
    _root_.GlobalTheory.LatPair.gluedS q c L f ≤ M ↔ (∀ y ∈ L, _root_.GlobalTheory.LatPair.inX k n c y ∈ M) ∧
      q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
          _root_.GlobalTheory.LatPair.inX k n c f ∈ M ∧
      ∀ i : Fin c, 0 < i.val →
        q.inv • _root_.GlobalTheory.LatPair.avec k n c (i.val + 1) ∈ M := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  rw [sup_le_iff, sup_le_iff, Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem,
    Submodule.span_le, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h i hi
    exact h ⟨i.val + 1, by omega, by omega, rfl⟩
  · rintro h y ⟨j, hj2, hjc, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact h ⟨m, by omega⟩ (by simp only; omega)

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.interX_gluedS (hc : 1 ≤ c) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX (_root_.GlobalTheory.LatPair.gluedS q c L f) = L := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX
  ext x
  rw [Submodule.mem_comap, ← _root_.GlobalTheory.LatPair.gluedLat_one]
  exact _root_.GlobalTheory.LatPair.inX_mem_gluedLat le_rfl hc

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
      _root_.GlobalTheory.LatPair.inX k n c f ∈ _root_.GlobalTheory.LatPair.gluedS q c L f := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (hc : 1 ≤ c) {L : Submodule 𝒪[k] (n → k)}
    {f x : n → k} :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔
      x - f ∈ L := by
  have hg := _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := c) L f
  have hsplit : q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x =
      (q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c f) + _root_.GlobalTheory.LatPair.inX k n c (x - f) := by
    rw [map_sub]
    abel
  rw [hsplit, Submodule.add_mem_iff_right _ hg, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.inX_mem_gluedLat le_rfl hc]

theorem mul_coord_mem {L : Submodule 𝒪[k] (n → k)} {f : n → k} {y : n ⊕ Fin c → k} (hy : y ∈ gluedS q c L f)
    (i : Fin c) : (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k] := by
  obtain ⟨s, -, h⟩ := mem_gluedS.1 hy
  rcases Nat.eq_zero_or_pos i.val with hi | hi
  · rw [(h i).1 hi, ← mul_assoc, mul_inv_q, one_mul]
    exact s.2
  · exact (h i).2 hi

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.gluedS_congr {L : Submodule 𝒪[k] (n → k)} {f f' : n → k}
    (h : f - f' ∈ L) : _root_.GlobalTheory.LatPair.gluedS q c L f = _root_.GlobalTheory.LatPair.gluedS q c L f' := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.gluedLat_congr q c 1 h]

variable [Fintype n] [DecidableEq n]

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
variable [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LevelUnfold.embX_smul_gluedS (g : GL n k) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) :
    _root_.GlobalTheory.RootEx.embX c g • _root_.GlobalTheory.LatPair.gluedS q c L f =
      _root_.GlobalTheory.LatPair.gluedS q c (g • L) (g • f) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.embX_smul_gluedLat]

omit [Fintype n] [DecidableEq n] in

def colEquiv (n n' : Type) (c : ℕ) :
    (Σ i : Fin c, n ⊕ Fin (i.val + 1)) ≃ {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} :=
  Equiv.ofBijective
    (fun t => ⟨(Sum.map id (Fin.castLE t.1.2) t.2, Sum.inr t.1.succ), by
      rcases t with ⟨i, j | j⟩
      · simp [Free]
      · simpa [Free] using j.2⟩) <| by
    constructor
    · rintro ⟨i, j⟩ ⟨i', j'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq, Sum.inr.injEq, Fin.succ_inj] at h
      obtain ⟨h, rfl⟩ := h
      rw [(Sum.map_injective.2 ⟨Function.injective_id, Fin.castLE_injective _⟩) h]
    · rintro ⟨⟨r | r, s | s⟩, h⟩
      · exact h.elim
      · have hs : s ≠ 0 := by rintro rfl; simp [Free] at h
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hs
        exact ⟨⟨i, Sum.inl r⟩, rfl⟩
      · simp [Free] at h
      · have hs : s ≠ 0 := by rintro rfl; simp [Free] at h
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hs
        exact ⟨⟨i, Sum.inr ⟨r.val, h⟩⟩, rfl⟩

end GlobalTheory.LevelUnfold
