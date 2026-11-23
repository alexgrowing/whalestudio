import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DivDerZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

abbrev blockWithThresholds (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) : BlockData N :=
  { D with T := { D.T with thr := thr } }

abbrev SSt (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  (blockWithThresholds D thr).SSZ O (r := r)

structure TieOK (D : BlockData N) : Prop where
  lt : ∀ i, D.T.pos i + 1 < N
  inj : ∀ i i', D.T.pos i = D.T.pos i' → i = i'
  sep : ∀ i i', D.T.pos i + 1 ≠ D.T.pos i'
  uW : ∀ i, D.T.pos i ≠ (D.uPos : ℕ) ∧ D.T.pos i + 1 ≠ (D.uPos : ℕ)
  vecE : ∀ i (h : D.T.pos i + 1 < N), D.LL.vec ⟨D.T.pos i + 1, h⟩ = false

def tailP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (jp : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g

theorem gen_mem (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    (∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g ∈ SSt O r D thr := by
  unfold SSt BlockData.SSZ
  apply Submodule.subset_span
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL, ⟨y, hy, g, hg, ?_⟩⟩⟩⟩
  unfold tailP
  simp only [mul_assoc]
  rfl

theorem SSt_mono (D : BlockData N) {thr thr' : Fin D.T.q → WithTop ℤ} (h : ∀ k, thr k ≤ thr' k) :
    SSt O r D thr ≤ SSt O r D thr' := by
  unfold SSt BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ h hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

def IsMult (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ)
    (aW aE : Fin N) (q0 : MvPolynomial (Fin N × Fin r) (KK O)) : Prop :=
  ∀ (deg : Fin N → ℕ) (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)),
    y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr →
    q0 * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ J
      (fun k => thr k + ((1 : ℤ) : WithTop ℤ))

theorem IsMult.pow {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) (l : ℕ) (deg : Fin N → ℕ)
    (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr) :
    q0 ^ l * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then l else 0⟩ J
      (fun k => thr k + ((l : ℤ) : WithTop ℤ)) := by
  induction l with
  | zero =>
    simpa using hy
  | succ l ih =>
    have h1 := h _ _ _ ih
    rw [pow_succ', mul_assoc]
    have e1 : (fun a => (deg a + if a = aW ∨ a = aE then l else 0) + if a = aW ∨ a = aE then 1 else 0) =
        fun a => deg a + if a = aW ∨ a = aE then l + 1 else 0 := by
      funext a
      split_ifs <;> omega
    have e2 : (fun k => thr k + ((l : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ)) =
        fun k => thr k + (((l + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      funext k
      rw [add_assoc]
      norm_cast
    rw [e1, e2] at h1
    exact h1

theorem isMult_XX (D7 : Formalism.BasicNotions.D7) (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ) (aW aE : Fin N) (hne : aW ≠ aE)
    (hE : vec aE = false) (c c' : Fin r) : IsMult O r vec J aW aE (X (aW, c) * X (aE, c')) := by
  intro deg thr y hy
  have h1 := yjtZ_X (O := O) D7 ⟨vec, deg⟩ ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩ rfl aE c' (fun _ => rfl) J
    (thr := thr) (thr' := thr) 0 (fun h => by simp [hE] at h) (fun k => by simp) hy
  have h2 := yjtZ_X (O := O) D7 ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩
    ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ rfl aW c
    (fun i => by
      show deg i + _ = deg i + _ + _
      by_cases h1 : i = aW
      · subst h1; simp [hne]
      · simp [h1]) J (thr := thr) (thr' := fun k => thr k + ((1 : ℤ) : WithTop ℤ)) 1 (fun _ => le_rfl)
    (fun k => by norm_cast) h1
  rw [mul_assoc]
  exact h2

theorem IsMult.neg {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) : IsMult O r vec J aW aE (-q0) := by
  intro deg thr y hy
  rw [neg_mul]
  exact Submodule.neg_mem _ (h deg thr y hy)

theorem IsMult.sum {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N} {ι : Type} (s : Finset ι)
    {q0 : ι → MvPolynomial (Fin N × Fin r) (KK O)} (h : ∀ i ∈ s, IsMult O r vec J aW aE (q0 i)) :
    IsMult O r vec J aW aE (∑ i ∈ s, q0 i) := by
  intro deg thr y hy
  rw [Finset.sum_mul]
  exact Submodule.sum_mem _ fun i hi => h i hi deg thr y hy

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
