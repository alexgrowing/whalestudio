import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic

noncomputable section

open Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.MirTower

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

def mirU (R : Type) [CommRing R] (a m : ℕ) : Subgroup (GL (Fin a) R) where
  carrier := {g | ∀ i k : Fin a, m ≤ (i : ℕ) → k ≤ i → g.val i k = (1 : Matrix (Fin a) (Fin a) R) i k}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh i k hi hk
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hg i i hi le_rfl, Matrix.one_apply_eq, one_mul,
      hh i k hi hk]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h1 | h1
      · rw [hg i l hi h1.le, Matrix.one_apply_ne hl.symm, zero_mul]
      · rw [hh l k (hi.trans h1.le) (hk.trans h1.le), Matrix.one_apply_ne (hk.trans_lt h1).ne', mul_zero]
    · simp
  inv_mem' := by
    intro g hg i
    induction i using WellFoundedGT.induction with
    | ind i ih =>
      intro k hi hk
      have h := congrFun (congrFun g.mul_inv i) k
      rw [Matrix.mul_apply, Finset.sum_eq_single i, hg i i hi le_rfl, Matrix.one_apply_eq, one_mul] at h
      · exact h
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with h1 | h1
        · rw [hg i l hi h1.le, Matrix.one_apply_ne hl.symm, zero_mul]
        · rw [ih l h1 k (hi.trans h1.le) (hk.trans h1.le), Matrix.one_apply_ne (hk.trans_lt h1).ne', mul_zero]
      · simp

theorem mem_mirU {m : ℕ} {g : GL (Fin a) R} :
    g ∈ mirU R a m ↔ ∀ i k : Fin a, m ≤ (i : ℕ) → k ≤ i → g.val i k = (1 : Matrix (Fin a) (Fin a) R) i k := Iff.rfl

theorem mirU_mono {m n : ℕ} (h : m ≤ n) : mirU R a m ≤ mirU R a n := fun _ hg i k hi hk => hg i k (h.trans hi) hk

theorem mem_mirU_zero {g : GL (Fin a) R} :
    g ∈ mirU R a 0 ↔ (∀ i k : Fin a, k < i → g.val i k = 0) ∧ ∀ i, g.val i i = 1 := by
  refine ⟨fun h => ⟨fun i k hk => ?_, fun i => ?_⟩, fun h i k _ hk => ?_⟩
  · rw [h i k (Nat.zero_le _) hk.le, Matrix.one_apply_ne hk.ne']
  · rw [h i i (Nat.zero_le _) le_rfl, Matrix.one_apply_eq]
  · rcases hk.eq_or_lt with rfl | h1
    · rw [h.2, Matrix.one_apply_eq]
    · rw [h.1 i k h1, Matrix.one_apply_ne h1.ne']

theorem mem_mirU_last {n : ℕ} {g : GL (Fin (n + 1)) R} :
    g ∈ mirU R (n + 1) n ↔ ∀ k, g.val (Fin.last n) k = if k = Fin.last n then 1 else 0 := by
  refine ⟨fun h k => ?_, fun h i k hi _ => ?_⟩
  · rw [h _ k le_rfl (Fin.le_last k), Matrix.one_apply]
    simp only [eq_comm]
  · obtain rfl : i = Fin.last n := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    rw [h, Matrix.one_apply]
    simp only [eq_comm]

def colFix (R : Type) [CommRing R] (a m : ℕ) : Subgroup (GL (Fin a) R) where
  carrier := {g | ∀ i k : Fin a, (k : ℕ) < m → g.val i k = (1 : Matrix (Fin a) (Fin a) R) i k}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh i k hk
    simp only [Units.val_mul, Matrix.mul_apply, hh _ k hk]
    rw [← Matrix.mul_apply, Matrix.mul_one, hg i k hk]
  inv_mem' := by
    intro g hg i k hk
    have h := congrFun (congrFun g.inv_mul i) k
    simp only [Matrix.mul_apply, hg _ k hk] at h
    rwa [← Matrix.mul_apply, Matrix.mul_one] at h

def lateU (R : Type) [CommRing R] (a m : ℕ) : Subgroup (GL (Fin a) R) := mirU R a m ⊓ colFix R a m

theorem mul_apply_congr {n : ℕ} {y : GL (Fin a) R} (hy : y ∈ mirU R a n) {x x' : Matrix (Fin a) (Fin a) R} {i : Fin a}
    (h : ∀ l : Fin a, (l : ℕ) < n → x i l = x' i l) {k : Fin a} (hk : (k : ℕ) < n) :
    (x * y.val) i k = (x' * y.val) i k := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : (l : ℕ) < n
  · rw [h l hl]
  · have h1 : k < l := by change (k : ℕ) < l; omega
    rw [hy l k (by omega) h1.le, Matrix.one_apply_ne h1.ne', mul_zero, mul_zero]

theorem conj_mem_lateU {n : ℕ} {γ u : GL (Fin a) R} (hγ : γ ∈ mirU R a n) (hu : u ∈ lateU R a n) :
    γ⁻¹ * u * γ ∈ lateU R a n := by
  refine ⟨(mirU R a n).mul_mem ((mirU R a n).mul_mem ((mirU R a n).inv_mem hγ) hu.1) hγ, fun i k hk => ?_⟩
  have h : ∀ l, (u.val * γ.val) l k = γ.val l k := fun l => by
    rw [mul_apply_congr hγ (x' := 1) (fun l' hl' => hu.2 l l' hl') hk, Matrix.one_mul]
  rw [mul_assoc, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp only [h]
  rw [← Matrix.mul_apply, Units.inv_mul]

theorem blkU_apply {n : ℕ} (y : UnipotentBlockColumnIndex a n n → R) (i k : Fin a) :
    (blkU y : GL (Fin a) R).val i k = (1 : Matrix (Fin a) (Fin a) R) i k +
      if h : (i : ℕ) < n ∧ n ≤ (k : ℕ) ∧ (k : ℕ) ≤ n then y ⟨(i, k), h⟩ else 0 := by
  rw [← posM_block_entry]; rfl

theorem blkU_add {n : ℕ} (x y : UnipotentBlockColumnIndex a n n → R) : (blkU (x + y) : GL (Fin a) R) = blkU x * blkU y := posU_add _ x y

theorem blkU_mem_mirU (m : ℕ) {n : ℕ} (y : UnipotentBlockColumnIndex a n n → R) : blkU y ∈ mirU R a m := fun i k _ hk => by
  have : (k : ℕ) ≤ i := hk
  rw [blkU_apply, dif_neg (by omega), add_zero]

theorem blkU_mem_lateU {m n : ℕ} (h : m ≤ n) (y : UnipotentBlockColumnIndex a n n → R) : blkU y ∈ lateU R a m :=
  ⟨blkU_mem_mirU m y, fun i k hk => by rw [blkU_apply, dif_neg (by omega), add_zero]⟩

def colGen (R : Type) [CommRing R] (a n : ℕ) : Subgroup (GL (Fin a) R) :=
  Subgroup.closure {u | ∃ k, n ≤ k ∧ ∃ y : UnipotentBlockColumnIndex a k k → R, u = blkU y}

theorem colGen_le_lateU {n : ℕ} : colGen R a n ≤ lateU R a n :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨k, hk, y, rfl⟩; exact blkU_mem_lateU hk y)

theorem exists_peel {m n : ℕ} (hmn : m ≤ n) {g : GL (Fin a) R} (hg : g ∈ mirU R a m) :
    ∃ u ∈ colGen R a n, ∃ g₀ ∈ mirU R a m, g = u * g₀ ∧
      (∀ i k : Fin a, n ≤ (k : ℕ) → g₀.val i k = (1 : Matrix (Fin a) (Fin a) R) i k) ∧
      ∀ i k : Fin a, (k : ℕ) < n → g₀.val i k = g.val i k := by
  by_cases hna : a ≤ n
  · exact ⟨1, one_mem _, g, hg, (one_mul g).symm, fun i k hk => absurd k.2 (by omega), fun _ _ _ => rfl⟩
  replace hna : n ≤ a := by omega
  induction hna using Nat.decreasingInduction with
  | self => exact ⟨1, one_mem _, g, hg, (one_mul g).symm, fun i k hk => absurd k.2 (by omega), fun _ _ _ => rfl⟩
  | of_succ n hn ih =>
    obtain ⟨u, hu, g₁, hg₁, rfl, h1, h2⟩ := ih (by omega)
    let y : UnipotentBlockColumnIndex a n n → R := fun t => g₁.val t.1.1 t.1.2
    have hrow : ∀ k : Fin a, (k : ℕ) = n → ∀ j, g₁.val k j = (1 : Matrix (Fin a) (Fin a) R) k j := by
      intro k hk j
      by_cases hj : j ≤ k
      · exact hg₁ k j (by omega) hj
      · exact h1 k j (by have : ¬ (j : ℕ) ≤ k := hj; omega)
    have hval : ∀ i j, ((blkU y)⁻¹ * g₁).val i j = g₁.val i j -
        if h : (i : ℕ) < n ∧ n ≤ (j : ℕ) ∧ (j : ℕ) ≤ n then y ⟨(i, j), h⟩ else 0 := by
      intro i j
      have e : ((blkU y)⁻¹ * g₁).val = (1 - posM Subtype.val y) * g₁.val := rfl
      rw [e, sub_mul, one_mul, posM_col_mul y _ hrow, Matrix.sub_apply, posM_block_entry]
    refine ⟨u * blkU y, mul_mem (Subgroup.closure_mono ?_ hu) (Subgroup.subset_closure ⟨n, le_rfl, y, rfl⟩),
      (blkU y)⁻¹ * g₁, mul_mem (inv_mem (blkU_mem_mirU m y)) hg₁, by group, fun i k hk => ?_, fun i k hk => ?_⟩
    · rintro _ ⟨k, hk, z, rfl⟩
      exact ⟨k, by omega, z, rfl⟩
    · rw [hval]
      split_ifs with h
      · rw [Matrix.one_apply_ne (fun e => by rw [e] at h; omega)]
        exact sub_self _
      · rw [sub_zero]
        by_cases hkn : n + 1 ≤ (k : ℕ)
        · exact h1 i k hkn
        · exact hg₁ i k (by omega) (by change (k : ℕ) ≤ i; omega)
    · rw [hval, dif_neg (by omega), sub_zero, h2 i k (by omega)]

theorem exists_eq_colGen_mul_blkU {n : ℕ} {u : GL (Fin a) R} (hu : u ∈ lateU R a n) :
    ∃ v ∈ colGen R a (n + 1), ∃ y : UnipotentBlockColumnIndex a n n → R, u = v * blkU y := by
  obtain ⟨v, hv, g₀, hg₀, rfl, h1, h2⟩ := exists_peel (Nat.le_succ n) hu.1
  refine ⟨v, hv, fun t => g₀.val t.1.1 t.1.2, ?_⟩
  congr 1
  ext i k
  rw [blkU_apply]
  split_ifs with h
  · rw [Matrix.one_apply_ne (fun e => by rw [e] at h; omega), zero_add]
  · rw [add_zero]
    rcases lt_trichotomy (k : ℕ) n with hk | hk | hk
    · rw [h2 i k (by omega)]; exact hu.2 i k hk
    · exact hg₀ i k (by omega) (by change (k : ℕ) ≤ i; omega)
    · exact h1 i k hk

theorem invariant_colGen {β : Sort*} {n : ℕ} {S : Type} [CommRing S] (φ : GL (Fin a) R →* GL (Fin a) S)
    (Φ : GL (Fin a) S → β) (h : ∀ k, n ≤ k → ∀ (y : UnipotentBlockColumnIndex a k k → R) g, Φ (φ (blkU y) * g) = Φ g)
    {u : GL (Fin a) R} (hu : u ∈ colGen R a n) (g : GL (Fin a) S) : Φ (φ u * g) = Φ g := by
  induction hu using Subgroup.closure_induction generalizing g with
  | mem x hx => obtain ⟨k, hk, y, rfl⟩ := hx; exact h k hk y g
  | one => rw [map_one, one_mul]
  | mul x y _ _ hx hy => rw [map_mul, mul_assoc, hx, hy]
  | inv x _ hx => rw [← hx, map_inv, mul_inv_cancel_left]

theorem map_mem_mirU {S : Type} [CommRing S] (φ : R →+* S) {m : ℕ} {g : GL (Fin a) R} (hg : g ∈ mirU R a m) :
    GeneralLinearGroup.map φ g ∈ mirU S a m := fun i k hi hk => by
  change φ (g.val i k) = _
  rw [hg i k hi hk, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isClosed_lateU [TopologicalSpace R] [T2Space R] (n : ℕ) : IsClosed (lateU R a n : Set (GL (Fin a) R)) := by
  have hc : ∀ i k : Fin a, IsClosed {g : GL (Fin a) R | g.val i k = (1 : Matrix (Fin a) (Fin a) R) i k} := fun i k =>
    isClosed_eq (Units.continuous_val.matrix_elem i k) continuous_const
  have e : (lateU R a n : Set (GL (Fin a) R)) =
      (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : n ≤ (i : ℕ), ⋂ _ : k ≤ i, {g | g.val i k = (1 : Matrix (Fin a) (Fin a) R) i k}) ∩
      ⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : (k : ℕ) < n, {g | g.val i k = (1 : Matrix (Fin a) (Fin a) R) i k} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ => hc i k).inter
    (isClosed_iInter fun i => isClosed_iInter fun k => isClosed_iInter fun _ => hc i k)

end Ring

section Adelic

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def ratMirU (E : Type) [Field E] [NumberField E] (a m : ℕ) : Subgroup (GA E a) := (mirU E a m).map (ratGL E a)

theorem discrete_of_le_range {Γ : Subgroup (GA E a)} (hΓ : Γ ≤ (ratGL E a).range) : DiscreteTopology Γ := by
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hW : IsOpen (⋂ i : Fin a, ⋂ k : Fin a,
      {g : Γ | (g : GA E a).val i k - (1 : Matrix (Fin a) (Fin a) (Ad E)) i k ∈ V}) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hVo.preimage (((Units.continuous_val.comp continuous_subtype_val).matrix_elem i k).sub continuous_const)
  convert hW using 1
  ext ⟨g, hg⟩
  obtain ⟨γ, rfl⟩ := hΓ hg
  simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h i k
    have h1 : ratGL E a γ = 1 := congrArg Subtype.val h
    rw [h1, Units.val_one, sub_self]
    exact hV0
  · intro h
    have h1 : γ = 1 := by
      ext i k
      have h2 := h i k
      have e : (ratGL E a γ).val i k - (1 : Matrix (Fin a) (Fin a) (Ad E)) i k =
          algebraMap E (Ad E) (γ.val i k - (1 : Matrix (Fin a) (Fin a) E) i k) := by
        rw [map_sub, Matrix.one_apply, Matrix.one_apply]
        congr 1
        split_ifs <;> simp
      rw [e] at h2
      exact sub_eq_zero.1 (h0 _ (hVU h2))
    subst h1
    exact Subtype.ext (map_one _)

theorem exists_compact_lateU (n : ℕ) : ∃ K : Set (GA E a), IsCompact K ∧
    ∀ u ∈ lateU (Ad E) a n, ∃ γ ∈ mirU E a 0, ratGL E a γ ∈ lateU (Ad E) a n ∧ ratGL E a γ * u ∈ K := by
  have top : ∀ n, a ≤ n → ∃ K : Set (GA E a), IsCompact K ∧
      ∀ u ∈ lateU (Ad E) a n, ∃ γ ∈ mirU E a 0, ratGL E a γ ∈ lateU (Ad E) a n ∧ ratGL E a γ * u ∈ K := by
    intro n hn
    refine ⟨{1}, isCompact_singleton, fun u hu => ⟨1, one_mem _, by rw [map_one]; exact one_mem _, ?_⟩⟩
    rw [map_one, one_mul]
    exact Units.ext (Matrix.ext fun i k => hu.2 i k (by have := k.2; omega))
  by_cases hna : a ≤ n
  · exact top n hna
  replace hna : n ≤ a := by omega
  induction hna using Nat.decreasingInduction with
  | self => exact top a le_rfl
  | of_succ n hn ih =>
    obtain ⟨K, hK, hcov⟩ := ih
    obtain ⟨-, L, hL, hLcov⟩ := isCoLat_ratV E (UnipotentBlockColumnIndex a n n)
    refine ⟨(fun p : GA E a × (UnipotentBlockColumnIndex a n n → Ad E) => p.1 * blkU p.2) '' (K ×ˢ L),
      (hK.prod hL).image (continuous_fst.mul ((continuous_posU _).comp continuous_snd)), fun u hu => ?_⟩
    obtain ⟨v, hv, y, rfl⟩ := exists_eq_colGen_mul_blkU hu
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hLcov y
    set z : UnipotentBlockColumnIndex a n n → Ad E := fun t => algebraMap E (Ad E) (c t) with hz
    have hv' := conj_mem_lateU (inv_mem (blkU_mem_mirU (n + 1) z)) (colGen_le_lateU hv)
    obtain ⟨γ, hγ, hγU, hγK⟩ := hcov _ hv'
    have hle : lateU (Ad E) a (n + 1) ≤ lateU (Ad E) a n := fun w hw => ⟨fun i k hi hk => by
      by_cases h : n + 1 ≤ (i : ℕ)
      · exact hw.1 i k h hk
      · exact hw.2 i k (by have : (k : ℕ) ≤ i := hk; omega), fun i k hk => hw.2 i k (by omega)⟩
    refine ⟨γ * blkU c, mul_mem hγ (blkU_mem_mirU 0 c), ?_, ⟨_, z + y⟩, ⟨hγK, hc⟩, ?_⟩
    · rw [map_mul, ratGL_blkU]
      exact mul_mem (hle hγU) (blkU_mem_lateU le_rfl _)
    · simp only [map_mul, ratGL_blkU, blkU_add, ← hz]
      group

end Adelic

end GlobalTheory.MirTower
