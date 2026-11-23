import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

section Pow
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}

theorem val_pos (x : kˣ) : 0 < valuation k (x : k) := by simp [zero_lt_iff]

theorem mem_pow {e : ℤ} {s : k} : s ∈ powInt ϖ e ↔ valuation k s ≤ valuation k (ϖ : k) ^ e := by
  simp [powInt]

theorem mem_pow_zero {s : k} : s ∈ powInt ϖ 0 ↔ s ∈ 𝒪[k] := by
  rw [mem_pow, zpow_zero]; rfl

theorem zpow_mul_mem_pow {a b : ℤ} {s : k} : (ϖ : k) ^ a * s ∈ powInt ϖ b ↔ s ∈ powInt ϖ (b - a) := by
  have h := val_pos ϖ
  rw [mem_pow, mem_pow, map_mul, map_zpow₀, zpow_sub₀ h.ne', le_div_iff₀ (zpow_pos h a), mul_comm]

theorem zero_mem_pow {e : ℤ} : (0 : k) ∈ powInt ϖ e := by simp [mem_pow]

theorem pow_mul_pow {a b : ℤ} {t s : k} (ht : t ∈ powInt ϖ a) (hs : s ∈ powInt ϖ b) : t * s ∈ powInt ϖ (a + b) := by
  rw [mem_pow] at ht hs ⊢
  rw [map_mul, zpow_add₀ (val_pos ϖ).ne']
  exact mul_le_mul' ht hs

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hϖ : valuation k (ϖ : k) = uniformizer k)
include hϖ

theorem zpow_mem_pow {a b : ℤ} : (ϖ : k) ^ a ∈ powInt ϖ b ↔ b ≤ a := by
  rw [mem_pow, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ (val_pos ϖ) (hϖ ▸ uniformizer_lt_one)]

theorem pow_mono {a b : ℤ} (h : a ≤ b) {s : k} (hs : s ∈ powInt ϖ b) : s ∈ powInt ϖ a := by
  have := (zpow_mem_pow hϖ).2 h
  rw [mem_pow] at hs this ⊢
  rw [map_zpow₀] at this
  exact hs.trans this

end Pow

section Lat
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_latOf_mul {g a : GL Y k} {y : Y → k} : y ∈ latOf (g * a) ↔ (g⁻¹).val *ᵥ y ∈ latOf a := by
  simp [mem_latOf, mulVec_mulVec]

theorem latOf_mul_congr (g : GL Y k) {a b : GL Y k} (h : latOf a = latOf b) : latOf (g * a) = latOf (g * b) := by
  ext y; rw [mem_latOf_mul, mem_latOf_mul, h]

omit [Fintype Y] [DecidableEq Y] in
theorem smul_mem_lat {L : Submodule 𝒪[k] (Y → k)} {t : k} (ht : t ∈ 𝒪[k]) {y : Y → k} (hy : y ∈ L) : t • y ∈ L :=
  L.smul_mem ⟨t, ht⟩ hy

theorem mapsLat_iff {x : Matrix Y Y' k} {g : GL Y' k} {h : GL Y k} :
    MapsLat x (latOf g) (latOf h) ↔ IntM ((h⁻¹).val * x * g.val) := by
  constructor
  · intro H i j
    have : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
      have := (mulVec_mem_latOf g (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := H _ this i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro H y hy i
    have : (h⁻¹).val *ᵥ (x *ᵥ y) = ((h⁻¹).val * x * g.val) *ᵥ ((g⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (H i l) (hy l)

theorem mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (nfBasis ϖ g e z) ↔
      (fun r => y (.inl r) - y (.inr 0) * z r) ∈ latOf g ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  have key : (nfBasis ϖ g e z).val *ᵥ Sum.elim ((g⁻¹).val *ᵥ fun r => y (.inl r) - y (.inr 0) * z r)
      (fun i => (ϖ : k) ^ (-e i) * y (.inr i)) = y := by
    have h0 : ∀ a : ℤ, (ϖ : k) ^ a ≠ 0 := fun a => zpow_ne_zero _ ϖ.ne_zero
    rw [nfBasis_val, fromBlocks_mulVec]
    ext (r | i)
    · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_mulVec, Units.mul_inv, one_mulVec,
        Pi.add_apply]
      simp [mulVec, dotProduct]
      field_simp
      ring
    · simp [mulVec_diagonal, h0]
  conv_lhs => rw [← key, ← mul_one (nfBasis ϖ g e z)]
  rw [mul_one, ← mul_one (nfBasis ϖ g e z)]
  conv_lhs => enter [2]; rw [mul_one]
  rw [mulVec_mem_latOf, mem_latOf_one, Sum.forall]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [Sum.elim_inr, ← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]; simp

theorem mem_normal {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (normalBasis ϖ e z) ↔
      (∀ r, y (.inl r) - y (.inr 0) * z r ∈ 𝒪[k]) ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  rw [← nfBasis_one, mem_nf, mem_latOf_one]

omit [ValuativeRel k] in
theorem N_mulVec {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (y : n ⊕ Fin c → k) (r : n ⊕ Fin c)
    (h : ∀ s, lev p r < lev p s → y s = 0) : (u.val *ᵥ y) r = y r := by
  have hu' := (Radical.mem_N_iff u).1 hu
  conv_rhs => rw [← one_mulVec y]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases le_or_gt (lev p s) (lev p r) with hs | hs
  · exact congrArg (· * y s) (hu' r s hs)
  · simp [h s hs]

omit [ValuativeRel k] in

theorem N_fix {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (y : n ⊕ Fin c → k)
    (h : ∀ l : Fin c, 0 < l.val → y (.inr l) = 0) : u.val *ᵥ y = y := by
  ext r
  refine N_mulVec hu y r ?_
  rintro (s | s) hs
  · rcases r with r | r <;> simp [lev] at hs
  · apply h
    rcases r with r | r <;> simp [lev] at hs <;> omega

omit [ValuativeRel k] in
theorem embX_mulVec (x : GL n k) (y : n ⊕ Fin c → k) :
    (embX c x).val *ᵥ y = Sum.elim (x.val *ᵥ fun r => y (.inl r)) fun l => y (.inr l) := by
  rw [Radical.embX_val, fromBlocks_mulVec]; simp; rfl

theorem topCoord_le {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf h) i ⊆ topCoord (latOf (r * h)) i := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  rintro _ ⟨y, hy, h0, rfl⟩
  have key : ∀ l, i ≤ l → ((embX c x * u).val *ᵥ y) (.inr l) = y (.inr l) := fun l hl => by
    rw [Units.val_mul, ← mulVec_mulVec, embX_mulVec, Sum.elim_inr]
    refine N_mulVec hu y _ ?_
    rintro (s | s) hs
    · simp [lev] at hs
    · apply h0
      simp [lev] at hs
      exact lt_of_le_of_lt hl hs
  exact ⟨_, (mulVec_mem_latOf _).2 hy, fun l hl => (key l hl.le).trans (h0 l hl), key i le_rfl⟩

theorem topCoord_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf (r * h)) i = topCoord (latOf h) i := by
  refine Set.Subset.antisymm ?_ (topCoord_le hr h i)
  have := topCoord_le (inv_mem hr) (r * h) i
  rwa [inv_mul_cancel_left] at this

theorem col_mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} (i : Fin (c + 1)) {s : k}
    (hs : s ∈ powInt ϖ (e i)) :
    (Sum.elim (fun r => if i = 0 then s * z r else 0) (Pi.single i s) : n ⊕ Fin (c + 1) → k) ∈
      latOf (nfBasis ϖ g e z) := by
  refine mem_nf.2 ⟨?_, fun l => ?_⟩
  · convert zero_mem (latOf g) using 1
    ext r
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  · rw [Sum.elim_inr, Pi.single_apply]
    split_ifs with h
    · rwa [h]
    · exact zero_mem_pow

theorem topCoord_nf (g : GL n k) (e : Fin (c + 1) → ℤ) (z : n → k) (i : Fin (c + 1)) :
    topCoord (latOf (nfBasis ϖ g e z)) i = powInt ϖ (e i) := by
  ext s
  constructor
  · rintro ⟨y, hy, -, rfl⟩
    exact (mem_nf.1 hy).2 i
  · intro hs
    exact ⟨_, col_mem_nf i hs, fun l hl => by simp [hl.ne'], by simp⟩

omit [ValuativeRel k] in
theorem embX_mul_nf (x g : GL n k) (e : Fin c → ℤ) (z : n → k) :
    embX c x * nfBasis ϖ g e z = nfBasis ϖ (x * g) e (x.val *ᵥ z) := by
  ext1
  rw [Units.val_mul, nfBasis_val, nfBasis_val, Radical.embX_val, fromBlocks_multiply]
  ext (r | r) (s | s)
  · simp
  · by_cases h : s.val = 0 <;> simp [h, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  · simp
  · simp

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latOf_eq_of_KO {g : GL Y k} (hg : g ∈ KO k Y) : latOf g = latOf 1 := by
  have := (mem_stabLat_iff (g := 1) (h := g)).1 (by simpa [mem_stabLat] using hg)
  rwa [mul_one] at this

theorem om_supp {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ} (hs : ∀ x, Φ x ≠ 0 → IntM x) (g : GL Y' k) (h : GL Y k)
    (x : Matrix Y Y' k) (hx : om μ g h Φ x ≠ 0) : MapsLat x (latOf g) (latOf h) :=
  mapsLat_iff.2 (hs _ (right_ne_zero_of_mul hx))

theorem om_per (hϖ : valuation k (ϖ : k) = uniformizer k) {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ}
    (hp : ∀ x y, MaxM y → Φ (x + y) = Φ x) (g : GL Y' k) (h : GL Y k)
    (x y : Matrix Y Y' k) (hy : MapsLat y (latOf g) (latOf h)) :
    om μ g h Φ (x + (ϖ : k) • y) = om μ g h Φ x := by
  unfold om
  rw [Matrix.mul_add, Matrix.add_mul, hp]
  intro i j
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hϖ]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le uniformizer_lt_one (mapsLat_iff.1 hy i j)

end Lat

end GlobalTheory.LatClass
