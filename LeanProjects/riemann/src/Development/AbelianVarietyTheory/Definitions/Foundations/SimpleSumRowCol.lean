import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem inN_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) : g.val.BlockTriangular (lev p) := by
  intro r s h
  rw [hg r s h.le, Matrix.one_apply_ne]
  rintro rfl; exact lt_irrefl _ h

theorem mul_entry {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (r s) (hrs : lev p s ≤ lev p r) : (g.val * h) r s = h r s := by
  have : (g.val * h) r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * h) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : lev p t ≤ lev p r
    · rw [hg r t ht]
    · rw [hh (show lev p s < lev p t by omega)]; simp
  rw [this, Matrix.one_mul]

def Nsub (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | InN p g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    rw [Units.val_mul, mul_entry ha (inN_tri hb) r s hrs, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have h1 : (a⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular (inN_tri ha)
    rw [← mul_entry ha h1 r s hrs, Units.mul_inv]

theorem mem_N_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ N k n c p ↔ InN p g := by
  have : N k n c p = Nsub k n c p := Subgroup.closure_eq (Nsub k n c p)
  rw [this]; rfl

theorem rowE_mem (p : ℕ) (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  rw [mem_N_iff]
  rintro (r | r) (s | s) h <;> simp [rowE, lowU, lev, Matrix.one_apply] at h ⊢
  omega

theorem colE_mem (p : ℕ) (β : n → k) : colE c (p + 1) β ∈ N k n c p := by
  rw [mem_N_iff]
  rintro (r | r) (s | s) h <;> simp [colE, upU, lev, Matrix.one_apply] at h ⊢
  omega

theorem rowE_not_mem (l : Fin c) (u : n → k) (hu : u ≠ 0) : rowE c (l.val + 1) u ∉ N k n c (l.val + 1) := by
  rw [mem_N_iff]
  intro h
  apply hu
  funext s
  simpa [rowE, lowU] using h (Sum.inr l) (Sum.inl s) (by simp [lev])

theorem simple_entry_mul {p : ℕ} {g h : GL (n ⊕ Fin c) k} (hg : InN p g) (hh : InN p h) (i j : Fin c)
    (hij : j.val = i.val + 1) : (g * h).val (Sum.inr i) (Sum.inr j) =
      g.val (Sum.inr i) (Sum.inr j) + h.val (Sum.inr i) (Sum.inr j) := by
  have hne : (Sum.inr i : n ⊕ Fin c) ≠ Sum.inr j := by
    intro e; have := Sum.inr.inj e; subst this; omega
  rw [Units.val_mul, Matrix.mul_apply]
  have key : ∀ t : n ⊕ Fin c, g.val (Sum.inr i) t * h.val t (Sum.inr j) =
      (if t = Sum.inr j then g.val (Sum.inr i) (Sum.inr j) else 0) +
      (if t = Sum.inr i then h.val (Sum.inr i) (Sum.inr j) else 0) := by
    intro t
    have li : lev p (Sum.inr i : n ⊕ Fin c) = i.val + 1 := rfl
    have lj : lev p (Sum.inr j : n ⊕ Fin c) = j.val + 1 := rfl
    by_cases ht : lev p t ≤ i.val + 1
    · have htj : t ≠ Sum.inr j := by rintro rfl; omega
      rw [hg _ t (by omega)]
      by_cases hti : t = Sum.inr i
      · subst hti; simp [htj]
      · simp [htj, hti, Matrix.one_apply, Ne.symm hti]
    · have hti : t ≠ Sum.inr i := by rintro rfl; omega
      rw [hh t _ (by omega)]
      by_cases htj : t = Sum.inr j
      · subst htj; simp [hti]
      · simp [htj, hti, Matrix.one_apply]
  simp [key, Finset.sum_add_distrib]

theorem simpleSum_mul {p : ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (hh : h ∈ N k n c p) :
    simpleSum (g * h) = simpleSum g + simpleSum h := by
  rw [mem_N_iff] at hg hh
  simp only [simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact simple_entry_mul hg hh i j hij
  · simp

theorem conj_mem {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ N k n c p := by
  rw [mem_N_iff] at hu ⊢
  rw [← map_inv]
  have h11 : u.val.toBlocks₁₁ = 1 := by
    ext r s
    have := hu (Sum.inl r) (Sum.inl s) le_rfl
    simpa [Matrix.one_apply, toBlocks₁₁] using this
  have hv : ((embX c g⁻¹) * u * embX c g).val = fromBlocks 1 ((g⁻¹).val * u.val.toBlocks₁₂)
      (u.val.toBlocks₂₁ * g.val) u.val.toBlocks₂₂ := by
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val, h11]
    simp [embX, fromBlocks_multiply]
  rintro (r | r) (s | s) h <;> rw [hv]
  · simp [Matrix.one_apply]
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [Matrix.mul_apply, toBlocks₁₂, this]
  · have : ∀ t, u.val (Sum.inr r) (Sum.inl t) = 0 := fun t => by
      simpa using hu (Sum.inr r) (Sum.inl t) h
    simp [Matrix.mul_apply, toBlocks₂₁, this]
  · simpa [toBlocks₂₂] using hu (Sum.inr r) (Sum.inr s) h

theorem simpleSum_conj (u : GL (n ⊕ Fin c) k) (g : GL n k) :
    simpleSum ((embX c g)⁻¹ * u * embX c g) = simpleSum u := by
  rw [← map_inv]
  have hv : ∀ i j, ((embX c g⁻¹) * u * embX c g).val (Sum.inr i) (Sum.inr j) = u.val (Sum.inr i) (Sum.inr j) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val]
    simp [embX, fromBlocks_multiply]
  simp only [simpleSum, hv]

theorem simpleSum_row_col (l : Fin c) (hl : l.val + 1 < c) (u β : n → k) :
    simpleSum (rowE c (l.val + 1) u * colE c (l.val + 1 + 1) β * (rowE c (l.val + 1) u)⁻¹) = u ⬝ᵥ β := by
  have hv : ∀ i j : Fin c, (rowE c (l.val + 1) u * colE c (l.val + 1 + 1) β * (rowE c (l.val + 1) u)⁻¹).val
      (Sum.inr i) (Sum.inr j) = (if i = l ∧ j.val = l.val + 1 then u ⬝ᵥ β else 0) + (1 : Matrix _ _ k) i j := by
    intro i j
    show ((fromBlocks 1 0 _ 1 * fromBlocks 1 _ 0 1 * fromBlocks 1 0 _ 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) _ _ = _
    simp only [fromBlocks_multiply, fromBlocks_apply₂₂]
    by_cases hi : i = l <;> by_cases hj : j.val = l.val + 1 <;>
      simp [Matrix.mul_apply, Matrix.one_apply, dotProduct, hi, hj, Fin.val_inj]
  simp only [simpleSum, hv]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single ⟨l.val + 1, hl⟩]
  · simp [Matrix.one_apply, Fin.ext_iff]
  · intro j _ hj
    rw [if_neg]; intro h; exact hj (Fin.ext h)
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h1 h2
    · exact absurd h2.1 hi
    · have : i ≠ j := by rintro rfl; omega
      simp [this]
    · rfl
  · simp

theorem affPt_block {n' : Type*} [Fintype n'] [DecidableEq n'] (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n) (s : n') :
    affPt p x₀ e (Sum.inl r) (Sum.inl s) = x₀ r s := by
  simp [affPt, basePt, Free]

theorem free_last {n' : Type*} (p : ℕ) (hp : p ≤ c) (r : n ⊕ Fin c) :
    Free (n := n) (n' := n') p (r, Sum.inr (Fin.last c)) := by
  rcases r with r | r <;> simp [Free]
  omega

def mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s => if h : lev p r < lev p s then e ⟨(r, s), h⟩ else (1 : Matrix _ _ k) r s

theorem det_mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    (mkN p e).det = 1 := by
  have ht : (mkN p e).BlockTriangular (lev p) := by
    intro r s h
    have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, not_lt.2 h.le, this]
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (mkN p e).toSquareBlock (lev p) a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, mkN, hr, hs, Matrix.one_apply]
  rw [this, det_one]

def mkNel (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) : N k n c p :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mkN p e) (by rw [det_mkN]; exact one_ne_zero), by
    rw [mem_N_iff]
    intro r s h
    show mkN p e r s = _
    simp [mkN, not_lt.2 h]⟩

section meas
variable [MeasurableSpace k]

theorem coord_embedding (p : ℕ) : MeasurableEmbedding
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) ∧ Function.Surjective
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
  have hs : Function.Surjective
      (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
    intro e
    refine ⟨mkNel p e, ?_⟩
    funext rs
    show mkN p e _ _ = _
    simp [mkN, rs.2]
  refine ⟨MeasurableEmbedding.of_measurable_inverse (g := mkNel (k := k) p) ?_ ?_ ?_ ?_, hs⟩
  · refine measurable_pi_lambda _ fun rs => ?_
    have h1 : Measurable (fun g : GL (n ⊕ Fin c) k => g.val) := comap_measurable _
    have h2 : Measurable (fun m : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => m rs.1.1 rs.1.2) :=
      (measurable_pi_apply rs.1.2).comp (measurable_pi_apply rs.1.1)
    exact h2.comp (h1.comp measurable_subtype_coe)
  · rw [hs.range_eq]; exact MeasurableSet.univ
  · refine Measurable.subtype_mk ?_
    refine measurable_comap_iff.2 ?_
    refine measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s => ?_
    show Measurable fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k => mkN (k := k) p e r s
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact measurable_pi_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact measurable_const
  · intro g
    ext r s
    show mkN (k := k) p (fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) r s = _
    by_cases h : lev p r < lev p s
    · simp [mkN, h]
    · simp only [mkN, Matrix.of_apply, dif_neg h]
      exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm

theorem volN_ne_zero (ν : Measure k) [SigmaFinite ν] (hν : ν ≠ 0) (p : ℕ) : volN ν n c p ≠ 0 := by
  classical
  intro h
  have h1 : volN ν n c p Set.univ = 0 := by rw [h]; rfl
  unfold volN at h1
  rw [(coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply, Set.image_univ, (coord_embedding (k := k) (n := n) (c := c) p).2.range_eq, Measure.pi_univ] at h1
  obtain ⟨_, _, h2⟩ := Finset.prod_eq_zero_iff.1 h1
  exact hν (Measure.measure_univ_eq_zero.1 h2)

end meas

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def chi (ψ : AddChar k Circle) (p : ℕ) (h : GL (n ⊕ Fin c) k) : ℂ :=
  if h ∈ N k n c p then (ψ (simpleSum h) : ℂ) else 0

theorem chi_mul (ψ : AddChar k Circle) (p : ℕ) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (h) :
    chi ψ p (u * h) = (ψ (simpleSum u) : ℂ) * chi ψ p h := by
  unfold chi
  by_cases hh : h ∈ N k n c p
  · rw [if_pos hh, if_pos (mul_mem hu hh), simpleSum_mul hu hh, AddChar.map_add_eq_mul]; simp
  · rw [if_neg hh, if_neg (by rwa [Subgroup.mul_mem_cancel_left _ hu]), mul_zero]

def reg (G : Type*) [Group G] : Representation ℂ G (G →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g * ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

theorem reg_single {G : Type*} [Group G] (g h : G) (x : ℂ) :
    reg G g (Finsupp.single h x) = Finsupp.single (g * h) x := by simp [reg]

theorem exists_isPos (ψ : AddChar k Circle) (p : ℕ) :
    ∃ b : (GL n k →₀ ℂ) →ₗ[ℂ] (GL (n ⊕ Fin c) k →₀ ℂ) →ₗ[ℂ] ℂ,
      IsPos ψ p (reg (GL n k))
        (reg (GL (n ⊕ Fin c) k)) b ∧ b ≠ 0 := by
  let w : GL n k → ℂ := fun g =>
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ)
  have hw : ∀ g g', w (g * g') = w g * w g' := by
    intro g g'
    simp only [w, nabs, map_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]; push_cast; rfl
  let b : (GL n k →₀ ℂ) →ₗ[ℂ] (GL (n ⊕ Fin c) k →₀ ℂ) →ₗ[ℂ] ℂ :=
    Finsupp.linearCombination ℂ fun g => Finsupp.linearCombination ℂ fun h => w g * chi ψ p ((embX c g)⁻¹ * h)
  have hb : ∀ g h x y, b (Finsupp.single g x) (Finsupp.single h y) = x * (y * (w g * chi ψ p ((embX c g)⁻¹ * h))) := by
    intro g h x y; simp [b]
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · intro φ u hu v
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add a a' h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]; ring
    | single g x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add a a' h1 h2 => simp only [map_add, h1, h2]; ring
      | single h y =>
        rw [reg_single, hb, hb,
          show (embX c g)⁻¹ * (u * h) = ((embX c g)⁻¹ * u * embX c g) * ((embX c g)⁻¹ * h) by group,
          chi_mul ψ p (conj_mem hu g), simpleSum_conj]
        ring
  · intro g' φ v
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add a a' h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]; ring
    | single g x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add a a' h1 h2 => simp only [map_add, h1, h2]; ring
      | single h y =>
        rw [reg_single, reg_single, hb, hb,
          hw, show (embX c (g' * g))⁻¹ * (embX c g' * h) = (embX c g)⁻¹ * h by rw [map_mul]; group]
        simp only [w]; ring
  · intro h0
    have := hb 1 1 1 1
    rw [h0] at this
    simp [w, nabs, chi, one_mem] at this
    exact Circle.coe_ne_zero _ this.symm

end GlobalTheory.RootEx.Model
