import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootExSource

theorem det_eq_one_of_unip {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (b : ι → ℕ)
    (M : Matrix ι ι k) (h : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hT : M.BlockTriangular b := fun r s hrs => by
    rw [h r s hrs.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hrs
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext r s
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, h _ _ (by rw [r.2, s.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_one]

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}

theorem mul_apply_of_inN {m : Type} {g : GL (n' ⊕ Fin c) k} (hg : InN p g)
    (x : Matrix m (n' ⊕ Fin c) k) (r : m) (s : n' ⊕ Fin c) :
    (x * g.val) r s = x r s + ∑ s', if lev p s' < lev p s then x r s' * g.val s' s else 0 := by
  have : x r s = (x * (1 : Matrix (n' ⊕ Fin c) (n' ⊕ Fin c) k)) r s := by rw [Matrix.mul_one]
  rw [this, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne, mul_zero, zero_add]
    rintro rfl
    exact lt_irrefl _ h
  · rw [hg s' s (not_lt.1 h), add_zero]

theorem affPt_nonfree (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, h]

theorem affPt_mul_nonfree {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : (affPt p x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [mul_apply_of_inN hg, affPt_nonfree _ _ _ _ h, Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ Free p (r, s') ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, lev, basePt] at h h' ⊢ <;> omega
    rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
  · rfl

theorem simpleSum_succ (g : GL (n' ⊕ Fin (c + 1)) k) :
    simpleSum g = ∑ l : Fin c, g.val (Sum.inr l.castSucc) (Sum.inr l.succ) := by
  unfold simpleSum
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Fin (c + 1) =>
    if j.val = (Fin.last c).val + 1 then g.val (Sum.inr (Fin.last c)) (Sum.inr j) else 0), add_zero]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.succ]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · simp
  · intro j _
    rw [if_neg]
    have := j.2
    simp only [Fin.val_last]
    omega

theorem ch_affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p x₀ e * g.val) = ch (affPt p x₀ e) + simpleSum g := by
  rw [simpleSum_succ, ch, ch, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_apply_of_inN hg, Finset.sum_eq_single (Sum.inr l.castSucc)]
  · rw [if_pos (by simp [lev]), affPt_nonfree _ _ _ (Sum.inr l.castSucc) (by simp [Free])]
    simp [basePt]
  · intro s' _ hs
    split_ifs with h'
    · have : ¬ Free p ((Sum.inr l : n ⊕ Fin c), s') ∧ basePt c x₀ (Sum.inr l) s' = 0 := by
        rcases s' with s' | s' <;> simp [Free, lev, basePt, Fin.ext_iff] at hs h' ⊢ <;> omega
      rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
    · rfl
  · simp

def linPart (n : Type) [DecidableEq n] (p : ℕ) (g : GL (n' ⊕ Fin (c + 1)) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g.val b.1.2 a.1.2 else 0

open Classical in
theorem det_linPart {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) : (linPart n p g).det = 1 := by
  rw [← det_transpose]
  refine det_eq_one_of_unip (fun a => lev p a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linPart, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]

open Classical in
theorem affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e * g.val = affPt p x₀ ((linPart n p g).mulVec e +
      fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases h : Free p (r, s)
  · have key : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
        ∑ s', (if h : Free p (r, s') then e ⟨(r, s'), h⟩ else 0) * g.val s' s := by
      have h1 : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
          ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), (if b.1 = r then g.val b.2 s else 0) *
            (if h : Free p b then e ⟨b, h⟩ else 0) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free p b)]
        rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ Free p b} => _)
          (fun b _ => by rw [dif_neg b.2, mul_zero]), add_zero]
        simp only [Matrix.mulVec, dotProduct, linPart, of_apply]
        refine Finset.sum_congr rfl fun b _ => by rw [dif_pos b.2]
      rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single r]
      · simp [mul_comm]
      · intro r' _ hr
        simp [hr]
      · simp
    unfold affPt
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, of_apply, dif_pos h, Pi.add_apply, key]
    simp only [Matrix.mul_apply, Matrix.sub_apply, of_apply]
    ring
  · rw [affPt_mul_nonfree hg _ _ _ _ h, affPt_nonfree _ _ _ _ h]

private theorem secondCountable_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact secondCountable_of_proper

theorem opE_om_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n' (c + 1) p, opE ψ ν p (om μ g 1 Φ) = (ψ (simpleSum g) : ℂ) • opE ψ ν p Φ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hgN
  classical
  have := secondCountable_local k
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n' (c + 1) p
  have hg : InN p g := (h1 g).1 hgN
  have hdet := h3 g hgN
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : om μ g 1 Φ = fun x => Φ (x * g.val) := by
    funext x
    simp [om, hdet, hn1]
  funext x₀
  rw [hom, Pi.smul_apply, smul_eq_mul]
  unfold opE
  set v : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2 with hv
  set F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) with hF
  let G : GL {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart n p g) (by rw [det_linPart hg]; exact one_ne_zero)
  have hGval : G.val = linPart n p g := rfl
  have hGdet : Matrix.GeneralLinearGroup.det G = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hGval, det_linPart hg]; rfl
  have hcov := (GlobalTheory.SplitWeil.linear_change_of_variables k {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} n ν).1 G
    (fun e => F (e + v))
  rw [hGdet, hn1, inv_one, one_smul, hGval] at hcov
  have hint : ∀ e, Φ (affPt p x₀ e * g.val) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (simpleSum g) : ℂ) * F ((linPart n p g).mulVec e + v) := by
    intro e
    simp only [hF]
    rw [hv, ← affPt_mul hg, ch_affPt_mul hg, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  simp only [hint]
  rw [integral_const_mul, hcov]
  congr 1
  exact integral_add_right_eq_self F v

end GlobalTheory.RootExSource
