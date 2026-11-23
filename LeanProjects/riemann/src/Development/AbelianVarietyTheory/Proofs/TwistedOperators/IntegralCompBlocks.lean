import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.OpELevi

section cov
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

lemma nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by
  simp [nabs]

lemma nabs_pos (x : kˣ) : 0 < nabs k x := by
  unfold nabs
  exact_mod_cast (distribHaarChar_pos (A := k) (g := x))

lemma nabs_pow (x : kˣ) (m : ℕ) : nabs k (x ^ m) = nabs k x ^ m := by
  simp [nabs]

lemma nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by
  simp [nabs]

lemma nabs_one : nabs k 1 = 1 := by
  simp [nabs]

variable [MeasurableSpace k] [BorelSpace k]

lemma integral_comp_blocks {F n J : Type} [Fintype F] [Fintype n] [DecidableEq n] [Fintype J]
    (ν : Measure k) [ν.IsAddHaarMeasure] (ι : n × J → F) (hι : Function.Injective ι)
    (A : Matrix n n k) (u : kˣ) (hu : A.det = u) (T : (F → k) → (F → k))
    (h1 : ∀ e r j, T e (ι (r, j)) = ∑ s, A r s * e (ι (s, j)))
    (h2 : ∀ e f, f ∉ Set.range ι → T e f = e f) (f : (F → k) → ℂ) :
    ∫ e, f (T e) ∂(Measure.pi fun _ => ν) =
      ((nabs k u ^ Fintype.card J)⁻¹ : ℝ) • ∫ e, f e ∂(Measure.pi fun _ => ν) := by
  classical
  let σ : (n × J) ⊕ {f // f ∉ Set.range ι} ≃ F :=
    (Equiv.sumCongr (Equiv.ofInjective ι hι) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range ι))
  have σl : ∀ x, σ (Sum.inl x) = ι x := fun x => rfl
  have σr : ∀ x, σ (Sum.inr x) = x.1 := fun x => rfl
  let G : Matrix F F k := Matrix.reindex σ σ (fromBlocks (blockDiagonal fun _ : J => A) 0 0 1)
  have hG : G.det = (u ^ Fintype.card J : kˣ) := by
    simp [G, det_blockDiagonal, hu]
  have hG0 : G.det ≠ 0 := by rw [hG]; exact Units.ne_zero _
  have hT : ∀ e, T e = G.mulVec e := by
    intro e
    funext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [Matrix.mulVec, dotProduct, ← σ.sum_comp]
    rcases y with ⟨r, j⟩ | y
    · have : σ.symm (ι (r, j)) = Sum.inl (r, j) := by rw [← σl]; simp
      simp [G, this, σl, σr, h1, Fintype.sum_sum_type, Fintype.sum_prod_type, blockDiagonal_apply]
    · rw [σr, h2 _ _ y.2]
      have : σ.symm y.1 = Sum.inr y := by rw [← σr]; simp
      simp [G, this, Fintype.sum_sum_type, Matrix.one_apply, σr]
  have key := (GlobalTheory.SplitWeil.linear_change_of_variables k F F ν).1 (Matrix.GeneralLinearGroup.mkOfDetNeZero G hG0) f
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero G hG0)
      = u ^ Fintype.card J := by
    ext
    rw [← hG]; rfl
  rw [hd, nabs_pow] at key
  simp only [hT]
  exact key
end cov

section alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

def ext (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Free p (r, s) then e ⟨(r, s), h⟩ else 0

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma affPt_eq (p : ℕ) (x₀ : Matrix n n' k) (e) :
    affPt (c := c) p x₀ e = basePt c x₀ + ext p e := rfl

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma ext_free (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r s)
    (h : Free p (r, s)) : ext p e r s = e ⟨(r, s), h⟩ := by
  simp [ext, h]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma ext_not_free (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r s)
    (h : ¬ Free p (r, s)) : ext p e r s = 0 := by
  simp [ext, h]

omit [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma left_inl (A : Matrix n n k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s) :
    ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x) (Sum.inl r) s
      = ∑ t, A r t * x (Sum.inl t) s := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

omit [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma left_inr (A : Matrix n n k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s) :
    ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x) (Sum.inr r) s
      = x (Sum.inr r) s := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
lemma right_inl (A : Matrix n' n' k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s) :
    (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) r (Sum.inl s)
      = ∑ t, Aᵀ s t * x r (Sum.inl t) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, mul_comm]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
lemma right_inr (A : Matrix n' n' k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s) :
    (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) r (Sum.inr s)
      = x r (Sum.inr s) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

def TL (p : ℕ) (A : Matrix n n k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs =>
  ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * ext p e) rs.1.1 rs.1.2

def TR (p : ℕ) (A : Matrix n' n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs =>
  (ext p e * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) rs.1.1 rs.1.2

omit [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma left_affPt (p : ℕ) (A : Matrix n n k) (x₀ : Matrix n n' k) (e) :
    (fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * affPt (c := c) p x₀ e
      = affPt p (A * x₀) (TL p A e) := by
  rw [affPt_eq, affPt_eq, Matrix.mul_add]
  congr 1
  · simp [basePt, fromBlocks_multiply]
  · ext r s
    by_cases h : Free p (r, s)
    · rw [ext_free _ _ _ _ h]; rfl
    · rw [ext_not_free _ _ _ _ h]
      rcases r with r | r
      · rw [left_inl]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [ext_not_free, mul_zero]
        rcases s with s | s <;> exact h
      · rw [left_inr, ext_not_free _ _ _ _ h]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
lemma right_affPt (p : ℕ) (A : Matrix n' n' k) (x₀ : Matrix n n' k) (e) :
    affPt (c := c) p x₀ e * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)
      = affPt p (x₀ * A) (TR p A e) := by
  rw [affPt_eq, affPt_eq, Matrix.add_mul]
  congr 1
  · simp [basePt, fromBlocks_multiply]
  · ext r s
    by_cases h : Free p (r, s)
    · rw [ext_free _ _ _ _ h]; rfl
    · rw [ext_not_free _ _ _ _ h]
      rcases s with s | s
      · rw [right_inl]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [ext_not_free, mul_zero]
        rcases r with r | r <;> exact h
      · rw [right_inr, ext_not_free _ _ _ _ h]

omit [DecidableEq n] [Fintype n'] [DecidableEq n'] in
lemma ch_left (A : Matrix n n k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x) = ch x := by
  simp only [ch, left_inr]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
lemma ch_right (A : Matrix n' n' k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = ch x := by
  simp only [ch, right_inr]

lemma card_cols (p : ℕ) (_ : 1 ≤ p) (h2 : p ≤ c) :
    (Fintype.card {i : Fin (c + 1) // p < i.val + 1} : ℝ) = c + 1 - p := by
  have : Fintype.card {i : Fin (c + 1) // p < i.val + 1} = c + 1 - p := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin (c + 1) => p < i.val + 1) = Finset.Ici ⟨p, by omega⟩ := by
      ext i; simp [Fin.le_def]
    rw [this, Fin.card_Ici]
  rw [this, Nat.cast_sub (by omega)]; push_cast; ring

lemma card_rows (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ c) :
    (Fintype.card {l : Fin c // l.val + 1 < p} : ℝ) = p - 1 := by
  have : Fintype.card {l : Fin c // l.val + 1 < p} = p - 1 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun l : Fin c => l.val + 1 < p) = Finset.Iio ⟨p - 1, by omega⟩ := by
      ext i; simp [Fin.lt_def]; omega
    rw [this, Fin.card_Iio]
  rw [this, Nat.cast_sub (by omega)]; push_cast; ring

lemma embX_val (g : GL n k) : (embX c g).val = fromBlocks g.val 0 0 1 := rfl

lemma det_embX (g : GL n k) :
    Matrix.GeneralLinearGroup.det (embX c g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [embX_val]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [DecidableEq n'] in
lemma integral_left (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (A : Matrix n n k) (u : kˣ) (hu : A.det = u)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => Φ ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x)) x₀ =
      ((nabs k u ^ Fintype.card {i : Fin (c + 1) // p < i.val + 1})⁻¹ : ℝ) • opE ψ ν p Φ (A * x₀) := by
  classical
  unfold opE
  rw [← integral_comp_blocks ν
    (fun x : n × {i : Fin (c + 1) // p < i.val + 1} =>
      (⟨(Sum.inl x.1, Sum.inr x.2.1), x.2.2⟩ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}))
    ?_ A u hu (TL p A) ?_ ?_]
  · simp only [← left_affPt, ch_left]
    rfl
  · rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
    have h' := congrArg Subtype.val h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h' ⊢
    exact h'
  · intro e r j
    simp only [TL, left_inl]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ext_free p e (Sum.inl t) (Sum.inr j.1) j.2]
  · rintro e ⟨⟨r | r, s⟩, h⟩ hf
    · rcases s with s | s
      · exact h.elim
      · exact (hf ⟨(r, ⟨s, h⟩), rfl⟩).elim
    · simp only [TL, left_inr]
      rw [ext_free]

omit [DecidableEq n] in
lemma integral_right (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (A : Matrix n' n' k) (u : kˣ) (hu : A.det = u)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => Φ (x * (fromBlocks A 0 0 1 :
        Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k))) x₀ =
      ((nabs k u ^ Fintype.card {l : Fin c // l.val + 1 < p})⁻¹ : ℝ) • opE ψ ν p Φ (x₀ * A) := by
  classical
  unfold opE
  rw [← integral_comp_blocks ν
    (fun x : n' × {l : Fin c // l.val + 1 < p} =>
      (⟨(Sum.inr x.2.1, Sum.inl x.1), x.2.2⟩ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}))
    ?_ Aᵀ u (by rw [det_transpose, hu]) (TR p A) ?_ ?_]
  · simp only [← right_affPt, ch_right]
    rfl
  · rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
    have h' := congrArg Subtype.val h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h' ⊢
    exact h'.symm
  · intro e r j
    simp only [TR, right_inl]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ext_free p e (Sum.inr j.1) (Sum.inl t) j.2]
  · rintro e ⟨⟨r, s | s⟩, h⟩ hf
    · rcases r with r | r
      · exact h.elim
      · exact (hf ⟨(s, ⟨r, h⟩), rfl⟩).elim
    · simp only [TR, right_inr]
      rw [ext_free]

omit [DecidableEq n] [DecidableEq n'] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [BorelSpace k] in
lemma opE_const_mul (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => a * Φ x) x₀ = a * opE ψ ν p Φ x₀ := by
  unfold opE
  rw [← integral_const_mul]
  simp only [mul_assoc]

end alg

end GlobalTheory.RootEx.OpELevi

open GlobalTheory.RootEx.OpELevi in

theorem GlobalTheory.RootEx.opE_om_embX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g : GL n k, opE ψ ν p (om μ 1 (embX c g) Φ) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) • om μ 1 g (opE ψ ν p Φ)) ∧ ∀ g : GL n' k, opE ψ ν p (om μ (embX (c + 1) g) 1 Φ) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - p) : ℝ) : ℂ) • om μ g 1 (opE ψ ν p Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p h1 h2 ψ ν _ μ Φ
  refine ⟨fun g => ?_, fun g => ?_⟩
  · funext x₀
    unfold om
    rw [opE_const_mul]
    simp only [← map_inv, embX_val, Units.val_one, Matrix.mul_one, det_embX, Pi.smul_apply,
      smul_eq_mul, map_one, nabs_one, Real.one_rpow, Complex.ofReal_one]
    erw [integral_left p ψ ν (g⁻¹).val (Matrix.GeneralLinearGroup.det g)⁻¹ (by rw [← map_inv]; rfl) Φ]
    have hp := nabs_pos (Matrix.GeneralLinearGroup.det g)
    set t := nabs k (Matrix.GeneralLinearGroup.det g) with ht
    have key : t ^ (-(Fintype.card (n' ⊕ Fin (c + 1)) : ℝ) / 2) *
        (t⁻¹ ^ Fintype.card {i : Fin (c + 1) // p < i.val + 1})⁻¹ =
        t ^ (((c : ℝ) + 1) / 2 - p) * t ^ (-(Fintype.card n' : ℝ) / 2) := by
      rw [inv_pow, inv_inv, ← Real.rpow_natCast, card_cols p h1 h2, ← Real.rpow_add hp,
        ← Real.rpow_add hp]
      congr 1
      simp only [Fintype.card_sum, Fintype.card_fin]
      push_cast; ring
    rw [nabs_inv, ← ht, Complex.real_smul]
    have key' := congrArg (fun r : ℝ => (r : ℂ)) key
    simp only [Complex.ofReal_mul] at key'
    linear_combination (((μ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ) *
      opE ψ ν p Φ ((g⁻¹).val * x₀)) * key'
  · funext x₀
    unfold om
    rw [opE_const_mul]
    simp only [inv_one, embX_val, Units.val_one, Matrix.one_mul, det_embX, Pi.smul_apply,
      smul_eq_mul, map_one, nabs_one, Real.one_rpow, Complex.ofReal_one]
    erw [integral_right p ψ ν g.val (Matrix.GeneralLinearGroup.det g) rfl Φ]
    have hp := nabs_pos (Matrix.GeneralLinearGroup.det g)
    set t := nabs k (Matrix.GeneralLinearGroup.det g) with ht
    have key : t ^ ((Fintype.card (n ⊕ Fin c) : ℝ) / 2) *
        (t ^ Fintype.card {l : Fin c // l.val + 1 < p})⁻¹ =
        t ^ (((c : ℝ) + 2) / 2 - p) * t ^ ((Fintype.card n : ℝ) / 2) := by
      rw [← Real.rpow_natCast, card_rows p h1 h2, ← Real.rpow_neg hp.le, ← Real.rpow_add hp,
        ← Real.rpow_add hp]
      congr 1
      simp only [Fintype.card_sum, Fintype.card_fin]
      push_cast; ring
    rw [Complex.real_smul]
    have key' := congrArg (fun r : ℝ => (r : ℂ)) key
    simp only [Complex.ofReal_mul] at key'
    linear_combination (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      opE ψ ν p Φ (x₀ * g.val)) * key'
