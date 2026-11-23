import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.BlkOneMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorConstantTermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOrdLConjGramDetOfUnitGramAdicCompletion

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun Formalism.UG.P
open GlobalTheory.ResW.HeckeCT (Tri)
open PositivityTheory.Rg.BcB.G8 (K2)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Tri

variable {R : Type} [CommRing R] {r s N : ℕ} {h : r + s = N}

private theorem blocks_inv (A A' : Matrix (Fin r) (Fin r) R) (D D' : Matrix (Fin s) (Fin s) R) (X : Matrix (Fin r) (Fin s) R)
    (h1 : A * A' = 1) (h2 : D * D' = 1) :
    Matrix.fromBlocks A X 0 D * Matrix.fromBlocks A' (-(A' * X * D')) 0 D' = 1 := by
  have e : A * -(A' * X * D') + X * D' = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp
  rw [Matrix.fromBlocks_multiply, e, h1, h2]
  simp [Matrix.fromBlocks_one]

private theorem tri_inv {g : GL (Fin N) R} {m : GL (Fin r) R × GL (Fin s) R} (a : Tri h g m) : Tri h g⁻¹ m⁻¹ := by
  obtain ⟨X, a⟩ := a
  refine ⟨-((m.1⁻¹).val * X * (m.2⁻¹).val), ?_⟩
  have e1 : (g⁻¹).val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) * g.val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← Units.val_mul]
    simp
  have e2 := blocks_inv m.1.val (m.1⁻¹).val m.2.val (m.2⁻¹).val X (Units.mul_inv m.1) (Units.mul_inv m.2)
  rw [a] at e1
  calc _ = (g⁻¹).val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) * (Matrix.fromBlocks m.1.val X 0 m.2.val * Matrix.fromBlocks (m.1⁻¹).val (-((m.1⁻¹).val * X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) := by rw [e2, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]; rfl

private def nU (h : r + s = N) (X : Matrix (Fin r) (Fin s) R) : GL (Fin N) R where
  val := Matrix.reindex (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) (Matrix.fromBlocks 1 X 0 1)
  inv := Matrix.reindex (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) (Matrix.fromBlocks 1 (-X) 0 1)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

private theorem nU_sub (X : Matrix (Fin r) (Fin s) R) :
    (nU h X).val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) = Matrix.fromBlocks 1 X 0 1 := by
  change (Matrix.reindex (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) (Matrix.fromBlocks 1 X 0 1)).submatrix _ _ = _
  simp

private theorem gl_ext {g g' : GL (Fin N) R}
    (e : g.val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) = g'.val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h)) : g = g' := by
  refine Units.ext ?_
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.ResW.blkE h).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.ResW.blkE h).surjective b
  exact congrFun (congrFun e a) b

private theorem nU_add (X Y : Matrix (Fin r) (Fin s) R) : nU h (X + Y) = nU h X * nU h Y := by
  refine gl_ext (h := h) ?_
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (GlobalTheory.ResW.blkE h), nU_sub, nU_sub, nU_sub, Matrix.fromBlocks_multiply]
  simp [add_comm]

private theorem nU_neg (X : Matrix (Fin r) (Fin s) R) : (nU h X)⁻¹ = nU h (-X) := by
  rw [inv_eq_iff_mul_eq_one, ← nU_add]
  refine gl_ext (h := h) ?_
  rw [nU_sub]
  simp [Matrix.fromBlocks_one]

private theorem tri_of_eq {g : GL (Fin N) R} {m : GL (Fin r) R × GL (Fin s) R} {Y : Matrix (Fin r) (Fin s) R}
    (a : g.val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) = Matrix.fromBlocks m.1.val Y 0 m.2.val) :
    g = GlobalTheory.ResW.blk h m * nU h ((m.1⁻¹).val * Y) := by
  refine gl_ext (h := h) ?_
  have e : m.1.val * ((m.1⁻¹).val * Y) = Y := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]; simp
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (GlobalTheory.ResW.blkE h), a, nU_sub, GlobalTheory.ResW.HeckeCT.blk_sub, Matrix.fromBlocks_multiply]
  simp [e]

private theorem tri_blk_nU (m : GL (Fin r) R × GL (Fin s) R) (X : Matrix (Fin r) (Fin s) R) :
    Tri h (GlobalTheory.ResW.blk h m * nU h X) m := by
  refine ⟨m.1.val * X, ?_⟩
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (GlobalTheory.ResW.blkE h), nU_sub, GlobalTheory.ResW.HeckeCT.blk_sub, Matrix.fromBlocks_multiply]
  simp

end Tri

section Int

variable {L : Type} [Field L] {O : Subring L} {r s N : ℕ} {h : r + s = N}

private theorem tri_int {k : GL (Fin N) L} {m : GL (Fin r) L × GL (Fin s) L} (a : Tri h k m) (hk : k ∈ GLint (Fin N) O) :
    m.1 ∈ GLint (Fin r) O ∧ m.2 ∈ GLint (Fin s) O := by
  have key : ∀ {k : GL (Fin N) L} {m : GL (Fin r) L × GL (Fin s) L}, Tri h k m → k ∈ GLint (Fin N) O →
      (∀ a b, m.1.val a b ∈ O) ∧ ∀ a b, m.2.val a b ∈ O := by
    rintro k m ⟨X, a⟩ hk
    constructor
    · intro i j
      have := congrFun (congrFun a (.inl i)) (.inl j)
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁] at this
      rw [← this]
      exact satake_glint_entry O hk _ _
    · intro i j
      have := congrFun (congrFun a (.inr i)) (.inr j)
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂] at this
      rw [← this]
      exact satake_glint_entry O hk _ _
  obtain ⟨a1, a2⟩ := key a hk
  obtain ⟨b1, b2⟩ := key (tri_inv a) (inv_mem hk)
  exact ⟨satake_mem_glint O _ a1 b1, satake_mem_glint O _ a2 b2⟩

private theorem nU_mem {X : Matrix (Fin r) (Fin s) L} (hX : ∀ i j, X i j ∈ O) : nU h X ∈ GLint (Fin N) O := by
  have key : ∀ {X : Matrix (Fin r) (Fin s) L}, (∀ i j, X i j ∈ O) → ∀ a b, (nU h X).val a b ∈ O := by
    intro X hX a b
    obtain ⟨a, rfl⟩ := (GlobalTheory.ResW.blkE h).surjective a
    obtain ⟨b, rfl⟩ := (GlobalTheory.ResW.blkE h).surjective b
    have := congrFun (congrFun (nU_sub (h := h) X) a) b
    rw [Matrix.submatrix_apply] at this
    rw [this]
    rcases a with a | a <;> rcases b with b | b
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]
    · exact hX a b
    · exact O.zero_mem
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]
  refine satake_mem_glint O _ (key hX) ?_
  rw [nU_neg]
  exact key fun i j => by simpa using O.neg_mem (hX i j)

private theorem nU_int {X : Matrix (Fin r) (Fin s) L} (hX : nU h X ∈ GLint (Fin N) O) (i : Fin r) (j : Fin s) : X i j ∈ O := by
  have := congrFun (congrFun (nU_sub (h := h) X) (.inl i)) (.inr j)
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂] at this
  rw [← this]
  exact satake_glint_entry O hX _ _

end Int

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} {w : Pl E}

private theorem bblk_eq (h : a + b = n) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GlobalTheory.BCT.blk h w m X = GlobalTheory.ResW.blk h m * nU h X := by
  have t : (GlobalTheory.ResW.blk h m * nU h X).val.submatrix (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) =
      Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val := by
    rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (GlobalTheory.ResW.blkE h), nU_sub, GlobalTheory.ResW.HeckeCT.blk_sub,
      Matrix.fromBlocks_multiply]
    simp
  have e : Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = (GlobalTheory.ResW.blk h m * nU h X).val := by
    change Matrix.reindex (GlobalTheory.ResW.blkE h) (GlobalTheory.ResW.blkE h) _ = _
    rw [← t]
    simp [Matrix.reindex_apply]
  have hu : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := e ▸ Units.isUnit _
  apply Units.ext
  unfold GlobalTheory.BCT.blk
  simp only
  rw [dif_pos hu, IsUnit.unit_spec, e]

private theorem mem_intMat {X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))} :
    X ∈ intMat a b w ↔ ∀ i j, (Multiplicative.toAdd X) i j ∈ Ov E w := by
  have hO : ∀ x : w.adicCompletion E, x ∈ Ov E w ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  constructor
  · intro hX
    induction hX using Subgroup.closure_induction with
    | mem x hx => exact fun i j => (hO _).2 (hx i j)
    | one => exact fun i j => (Ov E w).zero_mem
    | mul x y _ _ hx hy => exact fun i j => (Ov E w).add_mem (hx i j) (hy i j)
    | inv x _ hx => exact fun i j => (Ov E w).neg_mem (hx i j)
  · exact fun hX => Subgroup.subset_closure fun i j => (hO _).1 (hX i j)

private def FF (h : a + b = n) (m : GLw a w × GLw b w) (g : GLw n w) : ℂ :=
  if ∃ k ∈ GlobalTheory.LFun.KGL w n, Tri h (g * k) m then 1 else 0

private theorem FF_right (h : a + b = n) (m : GLw a w × GLw b w) (g : GLw n w) (k : GLw n w) (hk : k ∈ GlobalTheory.LFun.KGL w n) :
    FF h m (g * k) = FF h m g := by
  have : (∃ k' ∈ GlobalTheory.LFun.KGL w n, Tri h (g * k * k') m) ↔ ∃ k' ∈ GlobalTheory.LFun.KGL w n, Tri h (g * k') m := by
    constructor
    · rintro ⟨k', hk', t⟩
      exact ⟨k * k', mul_mem hk hk', by rwa [← mul_assoc]⟩
    · rintro ⟨k', hk', t⟩
      exact ⟨k⁻¹ * k', mul_mem (inv_mem hk) hk', by simpa [mul_assoc] using t⟩
  simp only [FF, this]

private theorem triangular_decomposition_right_translate {h : a + b = n} {m m' : GLw a w × GLw b w} {g g' : GLw n w} (t : Tri h g m') (t' : Tri h g' m') :
    (∃ k ∈ GlobalTheory.LFun.KGL w n, Tri h (g * k) m) → ∃ k ∈ GlobalTheory.LFun.KGL w n, Tri h (g' * k) m := by
  rintro ⟨k, hk, u⟩
  refine ⟨k, hk, ?_⟩
  have := (t'.mul (tri_inv t)).mul u
  simpa [mul_assoc] using this

private theorem FF_tri (h : a + b = n) (m : GLw a w × GLw b w) (g : GLw n w) (m' : GLw a w × GLw b w) (t : Tri h g m') :
    FF h m g = FF h m (GlobalTheory.ResW.blk h m') := by
  have t' := GlobalTheory.ResW.HeckeCT.tri_blk h m'
  simp only [FF, show (∃ k ∈ GlobalTheory.LFun.KGL w n, Tri h (g * k) m) ↔ _ from ⟨triangular_decomposition_right_translate t t', triangular_decomposition_right_translate t' t⟩]

private theorem FF_bblk (h : a + b = n) (m : GLw a w × GLw b w) (X) : FF h m (GlobalTheory.BCT.blk h w m X) = 1 := by
  rw [FF, if_pos]
  exact ⟨1, one_mem _, by rw [mul_one, bblk_eq]; exact tri_blk_nU m X⟩

private theorem sum_left (h : a + b = n) (m : GLw a w × GLw b w) (f : GLw n w → ℂ)
    (hf : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w n, f (g * k) = f g) :
    ∑ᶠ c : GLw n w ⧸ GlobalTheory.LFun.KGL w n, f c.out * FF h m c.out =
      ∑ᶠ q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
        f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out)) := by
  let φ : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w → GLw n w ⧸ GlobalTheory.LFun.KGL w n :=
    fun q => ((GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out) : GLw n w) : GLw n w ⧸ GlobalTheory.LFun.KGL w n)
  let u : GLw n w ⧸ GlobalTheory.LFun.KGL w n → ℂ := fun c => f c.out * FF h m c.out
  have hinj : Function.Injective φ := by
    intro q q' e
    have e' := QuotientGroup.eq.1 e
    rw [bblk_eq, bblk_eq] at e'
    have : (GlobalTheory.ResW.blk h m * nU h (Multiplicative.toAdd q.out))⁻¹ * (GlobalTheory.ResW.blk h m * nU h (Multiplicative.toAdd q'.out)) =
        nU h (-(Multiplicative.toAdd q.out) + Multiplicative.toAdd q'.out) := by
      rw [nU_add, ← nU_neg]; group
    rw [this] at e'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.2 (mem_intMat.2 (nU_int e'))
  have hsup : Function.support u ⊆ Set.range φ := by
    intro c hc
    have h1 : FF h m c.out ≠ 0 := right_ne_zero_of_mul hc
    have h2 : ∃ k ∈ GlobalTheory.LFun.KGL w n, Tri h (c.out * k) m := by
      by_contra h3
      exact h1 (by rw [FF, if_neg h3])
    obtain ⟨k, hk, Y, hY⟩ := h2
    have e := tri_of_eq hY
    let X := (m.1⁻¹).val * Y
    let q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w :=
      ((Multiplicative.ofAdd X : Multiplicative _) : _ ⧸ intMat a b w)
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (intMat a b w) (Multiplicative.ofAdd X)
    refine ⟨q, ?_⟩
    have e2 : GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out) = c.out * k * nU h (Multiplicative.toAdd t.1) := by
      rw [bblk_eq, e, show q.out = Multiplicative.ofAdd X * t.1 from ht, mul_assoc, ← nU_add]
      rfl
    change ((GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out) : GLw n w) : GLw n w ⧸ GlobalTheory.LFun.KGL w n) = c
    rw [e2]
    conv_rhs => rw [← QuotientGroup.out_eq' c]
    refine QuotientGroup.eq.2 ?_
    have : (c.out * k * nU h (Multiplicative.toAdd t.1))⁻¹ * c.out = (k * nU h (Multiplicative.toAdd t.1))⁻¹ := by group
    rw [this]
    exact inv_mem (mul_mem hk (nU_mem (mem_intMat.1 t.2)))
  have hval : ∀ q, u (φ q) = f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out)) := by
    intro q
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.LFun.KGL w n) (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out))
    change f (Quotient.out (φ q)) * FF h m (Quotient.out (φ q)) = _
    have : Quotient.out (φ q) = GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out) * κ.1 := hκ
    rw [this, hf _ _ κ.2, FF_right h m _ _ κ.2, FF_bblk, mul_one]
  calc ∑ᶠ c, u c = ∑ᶠ c ∈ Set.range φ, u c := by
        rw [finsum_mem_def, Set.indicator_eq_self.2 hsup]
    _ = ∑ᶠ q, u (φ q) := finsum_mem_range hinj
    _ = _ := finsum_congr hval

private theorem FF_blk (h : a + b = n) (m : GLw a w × GLw b w) (x : GLw a w) (y : GLw b w) :
    FF h m (GlobalTheory.ResW.blk h (x, y)) =
      if (x : GLw a w ⧸ GlobalTheory.LFun.KGL w a) = (m.1 : GLw a w) ∧ (y : GLw b w ⧸ GlobalTheory.LFun.KGL w b) = (m.2 : GLw b w) then 1 else 0 := by
  have : (∃ k ∈ GlobalTheory.LFun.KGL w n, Tri h (GlobalTheory.ResW.blk h (x, y) * k) m) ↔
      (x : GLw a w ⧸ GlobalTheory.LFun.KGL w a) = (m.1 : GLw a w) ∧ (y : GLw b w ⧸ GlobalTheory.LFun.KGL w b) = (m.2 : GLw b w) := by
    rw [QuotientGroup.eq, QuotientGroup.eq]
    constructor
    · rintro ⟨k, hk, t⟩
      have t2 := (GlobalTheory.ResW.HeckeCT.tri_blk h ((x, y)⁻¹)).mul t
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at t2
      exact tri_int (O := Ov E w) t2 hk
    · rintro ⟨h1, h2⟩
      refine ⟨GlobalTheory.ResW.blk h (x⁻¹ * m.1, y⁻¹ * m.2), GlobalTheory.ResW.HeckeCT.blk_mem h h1 h2, ?_⟩
      rw [← map_mul]
      have : (x, y) * (x⁻¹ * m.1, y⁻¹ * m.2) = m := by ext1 <;> simp
      rw [this]
      exact GlobalTheory.ResW.HeckeCT.tri_blk h m
  simp only [FF, this]

private theorem out_inv {k : ℕ} (A : GLw k w → ℂ) (hA : ∀ g, ∀ c ∈ GlobalTheory.LFun.KGL w k, A (g * c) = A g) (x : GLw k w) :
    A (Quotient.out ((x : GLw k w ⧸ GlobalTheory.LFun.KGL w k))) = A x := by
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.LFun.KGL w k) x
  have : Quotient.out ((x : GLw k w ⧸ GlobalTheory.LFun.KGL w k)) = x * κ.1 := hκ
  rw [this, hA _ _ κ.2]

private theorem sum_right (h : a + b = n) (m : GLw a w × GLw b w) (A : GLw a w → ℂ) (B : GLw b w → ℂ)
    (hA : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w a, A (g * k) = A g) (hB : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w b, B (g * k) = B g) :
    ∑ᶠ c₁ : GLw a w ⧸ GlobalTheory.LFun.KGL w a, ∑ᶠ c₂ : GLw b w ⧸ GlobalTheory.LFun.KGL w b,
      A c₁.out * B c₂.out * FF h m (GlobalTheory.ResW.blk h (c₁.out, c₂.out)) = A m.1 * B m.2 := by
  rw [finsum_eq_single _ ((m.1 : GLw a w) : GLw a w ⧸ GlobalTheory.LFun.KGL w a),
    finsum_eq_single _ ((m.2 : GLw b w) : GLw b w ⧸ GlobalTheory.LFun.KGL w b)]
  · rw [FF_blk, if_pos ⟨QuotientGroup.out_eq' _, QuotientGroup.out_eq' _⟩, mul_one, out_inv A hA, out_inv B hB]
  · intro c hc
    rw [FF_blk, if_neg, mul_zero]
    rintro ⟨-, e⟩
    exact hc ((QuotientGroup.out_eq' c).symm.trans e)
  · intro c hc
    refine finsum_eq_zero_of_forall_eq_zero fun c₂ => ?_
    rw [FF_blk, if_neg, mul_zero]
    rintro ⟨e, -⟩
    exact hc ((QuotientGroup.out_eq' c).symm.trans e)

end Local

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}

private theorem unif_spec (w : Pl E) : IsUnifV E w (unif w) := by
  have : ∃ x, IsUnifV E w x := by
    refine ⟨((w.valuation_exists_uniformizer E).choose : w.adicCompletion E), ?_⟩
    rw [IsUnifV, w.valuedAdicCompletion_eq_valuation', (w.valuation_exists_uniformizer E).choose_spec]
    rfl
  exact Classical.epsilon_spec this

private theorem tj_right (k i : ℕ) (ϖ : w.adicCompletion E) (g : GLw k w) (c : GLw k w) (hc : c ∈ KGL w k) :
    Tj ℂ k (Ov E w) ϖ i (g * c) = Tj ℂ k (Ov E w) ϖ i g := by
  have : g * c ∈ satakeTset w ϖ i ↔ g ∈ satakeTset w ϖ i :=
    ⟨fun t => by simpa using satake_Tset_right w t (inv_mem (show c ∈ GLint (Fin k) (Ov E w) from hc)),
      fun t => satake_Tset_right w t hc⟩
  by_cases hg : g ∈ satakeTset w ϖ i
  · rw [satake_Tj_eq, satake_Tj_eq, Set.indicator_of_mem (this.2 hg), Set.indicator_of_mem hg]; rfl
  · rw [satake_Tj_eq, satake_Tj_eq, Set.indicator_of_notMem (fun t => hg (this.1 t)), Set.indicator_of_notMem hg]

private theorem tj_left (k i : ℕ) (ϖ : w.adicCompletion E) (g : GLw k w) (c : GLw k w) (hc : c ∈ KGL w k) :
    Tj ℂ k (Ov E w) ϖ i (c * g) = Tj ℂ k (Ov E w) ϖ i g := by
  have : c * g ∈ satakeTset w ϖ i ↔ g ∈ satakeTset w ϖ i :=
    ⟨fun t => by simpa using satake_Tset_left w t (inv_mem (show c ∈ GLint (Fin k) (Ov E w) from hc)),
      fun t => satake_Tset_left w t hc⟩
  by_cases hg : g ∈ satakeTset w ϖ i
  · rw [satake_Tj_eq, satake_Tj_eq, Set.indicator_of_mem (this.2 hg), Set.indicator_of_mem hg]; rfl
  · rw [satake_Tj_eq, satake_Tj_eq, Set.indicator_of_notMem (fun t => hg (this.1 t)), Set.indicator_of_notMem hg]

private theorem isHecke_Tj (k i : ℕ) (ϖ : w.adicCompletion E) : IsHecke (KGL w k) (Tj ℂ k (Ov E w) ϖ i) := by
  have hc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w k).2
  refine ⟨?_, fun c hc x => ⟨tj_left k i ϖ x c hc, tj_right k i ϖ x c hc⟩⟩
  rcases (satakeTset w ϖ i : Set (GLw k w)).eq_empty_or_nonempty with h0 | ⟨d, a', ha', b', hb', hd⟩
  · refine HasCompactSupport.of_support_subset_isCompact isCompact_empty fun y hy => ?_
    have := (satake_Tj_ne_zero_iff w ℂ ϖ i y).1 hy
    rw [h0] at this
    exact this
  · refine HasCompactSupport.of_support_subset_isCompact
      (IsCompact.mul (IsCompact.mul hc (isCompact_singleton (x := d))) hc) fun y hy => ?_
    obtain ⟨a, ha, b, hb, hy'⟩ := (satake_Tj_ne_zero_iff w ℂ ϖ i y).1 hy
    refine Set.mem_mul.2 ⟨a * a'⁻¹ * d, Set.mem_mul.2 ⟨a * a'⁻¹, mul_mem ha (inv_mem ha'), d, rfl, rfl⟩,
      b'⁻¹ * b, mul_mem (inv_mem hb') hb, ?_⟩
    apply Units.ext
    have h1 : (a'⁻¹).val * a'.val = 1 := Units.inv_mul a'
    have h2 : b'.val * (b'⁻¹).val = 1 := Units.mul_inv b'
    simp only [Units.val_mul]
    rw [hy', hd]
    calc a.val * (a'⁻¹).val * (a'.val * diagJ k ϖ i * b'.val) * ((b'⁻¹).val * b.val)
        = a.val * ((a'⁻¹).val * a'.val) * diagJ k ϖ i * (b'.val * (b'⁻¹).val) * b.val := by simp only [mul_assoc]
      _ = _ := by rw [h1, h2]; simp

private theorem ord_det {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {k p : ℕ} (hp : p ≤ k) {g : GLw k w}
    (hg : Tj ℂ k (Ov E w) ϖ p g ≠ 0) :
    Valued.v g.val.det = ((Multiplicative.ofAdd (-(p : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  obtain ⟨A, ha, B, hb, e⟩ := (satake_Tj_ne_zero_iff w ℂ ϖ p g).1 hg
  have hA : Valued.v A.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem ha
  have hB : Valued.v B.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hb
  rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hp, map_mul, map_mul, hA, hB, one_mul, mul_one, map_pow, hϖ,
    ← WithZero.coe_pow, ← ofAdd_nsmul]
  simp

private theorem qV_pos (w : Pl E) : 0 < qV E w := by
  refine Nat.pos_of_ne_zero fun h0 => w.ne_bot ?_
  exact Ideal.absNorm_eq_zero_iff.1 h0

private theorem absHalf_eq (x : w.adicCompletion E) (t : ℤ) (hx : ordL x = t) :
    absHalf w x = (qV E w : ℂ) ^ (-(t : ℂ) / 2) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have e : Real.sqrt ((qV E w : ℝ) ^ (-ordL x)) = (qV E w : ℝ) ^ ((-(t : ℝ) / 2 : ℝ)) := by
    rw [hx, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast
    ring
  rw [absHalf, e, Complex.ofReal_cpow hq.le]
  push_cast
  rfl

private theorem term_eq {a b p₁ p₂ : ℕ} (h1 : p₁ ≤ a) (h2 : p₂ ≤ b) (m : GLw a w × GLw b w)
    (hT₁ : Tj ℂ a (Ov E w) (unif w) p₁ m.1 ≠ 0) (hT₂ : Tj ℂ b (Ov E w) (unif w) p₂ m.2 ≠ 0) :
    absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * (qV E w : ℂ) ^ (p₁ * (b - p₂)) =
      (qV E w : ℂ) ^ ((((p₁ : ℂ) * ((b : ℂ) - (p₂ : ℕ)) + ((p₂ : ℕ) : ℂ) * ((a : ℂ) - (p₁ : ℕ))) / 2)) := by
  have s1 := ord_det (unif_spec w) h1 hT₁
  have s2 := ord_det (unif_spec w) h2 hT₂
  have n1 : m.1.val.det ≠ 0 := fun h0 => by simp [h0] at s1
  have n2 : m.2.val.det ≠ 0 := fun h0 => by simp [h0] at s2
  have ho : ordL (m.1.val.det ^ b / m.2.val.det ^ a) = (b : ℤ) * p₁ - a * p₂ := by
    refine GlobalTheory.GramParity.ordL_eq_of (div_ne_zero (pow_ne_zero _ n1) (pow_ne_zero _ n2)) ?_
    rw [map_div₀, map_pow, map_pow, s1, s2, ← WithZero.coe_pow, ← WithZero.coe_pow, ← WithZero.coe_div,
      ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_sub]
    congr 2
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hq : (qV E w : ℂ) ≠ 0 := by exact_mod_cast (qV_pos w).ne'
  rw [absHalf_eq _ _ ho, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub h2]
  push_cast
  ring

private theorem sum_conv (a b j : ℕ) (g : ℕ × ℕ → ℂ) :
    ∑ i ∈ (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j), g i =
      ∑ p : Fin (a + 1) × Fin (b + 1), if (p.1 : ℕ) + p.2 = j then g (p.1, p.2) else 0 := by
  rw [Finset.sum_filter, Finset.sum_product, Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_range]

end Main

theorem ctT : CtT := by
  intro E _ _ _ w n a b h j m
  have hH : IsHecke (KGL w n) (Tj ℂ n (Ov E w) (unif w) j) := isHecke_Tj _ _ _
  rw [(ctSph E w n a b h _ hH m).1, ← sum_left h m _ (fun g k hk => tj_right _ _ _ g k hk),
    GlobalTheory.ResW.HeckeCT.finsum_Tj_levi (unif_spec w) h (Nat.lt_succ_iff.1 j.2) (FF h m)
      (fun g k hk => FF_right h m g k hk) (fun g m' t => FF_tri h m g m' t)]
  have e := fun i : ℕ × ℕ => sum_right h m (Tj ℂ a (Ov E w) (unif w) i.1) (Tj ℂ b (Ov E w) (unif w) i.2)
    (fun g k hk => tj_right _ _ _ g k hk) (fun g k hk => tj_right _ _ _ g k hk)
  simp only [e]
  rw [sum_conv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : (p.1 : ℕ) + p.2 = j
  · rw [if_pos hp, cf, if_pos hp]
    by_cases h1 : Tj ℂ a (Ov E w) (unif w) p.1 m.1 = 0
    · simp [h1]
    by_cases h2 : Tj ℂ b (Ov E w) (unif w) p.2 m.2 = 0
    · simp [h2]
    rw [← mul_assoc, term_eq (Nat.lt_succ_iff.1 p.1.2) (Nat.lt_succ_iff.1 p.2.2) m h1 h2]
  · rw [if_neg hp, cf, if_neg hp]
    simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
