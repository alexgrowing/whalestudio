import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent

section Vertex
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def symLev (c : ℕ) : n ⊕ Fin c → ℕ := if Even c then midLev (c / 2) else lev (c / 2 + 1)

omit [Fintype n] [DecidableEq n] in
theorem midLev_lt_of_symLev_lt {r s : n ⊕ Fin c} (h : symLev c r < symLev c s) :
    midLev (c / 2) r < midLev (c / 2) s := by
  unfold symLev at h
  split_ifs at h
  · exact h
  · rcases r with r | r <;> rcases s with s | s <;> simp [lev, midLev] at h ⊢ <;> omega

theorem mem_symN (hc : 1 ≤ c) {g : GL (n ⊕ Fin c) k}
    (hg : ∀ r s, symLev c s ≤ symLev c r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) :
    g ∈ symN k n c := by
  unfold symLev at hg
  split_ifs at hg with h
  · obtain ⟨ρ, rfl⟩ := h
    have e1 : (ρ + ρ) / 2 = ρ := by omega
    have e2 : (ρ + ρ + 1) / 2 = ρ := by omega
    rw [e1] at hg
    rw [symN, e1, e2]
    exact ((fj_unipotent k n (ρ + ρ) ρ (by omega) (by omega)).2.1 g).2 hg
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure hg)

omit [Fintype n'] [DecidableEq n'] in

theorem mul_stepPt_apply {b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hb : b.BlockTriangular (midLev (c / 2)))
    (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n ⊕ Fin c) (j : Fin c)
    (h : symLev c r = symLev c (Sum.inr j : n ⊕ Fin c)) :
    (b * stepPt x₀ e) r (Sum.inr j.castSucc) = b r (Sum.inr j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr j)]
  · simp [stepPt, basePt, Free, Kept]
  · intro s _ hs
    by_cases hl : midLev (c / 2) s < midLev (c / 2) r
    · rw [hb hl, zero_mul]
    · unfold symLev at h
      rcases s with s | l
      · have : ¬ (c / 2 + 1 < j.val + 1 ∨ (Even c ∧ j.val = c / 2)) := by
          split_ifs at h with he <;> rcases r with r | r <;> simp [lev, midLev, he] at h hl ⊢ <;> omega
        have h0 : stepPt x₀ e (Sum.inl s) (Sum.inr j.castSucc) = 0 := by
          rw [stepPt, Matrix.add_apply, of_apply, dif_neg (by exact this)]; simp [basePt]
        rw [h0, mul_zero]
      · have h1 : ¬ l.val < j.val := by
          split_ifs at h with he <;> rcases r with r | r <;> simp [lev, midLev] at h hl ⊢ <;> omega
        have h2 : l.val ≠ j.val := fun e => hs (by rw [Fin.ext e])
        simp [stepPt, basePt, Free, Kept, h1, h2]
  · simp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [Fintype n'] in

theorem exists_symR_mul (hc : 1 ≤ c) (ψ : AddChar k Circle) {γ δ : ValueGroupWithZero k} (hγ : 1 ≤ γ)
    (hψ : ∀ a : k, (∀ t, valuation k t ≤ δ → ψ (a * t) = 1) → valuation k a ≤ γ)
    (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k)
    (h1 : Bd γ ((h⁻¹).val * stepPt x₀ e))
    (h2 : ∀ d : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, (∀ r s, ¬ Free (c / 2 + 1) (r, s) → d r s = 0) →
      (∀ r s, d r (Sum.inl s) = 0) → Bd δ ((h⁻¹).val * d) → ψ (ch d) = 1) :
    ∃ r ∈ symR k n c, ∃ w : GL (n ⊕ Fin c) k, Bd (γ * γ) w.val ∧ Bd (γ * γ) (w⁻¹).val ∧ h = r * w := by
  obtain ⟨b, hb', κ, hκ, rfl⟩ := iwasawa_blockTriangular k (n ⊕ Fin c) (midLev (c / 2)) h
  have hb : b.val.BlockTriangular (symLev c) := fun r s hrs => hb' (midLev_lt_of_symLev_lt hrs)
  have hκ1 : Bd 1 κ.val := bd_of_mem_KO hκ
  have hκ2 : Bd 1 (κ⁻¹).val := bd_of_mem_KO (inv_mem hκ)
  have hdiag : ∀ i : Fin c, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ γ := by
    intro i
    refine hψ _ fun t ht => ?_
    set E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := Matrix.single (Sum.inr i) (Sum.inr i.succ) t with hE
    have hEb : Bd δ E := by
      intro r s
      simp only [hE, Matrix.single, Matrix.of_apply]
      split_ifs
      · exact ht
      · simp
    have hd1 : ∀ r, (b.val * E) r (Sum.inr i.succ) = b.val r (Sum.inr i) * t := fun r => by
      rw [hE, Matrix.mul_single_apply_same]
    have hd2 : ∀ r s, s ≠ Sum.inr i.succ → (b.val * E) r s = 0 := fun r s hs => by
      rw [hE, Matrix.mul_single_apply_of_ne _ _ _ _ _ hs]
    have := h2 (b.val * E) ?_ (fun r s => hd2 _ _ (by simp)) ?_
    · have hc : ch (b.val * E) = b.val (Sum.inr i) (Sum.inr i) * t := by
        rw [ch, Finset.sum_eq_single i, hd1]
        · intro l _ hl; exact hd2 _ _ (by simpa using hl)
        · simp
      rwa [hc] at this
    · intro r s hf
      by_cases hs : s = Sum.inr i.succ
      · subst hs
        rw [hd1, hb' (i := r) (j := Sum.inr i), zero_mul]
        rcases r with r | r <;> simp [midLev, Free] at hf ⊢ <;> omega
      · exact hd2 r s hs
    · rw [← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
      simpa using hκ2.mul hEb
  have hbx : Bd γ ((b⁻¹).val * stepPt x₀ e) := by
    have := hκ1.mul h1
    rwa [one_mul, ← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  have m0 : ∀ i s, (levi (symLev c) b hb).val (Sum.inr i) (Sum.inl s) = 0 := by
    intro i s
    change (if _ then _ else _) = _
    split_ifs with hl
    · apply hb'
      unfold symLev at hl
      split_ifs at hl <;> simp [lev, midLev] at hl ⊢ <;> omega
    · rfl
  have m1 : ∀ i j, valuation k ((levi (symLev c) b hb).val (Sum.inr i) (Sum.inr j)) ≤ γ := by
    intro i j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · obtain rfl : i = j := Fin.ext (by
        unfold symLev at hl
        split_ifs at hl <;> simpa [lev, midLev] using hl)
      exact hdiag i
    · simp
  have m2 : ∀ r j, valuation k (((levi (symLev c) b hb)⁻¹).val r (Sum.inr j)) ≤ γ := by
    intro r j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · rw [← mul_stepPt_apply (inv_blockTriangular hb') x₀ e r j hl]
      exact hbx _ _
    · simp
  obtain ⟨x, w, hxw, hw1, hw2⟩ := exists_embX_mul (levi (symLev c) b hb) (γ := γ) m0 hγ m1 m2
  refine ⟨b * (levi (symLev c) b hb)⁻¹ * embX c x, mul_mem (Subgroup.mem_sup_right (mem_symN hc ?_))
      (Subgroup.mem_sup_left ⟨x, rfl⟩), w * κ, ?_, ?_, ?_⟩
  · intro r s hrs
    change (b.val * diagPart (symLev c) (b⁻¹).val) r s = _
    rw [mul_diagPart_apply hb (inv_blockTriangular hb) hrs, b.mul_inv]
  · simpa using hw1.mul hκ1
  · rw [_root_.mul_inv_rev, Units.val_mul]
    simpa using hκ2.mul hw2
  · rw [mul_assoc, ← mul_assoc (embX c x), ← hxw]
    group

end Vertex

section Shift
variable {k : Type} [Field k] {G : Grid k} (hs : 1 ≤ G.s)

abbrev Shifts (G : Grid k) : Type := ∀ j : Fin (G.m - 1),
  Matrix (Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1)) k

def IsAuxiliaryHeckeCharacter (d : Shifts G) : Prop :=
  ∀ j, (∀ r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → d j r s = 0) ∧ ∀ r s, d j r (Sum.inl s) = 0

def shiftVars (d : Shifts G) : Vars G := fun j rs => d j rs.1.1 rs.1.2

theorem stepPt_shift {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) (j : Fin (G.m - 1)) :
    stepPt (x j) ((shiftVars d + e) j) = stepPt (x j) (e j) + d j := by
  ext r s
  simp only [stepPt, Matrix.add_apply, of_apply]
  split_ifs with h
  · simp only [shiftVars, Pi.add_apply]; ring
  · rw [(hd j).1 r s fun h' => h (Or.inl h'), add_zero, add_zero]

theorem phase_shift {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) :
    phase x (shiftVars d + e) = phase x e + ∑ j, ch (d j) := by
  have h1 : ∀ j s, rowVar x (shiftVars d + e) j s = rowVar x e j s := fun j s => by
    unfold rowVar
    split_ifs with h
    · refine Finset.sum_congr rfl fun l _ => ?_
      have := stepPt_shift hd x e ⟨j, h⟩
      dsimp only at this
      rw [this, Matrix.add_apply, (hd ⟨j, h⟩).2, add_zero]
    · rfl
  have h2 : ∀ j r, colVar x (shiftVars d + e) j r = colVar x e j r := fun j r => by
    rw [colVar, colVar, stepPt_shift hd, Matrix.add_apply, (hd j).1 _ _ (by simp [Free]), add_zero]
  have h3 : ∀ j : Fin (G.m - 1), ch (stepPt (x j) ((shiftVars d + e) j)) = ch (stepPt (x j) (e j)) + ch (d j) :=
    fun j => by rw [stepPt_shift hd]; simp [ch, Finset.sum_add_distrib]
  simp only [phase, h1, h2, h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem moveArgs_theta (g : G.VertexGroup) (z : G.Args) (i j : ℕ) : G.moveArgs .one g z (.theta i j) =
    (((g (i, j + 1))⁻¹).val * (z (.theta i j))ᵀ * (g (i, j)).val)ᵀ := by
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, transpose_mul, transpose_transpose,
    Matrix.mul_assoc]

theorem moveArgs_sub (g : G.VertexGroup) (z z' : G.Args) :
    G.moveArgs .one g (z - z') = G.moveArgs .one g z - G.moveArgs .one g z' := by
  funext b
  simp only [Grid.moveArgs, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul]

theorem downMap_shift {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) (j : ℕ) :
    downMap hs x (shiftVars d + e) j - downMap hs x e j = if h : j < G.m - 1 then
      (d ⟨j, h⟩).reindex (frame (by have := topRank_add hs (j + 1); dsimp only; omega))
        (frame (by have := topRank_add hs j; dsimp only; omega)) else 0 := by
  unfold downMap
  split_ifs with h
  · have := stepPt_shift hd x e ⟨j, h⟩
    dsimp only at this
    rw [this]
    ext r s; simp
  · simp
  · simp

end Shift

section Frame
variable {k : Type} [Field k] {a c b : ℕ}

theorem frameGL_val (h : a + c = b) (g : GL (Fin b) k) : (frameGL h g).val = g.val.submatrix (frame h) (frame h) := rfl

theorem frameGL_symm_val (h : a + c = b) (g : GL (Fin a ⊕ Fin c) k) :
    ((frameGL h).symm g).val = g.val.submatrix (frame h).symm (frame h).symm := rfl

theorem comap_symR_congr {c' : ℕ} (hc : c = c') (h : a + c = b) (h' : a + c' = b) :
    (symR k (Fin a) c).comap (frameGL h).toMonoidHom = (symR k (Fin a) c').comap (frameGL h').toMonoidHom := by
  subst hc; rfl

theorem mul_reindex {ι : Type} {a' : ℕ} (h : a + c = b) (f : ι ≃ Fin a') (g : GL (Fin b) k)
    (D : Matrix (Fin a ⊕ Fin c) ι k) :
    g.val * D.reindex (frame h) f = ((frameGL h g).val * D).reindex (frame h) f := by
  rw [frameGL_val, reindex_apply, reindex_apply, ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _)]
  simp

variable [ValuativeRel k]

theorem bd_submatrix {ι κ ι' κ' : Type} {γ : ValueGroupWithZero k} {x : Matrix ι κ k} (hx : Bd γ x) (f : ι' → ι)
    (g : κ' → κ) : Bd γ (x.submatrix f g) := fun _ _ => hx _ _

theorem bd_reindex_iff {ι κ ι' κ' : Type} {γ : ValueGroupWithZero k} {x : Matrix ι κ k} (f : ι ≃ ι')
    (g : κ ≃ κ') : Bd γ (x.reindex f g) ↔ Bd γ x :=
  ⟨fun h r s => by simpa using h (f r) (g s), fun h _ _ => h _ _⟩

theorem transpose_mem_matLat [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι κ : Type} (u : kˣ) {x : Matrix κ ι k} (hx : Bd (valuation k (u : k)) x) :
    xᵀ ∈ matLat ι (u • stdLat k κ) := fun i => by
  rw [stdLat, smul_diagLat]
  exact fun j => by simpa using hx j i

end Frame

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem char_eq_one {S : G.Args → ℂ} {x : ColArgs G} {y : RowArgs G} (hne : flatTensor hs ψ ν S x y ≠ 0)
    {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (hS : ∀ e, S (fill hs x y (shiftVars d + e)) = S (fill hs x y e)) :
    ψ (∑ j, ch (d j)) = 1 := by
  classical
  haveI := secondCountable k
  haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance
  have key := integral_add_left_eq_self (μ := varsVol G ν) (flatIntegrand hs ψ S x y) (shiftVars d)
  simp only [flatIntegrand, hS, phase_shift hd, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← mul_assoc] at key
  rw [integral_mul_const] at key
  have h1 : (ψ (-∑ j, ch (d j)) : ℂ) = 1 := by
    apply mul_left_cancel₀ hne
    rw [mul_one]
    exact key
  have h2 : ψ (-∑ j, ch (d j)) = 1 := Circle.coe_eq_one.1 h1
  rwa [AddChar.map_neg_eq_inv, inv_eq_one] at h2

omit [MeasurableSpace k] [BorelSpace k] in

theorem tensor_shift {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (g : G.VertexGroup) (x : ColArgs G) (y : RowArgs G) (v : Vars G) {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d)
    (hb : ∀ (j : ℕ) (h : j < G.m - 1), Bd (valuation k ((ϖ ^ e : kˣ) : k)) (((g (G.m, j + 1))⁻¹).val *
      (d ⟨j, h⟩).reindex (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); dsimp only; omega))
        (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; dsimp only; omega)) * (g (G.m, j)).val)) :
    T (G.moveArgs .one g (fill hs x y (shiftVars d + v))) = T (G.moveArgs .one g (fill hs x y v)) := by
  rw [← hT.2.2 (G.moveArgs .one g (fill hs x y v))
    (G.moveArgs .one g (fill hs x y (shiftVars d + v) - fill hs x y v)), moveArgs_sub, add_sub_cancel]
  rintro (⟨i, l⟩ | ⟨i, l⟩)
  · rw [moveArgs_theta]
    refine transpose_mem_matLat _ ?_
    by_cases hi : i = G.m
    · subst hi
      rw [Pi.sub_apply, fill_theta, fill_theta, ← transpose_sub, transpose_transpose, downMap_shift hs hd]
      split_ifs with hl
      · exact hb l hl
      · simpa using bd_zero _
    · have : (fill hs x y (shiftVars d + v) - fill hs x y v) (.theta i l) = 0 := by simp [fill, hi]
      rw [this]
      simpa using bd_zero _
  · have : (fill hs x y (shiftVars d + v) - fill hs x y v) (.ex i l) = 0 := sub_self _
    simp only [Grid.moveArgs, this, Matrix.mul_zero, Matrix.zero_mul, zero_mem]

theorem exists_rowR_mul (hψ : ψ ≠ 1) {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (s : kˣ) : ∃ δ : ValueGroupWithZero k, ∀ (keep : Bool) (g : G.VertexGroup) (x : ColArgs G) (y : RowArgs G)
      (j : ℕ) (hj : j < G.m - 2), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      Bd (valuation k (s : k)) (g (G.m, j)).val → Bd (valuation k (s : k)) ((g (G.m, j))⁻¹).val →
      ∃ r ∈ rowR hs (j := j + 1) (by omega), ∃ w : GL (Fin (G.rank (G.m, j + 1))) k,
        Bd δ w.val ∧ Bd δ (w⁻¹).val ∧ g (G.m, j + 1) = r * w := by
  obtain ⟨γ₂, hγ₂⟩ := exists_bd_of_char ψ hψ (ϖ ^ e * s⁻¹)
  set γ : ValueGroupWithZero k := max 1 (max (valuation k (s : k)) γ₂) with hγ
  have g0 : 1 ≤ γ := le_max_left _ _
  have g1 : valuation k (s : k) ≤ γ := (le_max_left _ _).trans (le_max_right _ _)
  have g2 : γ₂ ≤ γ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨γ * γ, fun keep g x y j hj hne hb1 hb2 => ?_⟩
  have hj1 : j < G.m - 1 := by omega
  have hf1 : topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by have := topRank_add hs (j + 1); omega
  have hf2 : topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by have := topRank_add hs j; omega
  obtain ⟨v, hv⟩ : ∃ v : Vars G, T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp only [flatTensor, flatIntegrand, moved, Grid.pathAct, hcon, mul_zero, zero_mul, integral_zero]
  have hint : Bd 1 (((g (G.m, j + 1))⁻¹).val * downMap hs x v j * (g (G.m, j)).val) := by
    have h1 : G.moveArgs .one g (fill hs x y v) (.theta G.m j) ∈ matLat _ (stdLat k _) := by
      by_contra hc
      exact hv (hT.2.1 _ _ (by simp [oppositePath]; omega) hc)
    rw [moveArgs_theta, fill_theta, transpose_transpose, mem_matLat_stdLat] at h1
    exact fun r t => h1 t r
  have h1 : Bd γ (((frameGL hf1 (g (G.m, j + 1)))⁻¹).val * stepPt (c := G.m - 2 - j) (x j) (v ⟨j, hj1⟩)) := by
    have h2 := hint.mul hb2
    rw [one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, downMap, dif_pos hj1, mul_reindex hf1,
      bd_reindex_iff, map_inv] at h2
    exact h2.mono g1
  obtain ⟨r, hr, w, hw1, hw2, hrw⟩ := exists_symR_mul (δ := valuation k ((ϖ ^ e * s⁻¹ : kˣ) : k)) (by omega) ψ g0
    (fun a ha => (hγ₂ a ha).trans g2) _ _ _ h1 fun d hd1 hd2 hd3 => by
      have hd : IsAuxiliaryHeckeCharacter (Pi.single (⟨j, hj1⟩ : Fin (G.m - 1)) d : Shifts G) := fun i => by
        by_cases hi : i = ⟨j, hj1⟩
        · subst hi; rw [Pi.single_eq_same]; exact ⟨hd1, hd2⟩
        · rw [Pi.single_eq_of_ne hi]; exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
      have h3 := char_eq_one hs ψ ν hne hd fun v => ?_
      · rw [Finset.sum_eq_single (⟨j, hj1⟩ : Fin (G.m - 1)), Pi.single_eq_same] at h3
        · exact h3
        · intro i _ hi; rw [Pi.single_eq_of_ne hi]; simp [ch]
        · simp
      · have h5 := tensor_shift hs hT g x y v hd fun l hl => ?_
        · simp only [moved, Grid.pathAct, h5]
        · by_cases hl' : l = j
          · subst hl'
            rw [Pi.single_eq_same, mul_reindex hf1, map_inv]
            have h4 := ((bd_reindex_iff (frame hf1) (frame hf2)).2 hd3).mul hb1
            simpa [mul_assoc] using h4
          · rw [Pi.single_eq_of_ne (fun h => hl' (congrArg Fin.val h))]
            simpa using bd_zero _
  refine ⟨(frameGL hf1).symm r, ?_, (frameGL hf1).symm w, bd_submatrix hw1 _ _, ?_, ?_⟩
  · rw [rowR, toFrame, comap_symR_congr (c' := G.m - 2 - j) (by omega) _ hf1]
    simpa using hr
  · rw [← map_inv]; exact bd_submatrix hw2 _ _
  · rw [← map_mul, ← hrw, MulEquiv.symm_apply_apply]

end Step

theorem finite_image_mk {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (H U : Subgroup A)
    (hU : IsOpen (U : Set A)) {Ω : Set A} (hΩ : IsCompact Ω) : (DoubleCoset.mk H U '' Ω).Finite := by
  obtain ⟨t, -, ht, hc⟩ := hΩ.elim_finite_subcover_image (b := Ω) (c := fun a => (fun z => a⁻¹ * z) ⁻¹' (U : Set A))
    (fun a _ => hU.preimage (continuous_const.mul continuous_id))
    (fun a ha => Set.mem_biUnion ha (by simp))
  refine (ht.image (DoubleCoset.mk H U)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨a, ha, haz⟩ := Set.mem_iUnion₂.1 (hc hz)
  exact ⟨a, ha, (DoubleCoset.eq H U a z).2 ⟨1, one_mem _, a⁻¹ * z, haz, by simp⟩⟩

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bd {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (GL ι k)} (hS : S.Finite) :
    ∃ s : kˣ, ∀ g ∈ S, Bd (valuation k (s : k)) g.val ∧ Bd (valuation k (s : k)) (g⁻¹).val := by
  obtain ⟨γ, hγ⟩ := exists_bd_of_isCompact
    ((hS.image fun g => g.val).union (hS.image fun g => (g⁻¹).val)).isCompact
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (max 1 γ)
  have h0 : t ≠ 0 := by
    rintro rfl
    have : (1 : ValueGroupWithZero k) ≤ 0 := by simpa using (le_max_left 1 γ).trans ht.ge
    simp at this
  have h1 : γ ≤ valuation k t := ht ▸ le_max_right _ _
  exact ⟨Units.mk0 t h0, fun g hg => ⟨(hγ _ (Or.inl ⟨g, hg, rfl⟩)).mono h1, (hγ _ (Or.inr ⟨g, hg, rfl⟩)).mono h1⟩⟩

variable [MeasurableSpace k] [BorelSpace k] {G : Grid k} {hs : 1 ≤ G.s} {ψ : AddChar k Circle} (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem finite_unfSupport_of_ne_one (hψ : ψ ≠ 1) {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) {J : G.Level}
    (hJ : ∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k)))
    (keep : Bool) (ρ : Reps hs J) : (unfSupport ψ ν keep ρ T).Finite := by
  have step : ∀ i : Fin (G.m - 2), ((fun β => ρ.elt β (G.m, i)) '' unfSupport ψ ν keep ρ T).Finite →
      ((fun β => β i) '' unfSupport ψ ν keep ρ T).Finite := by
    intro i hi
    obtain ⟨s, hs'⟩ := exists_unit_bd hi
    obtain ⟨δ, hδ⟩ := exists_rowR_mul hs ψ ν hψ hT s
    refine (finite_image_mk (rowR hs (j := i + 1) (by omega)) _ (hJ (i + 1) (by omega) (by omega))
      (isCompact_bd δ)).subset ?_
    rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hβ
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hx
    obtain ⟨b1, b2⟩ := hs' _ ⟨β, hβ, rfl⟩
    obtain ⟨r, hr, w, w1, w2, hw⟩ := hδ keep (ρ.elt β) x y i i.2 hy b1 b2
    refine ⟨w, ⟨w1, w2⟩, ?_⟩
    rw [Reps.elt, onColumn_apply] at hw
    simp only [i.2, dif_pos] at hw
    refine Eq.trans ?_ (ρ.mk_rep i (β i))
    exact (DoubleCoset.eq _ _ _ _).2 ⟨r, hr, 1, one_mem _, by rw [mul_one]; exact hw⟩
  have col : ∀ j, j ≤ G.m - 2 → ((fun β => ρ.elt β (G.m, j)) '' unfSupport ψ ν keep ρ T).Finite := by
    intro j
    induction j with
    | zero =>
      refine fun _ => (Set.finite_singleton ρ.base).subset ?_
      rintro _ ⟨β, -, rfl⟩
      exact onColumn_apply _ 0
    | succ j ih =>
      intro hj
      refine ((step ⟨j, hj⟩ (ih (by omega))).image (ρ.rep ⟨j, hj⟩)).subset ?_
      rintro _ ⟨β, hβ, rfl⟩
      refine ⟨_, ⟨β, hβ, rfl⟩, ?_⟩
      simp only [Reps.elt, onColumn_apply, show j < G.m - 2 from hj, dif_pos]
  exact (Set.Finite.pi' fun i => step i (col i i.2.le)).subset fun β hβ i => ⟨β, hβ, rfl⟩

end Main

theorem finite_unfSupport {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (J : G.Level) :
    Even G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T →
      (∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k))) →
      ∀ (keep : Bool) (ρ : Reps hs J), (unfSupport ψ ν keep ρ T).Finite :=
  fun _ _ hψ hT hJ keep ρ => finite_unfSupport_of_ne_one ν hψ.ne_one hT hJ keep ρ

end GlobalTheory.FunObj.FiniteSupport
