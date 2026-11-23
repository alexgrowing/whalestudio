import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

namespace UpperTheory.V.Loc.SymplecticTangentProjection

open Polynomial TrivSqZeroExt

private def conjHom {B : Type} [CommRing B] (h h' : M4 B) (e : h' * h = 1) (e' : h * h' = 1) : M4 B →ₐ[B] M4 B where
  toFun M := h * M * h'
  map_one' := by rw [mul_one, e']
  map_mul' a b := by
    have : h * a * h' * (h * b * h') = h * a * (h' * h) * b * h' := by simp only [mul_assoc]
    rw [this, e, mul_one]
    simp only [mul_assoc]
  map_zero' := by simp
  map_add' a b := by rw [mul_add, add_mul]
  commutes' a := by rw [← Algebra.commutes, mul_assoc, e', mul_one]

private theorem prj_diag {B : Type} [CommRing B] (c : Fin 4 → B) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.single i i (∏ j ∈ Finset.univ.erase i, (c i - c j)) := by
  have hq : ∀ q : Polynomial B, Polynomial.aeval (Matrix.diagonal c : M4 B) q = Matrix.diagonal (fun k => q.eval (c k)) := by
    intro q
    have h1 : (Matrix.diagonal c : M4 B) = Matrix.diagonalAlgHom B c := rfl
    rw [h1, Polynomial.aeval_algHom_apply]
    show Matrix.diagonal (Polynomial.aeval c q) = _
    congr 1
    funext k
    have h2 := Polynomial.aeval_algHom_apply (Pi.evalAlgHom B (fun _ : Fin 4 => B) k) c q
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at h2
    rw [h2]
    rfl
  unfold prj
  rw [hq]
  ext a b
  rw [Matrix.diagonal_apply, Matrix.single_apply, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai
      simp
    · rw [if_pos rfl, if_neg (fun h => hai h.1.symm)]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hai, Finset.mem_univ _⟩) (sub_self _)
  · rw [if_neg hab, if_neg (fun h => hab (h.1.symm.trans h.2))]

private theorem prj_mul_eq_zero {B : Type} [CommRing B] {h h' : M4 B} (e : h' * h = 1) (e' : h * h' = 1)
    {c : Fin 4 → B} (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (M : M4 B) (i j : Fin 4) :
    prj c (h * Matrix.diagonal c * h') j * M * prj c (h * Matrix.diagonal c * h') i = 0 ↔ (h' * M * h) j i = 0 := by
  have hconj : ∀ k, prj c (h * Matrix.diagonal c * h') k = h * prj c (Matrix.diagonal c) k * h' := fun k =>
    Polynomial.aeval_algHom_apply (conjHom h h' e e') (Matrix.diagonal c) _
  have hu : ∀ k, IsUnit (∏ m ∈ Finset.univ.erase k, (c k - c m)) := fun k =>
    IsUnit.prod_iff.2 fun m hm => hc k m (Finset.ne_of_mem_erase hm).symm
  rw [hconj, hconj, prj_diag, prj_diag]
  obtain ⟨ua, hua⟩ := hu j
  obtain ⟨ub, hub⟩ := hu i
  rw [← hua, ← hub]
  have hre : h * Matrix.single j j (ua : B) * h' * M * (h * Matrix.single i i (ub : B) * h') =
      h * (Matrix.single j j (ua : B) * (h' * M * h) * Matrix.single i i (ub : B)) * h' := by
    simp only [mul_assoc]
  have hcancel : ∀ X : M4 B, h * X * h' = 0 ↔ X = 0 := by
    intro X
    constructor
    · intro hX
      rw [show X = (h' * h) * X * (h' * h) by rw [e, one_mul, mul_one]]
      rw [show h' * h * X * (h' * h) = h' * (h * X * h') * h by simp only [mul_assoc]]
      rw [hX, mul_zero, zero_mul]
    · intro hX
      rw [hX, mul_zero, zero_mul]
  have hent : ∀ (N : M4 B) p q, (Matrix.single j j (ua : B) * N * Matrix.single i i (ub : B)) p q =
      if p = j ∧ q = i then (ua : B) * N j i * ub else 0 := by
    intro N p q
    by_cases hp : p = j
    · by_cases hq : q = i
      · subst hp hq
        simp [Matrix.mul_apply, Matrix.single_apply]
      · simp [Matrix.mul_apply, Matrix.single_apply, hq, Ne.symm hq]
    · simp [Matrix.mul_apply, Matrix.single_apply, hp, Ne.symm hp]
  rw [hre, hcancel]
  constructor
  · intro hz
    have h1 := hent (h' * M * h) j i
    rw [hz, if_pos ⟨rfl, rfl⟩] at h1
    have h2 : (ua : B) * (h' * M * h) j i * ub = 0 := h1.symm
    simpa using h2
  · intro hz
    ext p q
    rw [hent]
    split_ifs
    · simp [hz]
    · rfl

variable {E : Type} [Field E]

private def dual (P N : M4 E) : M4 (DualNumber E) := Matrix.of fun a b => ⟨P a b, N a b⟩

@[simp] private theorem fst_dual (P N : M4 E) (a b : Fin 4) : (dual P N a b).fst = P a b := rfl

@[simp] private theorem snd_dual (P N : M4 E) (a b : Fin 4) : (dual P N a b).snd = N a b := rfl

private theorem dual_mul (P N P' N' : M4 E) : dual P N * dual P' N' = dual (P * P') (P * N' + N * P') := by
  ext a b
  · rw [Matrix.mul_apply, TrivSqZeroExt.fst_sum]
    simp [Matrix.mul_apply]
  · rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
    simp only [TrivSqZeroExt.snd_mul, fst_dual, snd_dual, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

private theorem dual_one : dual (1 : M4 E) 0 = 1 := by
  ext a b
  · by_cases h : a = b <;> simp [Matrix.one_apply, h]
  · by_cases h : a = b <;> simp [Matrix.one_apply, h]

private theorem adj_dual_eq_dual_adj (P N : M4 E) : adj (dual P N) = dual (adj P) (adj N) := by
  ext i j <;> simp [adj_apply]

private theorem adj_diagonal_eq_diagonal_rev (p : Fin 4 → E) : adj (Matrix.diagonal p) = Matrix.diagonal (fun a : Fin 4 => p a.rev) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.diagonal]

private theorem inl_smul_one_eq_dual_smul_one (ν : E) : (inl ν : DualNumber E) • (1 : M4 (DualNumber E)) = dual (ν • 1) 0 := by
  ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp

private theorem dual_eq_dual_iff (A B A' B' : M4 E) : dual A B = dual A' B' ↔ A = A' ∧ B = B' := by
  constructor
  · intro h
    constructor
    · ext i j
      simpa using congrArg fst (congrFun (congrFun h i) j)
    · ext i j
      simpa using congrArg snd (congrFun (congrFun h i) j)
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem diag_rev_mul_add_adj_mul_diag_apply (p : Fin 4 → E) (γ : M4 E) (i j : Fin 4) :
    (Matrix.diagonal (fun a : Fin 4 => p a.rev) * (γ * Matrix.diagonal p) +
        adj (γ * Matrix.diagonal p) * Matrix.diagonal p) i j =
      p i.rev * p j * (γ i j + adj γ i j) := by
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, adj_apply, zsmul_eq_mul]
  ring

private theorem gsp_iff (p : Fin 4 → E) (ν : E) (hp : ∀ a, p a ≠ 0) (hν : ∀ a, p a.rev * p a = ν) (γ : M4 E) :
    IsGSp (inl ν : DualNumber E) (dual (Matrix.diagonal p) (γ * Matrix.diagonal p)) ↔ γ ∈ sp4 E := by
  show adj _ * _ = _ ↔ adj γ = -γ
  rw [adj_dual_eq_dual_adj, dual_mul, inl_smul_one_eq_dual_smul_one, dual_eq_dual_iff, adj_diagonal_eq_diagonal_rev]
  have h1 : Matrix.diagonal (fun a : Fin 4 => p a.rev) * Matrix.diagonal p = ν • 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    exact hν a
  rw [and_iff_right h1]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [diag_rev_mul_add_adj_mul_diag_apply] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (mul_ne_zero (hp _) (hp _))
    · rw [Matrix.neg_apply]
      exact eq_neg_of_add_eq_zero_right h0
  · intro h
    ext i j
    rw [diag_rev_mul_add_adj_mul_diag_apply, h, Matrix.neg_apply, add_neg_cancel, mul_zero]
    rfl

private theorem conj_entry (p : Fin 4 → E) (γ Y : M4 E) (a b : Fin 4) :
    (dual 1 (-Y) * dual (Matrix.diagonal p) (γ * Matrix.diagonal p) * dual 1 Y) a b =
      inl (Matrix.diagonal p a b) + inr (γ a b * p b - Y a b * p b + p a * Y a b) := by
  rw [dual_mul, dual_mul]
  ext
  · simp
  · simp
    ring

private theorem ord_iff {H : Type} [Group H] (I : Subgroup H) (s₀ : H) (hs : s₀ ∈ I) (p : Fin 4 → H → E)
    (hp : ∀ a g, p a g ≠ 0) (hc : Function.Injective fun a => p a s₀) (γ : H → M4 E) (r : H →* M4 (DualNumber E))
    (hr : ∀ g, r g = dual (Matrix.diagonal fun a => p a g) (γ g * Matrix.diagonal fun a => p a g))
    (Y : M4 E) (hY : ∀ a b, a ≠ b → γ s₀ a b = (1 - p a s₀ / p b s₀) * Y a b) :
    Ord I (fun a g => (inl (p a g) : DualNumber E)) s₀ r ↔
      (∀ g a b, b < a → γ g a b = (1 - p a g / p b g) * Y a b) ∧ ∀ s ∈ I, ∀ a, γ s a a = 0 := by
  classical
  have e : dual 1 (-Y) * dual 1 Y = 1 := by
    rw [dual_mul, ← dual_one]
    congr 1 <;> simp
  have e' : dual 1 Y * dual 1 (-Y) = 1 := by
    rw [dual_mul, ← dual_one]
    congr 1 <;> simp
  have hconj : ∀ g a b, (dual 1 (-Y) * r g * dual 1 Y) a b =
      inl (Matrix.diagonal (fun a => p a g) a b) + inr (γ g a b * p b g - Y a b * p b g + p a g * Y a b) := by
    intro g a b
    rw [hr g]
    exact conj_entry (fun a => p a g) (γ g) Y a b
  have hpne : ∀ a b, a ≠ b → p a s₀ ≠ p b s₀ := fun a b hab h => hab (hc h)
  have hu : ∀ i j, i ≠ j → IsUnit ((fun a => (inl (p a s₀) : DualNumber E)) i - (fun a => (inl (p a s₀) : DualNumber E)) j) := by
    intro i j hij
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl]
    exact (sub_ne_zero.2 (hpne i j hij)).isUnit
  obtain ⟨c', hc'⟩ : ∃ c' : Fin 4 → DualNumber E, c' = fun a => inl (p a s₀) + inr (γ s₀ a a * p a s₀) := ⟨_, rfl⟩
  have hD : dual 1 (-Y) * r s₀ * dual 1 Y = Matrix.diagonal c' := by
    refine Matrix.ext fun a b => ?_
    rw [hconj]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hc']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        ring
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, hY a b hab]
      have hb : p b s₀ ≠ 0 := hp b s₀
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
          TrivSqZeroExt.snd_zero]
        field_simp
        ring
  have hrs' : r s₀ = dual 1 Y * Matrix.diagonal c' * dual 1 (-Y) := by
    rw [← hD]
    simp only [← mul_assoc, e', one_mul]
    rw [mul_assoc, e', mul_one]
  have hrs : ∀ (_ : ∀ a, γ s₀ a a = 0),
      r s₀ = dual 1 Y * Matrix.diagonal (fun a => (inl (p a s₀) : DualNumber E)) * dual 1 (-Y) := by
    intro hd
    have hcc : c' = fun a => (inl (p a s₀) : DualNumber E) := by
      rw [hc']
      funext b
      simp [hd b]
    rw [hrs', hcc]
  have hst : ∀ (_ : ∀ a, γ s₀ a a = 0) g (i j : Fin 4), i ≠ j →
      (prj (fun a => (inl (p a s₀) : DualNumber E)) (r s₀) j * r g *
          prj (fun a => (inl (p a s₀) : DualNumber E)) (r s₀) i = 0 ↔
        γ g j i = (1 - p j g / p i g) * Y j i) := by
    intro hd g i j hij
    rw [hrs hd, prj_mul_eq_zero e e' hu, hconj, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
    have hi : p i g ≠ 0 := hp i g
    rw [TrivSqZeroExt.ext_iff]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, add_zero,
      zero_add, true_and]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      rw [h]
      field_simp
      ring
  have hin : ∀ (_ : ∀ a, γ s₀ a a = 0) s (i : Fin 4),
      (prj (fun a => (inl (p a s₀) : DualNumber E)) (r s₀) i * (r s - (inl (p i s) : DualNumber E) • 1) *
          prj (fun a => (inl (p a s₀) : DualNumber E)) (r s₀) i = 0 ↔ γ s i i = 0) := by
    intro hd s i
    rw [hrs hd, prj_mul_eq_zero e e' hu]
    rw [mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, e, Matrix.sub_apply, hconj,
      Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    have hi : p i s ≠ 0 := hp i s
    have hsimp : γ s i i * p i s - Y i i * p i s + p i s * Y i i = γ s i i * p i s := by ring
    rw [hsimp, TrivSqZeroExt.ext_iff]
    simp [hi]
  have main : ∀ (_ : ∀ a, γ s₀ a a = 0), Ord I (fun a g => (inl (p a g) : DualNumber E)) s₀ r ↔
      (∀ g a b, b < a → γ g a b = (1 - p a g / p b g) * Y a b) ∧ ∀ s ∈ I, ∀ a, γ s a a = 0 := by
    intro hd
    constructor
    · intro hO
      exact ⟨fun g a b hba => (hst hd g b a (ne_of_lt hba)).1 (hO.stable g b a hba),
        fun s hsI a => (hin hd s a).1 (hO.inert s hsI a)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun g i j hij => (hst hd g i j (ne_of_lt hij)).2 (h1 g j i hij),
        fun s hsI i => (hin hd s i).2 (h2 s hsI i)⟩
      rw [hrs hd, Matrix.charpoly_mul_comm, ← mul_assoc, e, one_mul, Matrix.charpoly_diagonal]
  constructor
  · intro hO
    have hd : ∀ a, γ s₀ a a = 0 := by
      intro a
      have hcp := hO.charpoly
      rw [hrs', Matrix.charpoly_mul_comm, ← mul_assoc, e, one_mul, Matrix.charpoly_diagonal] at hcp
      have hev := congrArg (Polynomial.eval (c' a)) hcp
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
      have hz : ∏ i, (c' a - c' i) = 0 := Finset.prod_eq_zero (Finset.mem_univ a) (sub_self _)
      rw [hz, ← Finset.mul_prod_erase Finset.univ (fun j => c' a - inl (p j s₀)) (Finset.mem_univ a)] at hev
      beta_reduce at hev
      have hunit : IsUnit (∏ j ∈ Finset.univ.erase a, (c' a - (inl (p j s₀) : DualNumber E))) := by
        rw [IsUnit.prod_iff]
        intro j hj
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hc']
        simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
          add_zero]
        exact (sub_ne_zero.2 (hpne a j (Finset.ne_of_mem_erase hj).symm)).isUnit
      have h0 := (hunit.mul_left_eq_zero).1 hev.symm
      rw [hc'] at h0
      simpa [hp a s₀] using congrArg TrivSqZeroExt.snd h0
    exact (main hd).1 hO
  · intro hR
    exact (main (fun a => hR.2 s₀ hs a)).2 hR

private theorem main {H : Type} [Group H] (I : Subgroup H) (s₀ : H) (hs : s₀ ∈ I) (p : Fin 4 → H → E) (ν : H → E)
    (hp : ∀ a g, p a g ≠ 0) (hν : ∀ a g, p a.rev g * p a g = ν g) (hc : Function.Injective fun a => p a s₀)
    (γ : H → M4 E) (r : H →* M4 (DualNumber E))
    (hr : ∀ g, r g = dual (Matrix.diagonal fun a => p a g) (γ g * Matrix.diagonal fun a => p a g)) :
    ((∀ g, IsGSp (inl (ν g) : DualNumber E) (r g)) ∧ Ord I (fun a g => (inl (p a g) : DualNumber E)) s₀ r) ↔
      (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, b < a → γ g a b = (1 - p a g / p b g) * X a b) ∧
        ∀ s ∈ I, ∀ a, γ s a a = 0 := by
  have hrat : ∀ g a b, p b.rev g / p a.rev g = p a g / p b g := by
    intro g a b
    rw [div_eq_div_iff (hp _ _) (hp _ _), hν b g, mul_comm (p a g), hν a g]
  have hne : ∀ a b, a ≠ b → (1 - p a s₀ / p b s₀) ≠ 0 := by
    intro a b hab h
    apply hab
    apply hc
    exact (div_eq_one_iff_eq (hp b s₀)).1 (sub_eq_zero.1 h).symm
  have hsp : ∀ M : M4 E, M ∈ sp4 E ↔ ∀ i j, (sgn i * sgn j) • M j.rev i.rev = -M i j := by
    intro M
    show adj M = -M ↔ _
    constructor
    · intro h i j
      rw [← adj_apply, h, Matrix.neg_apply]
    · intro h
      ext i j
      rw [adj_apply, h, Matrix.neg_apply]
  have hG : (∀ g, IsGSp (inl (ν g) : DualNumber E) (r g)) ↔ ∀ g, γ g ∈ sp4 E := by
    refine forall_congr' fun g => ?_
    rw [hr g]
    exact gsp_iff (fun a => p a g) (ν g) (fun a => hp a g) (fun a => hν a g) (γ g)
  rw [hG]
  constructor
  · rintro ⟨hsp4, hO⟩
    set Y : M4 E := Matrix.of fun a b => if a = b then 0 else γ s₀ a b / (1 - p a s₀ / p b s₀) with hYdef
    have hY : ∀ a b, a ≠ b → γ s₀ a b = (1 - p a s₀ / p b s₀) * Y a b := by
      intro a b hab
      simp only [hYdef, Matrix.of_apply, if_neg hab]
      rw [mul_div_assoc', eq_div_iff (hne a b hab), mul_comm]
    have hY' := (ord_iff I s₀ hs p hp hc γ r hr Y hY).1 hO
    refine ⟨hsp4, ⟨Y, ?_, hY'.1⟩, hY'.2⟩
    rw [hsp]
    intro i j
    have hγ := (hsp (γ s₀)).1 (hsp4 s₀) i j
    simp only [hYdef, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : j.rev ≠ i.rev := fun h => hij (Fin.rev_injective h).symm
      rw [if_neg hij', if_neg hij, hrat s₀ i j, ← neg_div, ← hγ, smul_div_assoc]
  · rintro ⟨hsp4, ⟨X, hX, hlow⟩, hin⟩
    set Y : M4 E := Matrix.of fun a b => if b < a then X a b else γ s₀ a b / (1 - p a s₀ / p b s₀) with hYdef
    have hY : ∀ a b, a ≠ b → γ s₀ a b = (1 - p a s₀ / p b s₀) * Y a b := by
      intro a b hab
      simp only [hYdef, Matrix.of_apply]
      split_ifs with hba
      · exact hlow s₀ a b hba
      · rw [mul_div_assoc', eq_div_iff (hne a b hab), mul_comm]
    refine ⟨hsp4, (ord_iff I s₀ hs p hp hc γ r hr Y hY).2 ⟨?_, hin⟩⟩
    intro g a b hba
    simp only [hYdef, Matrix.of_apply, if_pos hba]
    exact hlow g a b hba

end UpperTheory.V.Loc.SymplecticTangentProjection

open UpperTheory.V.Loc.SymplecticTangentProjection in
theorem UpperTheory.V.Loc.spTanL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (γ : D.Gp l → M4 E) (r' : D.Gp l →* M4 (DualNumber E)), IsFirstOrderDeformationOfRZero D l γ r' → (∀ a b, QCont l fun g => γ g a b) → (EqL D r' ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ (g : D.Gp l) a b, b < a → γ g a b = (1 - algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O)) * X a b) ∧ ∀ s : D.Gp l, (s : G ℚ Ω) ∈ D.Ip l → ∀ a, γ s a a = 0) := by
  intro Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ γ r' hdual hcont
  unfold EqL
  have hinjZ : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have hm := hD.decompSigma_mem
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hm
  have hξ : D.ξ D.s0 = 1 := hD.xi_unrT l (by simp [Raw.T]) hm.1.1
  have key : ∀ a, algebraMap c.O E ((D.ps a (D.s0 : G ℚ Ω) : c.Oˣ) : c.O) =
      ((Units.map (algebraMap ℤ_[l] E : ℤ_[l] →* E) (cycZ ℚ Ω l D.s0) ^ D.wts4 a : Eˣ) : E) := by
    intro a
    fin_cases a <;> simp [Raw.ps, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi, chiO, hm.1.2, hm.2, hξ, Raw.wts4,
      ← IsScalarTower.algebraMap_apply, pow_succ] <;> ring
  have hW : ¬IsOfFinOrder (Units.map (algebraMap ℤ_[l] E : ℤ_[l] →* E) (cycZ ℚ Ω l D.s0)) := by
    rw [(Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinjZ).isOfFinOrder_iff]
    exact hD.decompSigma_ord
  have hwts : Function.Injective D.wts4 := by
    intro a b h
    have := hD.two_le
    fin_cases a <;> fin_cases b <;> simp [Raw.wts4] at h ⊢ <;> omega
  have hd : ∀ g : D.Gp l, (D.r0At l g).map (algebraMap c.O E) =
      Matrix.diagonal (fun a => algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O)) := by
    intro g
    rw [show D.r0At l g = Matrix.diagonal fun a => ((D.ps a g : c.Oˣ) : c.O) from rfl,
      Matrix.diagonal_map (map_zero _)]
  have hr : ∀ g, r' g = dual (Matrix.diagonal fun a => algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O))
      (γ g * Matrix.diagonal fun a => algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O)) := by
    intro g
    refine Matrix.ext fun a b => ?_
    have h1 : algebraMap c.O E (D.r0At l g a b) =
        Matrix.diagonal (fun a => algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O)) a b := by
      rw [← hd g]
      rfl
    rw [hdual g a b, hd g, h1]
    rfl
  have hp : ∀ a (g : D.Gp l), algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O) ≠ 0 := fun a g =>
    (map_ne_zero_iff _ (IsFractionRing.injective c.O E)).2 (Units.ne_zero _)
  have hν : ∀ a (g : D.Gp l), algebraMap c.O E ((D.ps a.rev g : c.Oˣ) : c.O) *
      algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O) = algebraMap c.O E ((D.th g : c.Oˣ) : c.O) := by
    intro a g
    rw [← map_mul, ← Units.val_mul]
    congr 2
    fin_cases a <;> simp [Raw.ps, Raw.th, Fin.rev, mul_comm]
  have hc : Function.Injective fun a => algebraMap c.O E ((D.ps a (D.s0 : G ℚ Ω) : c.Oˣ) : c.O) := by
    intro a b h
    simp only [key] at h
    exact hwts ((injective_pow_iff_not_isOfFinOrder.2 hW) (Units.ext h))
  have hI : D.s0 ∈ (D.Ip l).subgroupOf (D.Gp l) := Subgroup.mem_subgroupOf.2 hm.1.1
  have hmain := main ((D.Ip l).subgroupOf (D.Gp l)) D.s0 hI
    (fun a g => algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O)) (fun g => algebraMap c.O E ((D.th g : c.Oˣ) : c.O))
    hp hν hc γ r' hr
  have hdiv : ∀ (g : D.Gp l) a b, algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O) =
      algebraMap c.O E ((D.ps a g : c.Oˣ) : c.O) / algebraMap c.O E ((D.ps b g : c.Oˣ) : c.O) := by
    intro g a b
    rw [Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]
  simp only [hdiv, Subgroup.mem_subgroupOf] at hmain ⊢
  exact hmain
