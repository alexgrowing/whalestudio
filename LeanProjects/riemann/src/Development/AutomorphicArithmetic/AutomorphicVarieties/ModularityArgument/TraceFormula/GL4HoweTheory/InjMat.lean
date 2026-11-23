import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open ValuativeRel Matrix

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ} {r s t : ValueGroupWithZero E} {A B M N : Matrix (Fin n) (Fin n) E}

def Bd (s : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, valuation E (M i j) ≤ s

private theorem Bd.mul (h : Bd s M) (h' : Bd t N) : Bd (s * t) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (h i l) (h' l j)

private theorem Bd.add (h : Bd s M) (h' : Bd s N) : Bd s (M + N) := fun i j => Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.sub (h : Bd s M) (h' : Bd s N) : Bd s (M - N) := fun i j => Valuation.map_sub_le _ (h i j) (h' i j)

private theorem Bd.mono (h : Bd s M) (e : s ≤ t) : Bd t M := fun i j => (h i j).trans e

private theorem Bd.smul (h : Bd s M) (x : E) : Bd (valuation E x * s) (x • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul' le_rfl (h i j)

private theorem bd_one : Bd 1 (1 : Matrix (Fin n) (Fin n) E) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

private theorem solve (hr : r < 1) (hA : Bd r (A - 1)) (e : A * M = B) (hB : Bd s B) : Bd s M := by
  intro i j
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => valuation E (M p.1 p.2))
    ⟨(i, j), Finset.mem_univ _⟩
  have hM : Bd (valuation E (M p.1 p.2)) M := fun a b => hp (a, b) (Finset.mem_univ _)
  have e2 : M = B - (A - 1) * M := by rw [← e, sub_mul, one_mul, sub_sub_cancel]
  refine (hM i j).trans (not_lt.1 fun hlt => ?_)
  have h0 : 0 < valuation E (M p.1 p.2) := lt_of_le_of_lt zero_le hlt
  have h1 := congrArg (valuation E) (congrFun (congrFun e2 p.1) p.2)
  rw [Matrix.sub_apply] at h1
  refine (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ((hB _ _).trans_lt hlt) ?_)).ne' h1
  exact ((hA.mul hM) _ _).trans_lt (mul_lt_of_lt_one_left h0 hr)

private theorem near (hr : r < 1) (hA : Bd r (A - 1)) (e : A * M = B) (hB : Bd r (B - 1)) : Bd r (M - 1) := by
  have h1 : Bd 1 M := solve hr hA e (by simpa using (hB.mono hr.le).add bd_one)
  have e2 : M - 1 = (B - 1) - (A - 1) * M := by rw [← e, sub_mul, one_mul]; abel
  rw [e2]
  exact hB.sub (by simpa using hA.mul h1)

private theorem unit_of (hr : r < 1) (hA : Bd r (A - 1)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨x, hx, h⟩
  have h1 : Bd 0 (Matrix.of fun i (_ : Fin n) => x i) := solve hr hA (B := 0) (by
    ext i j
    exact congrFun h i) fun i j => by simp
  exact hx (funext fun i => by simpa using h1 i i)

variable (E n) in

private def Js : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => if (i : ℕ) = j + 1 then 1 else 0

private theorem Js_bd : Bd 1 (Js E n) := fun i j => by
  rw [Js, Matrix.of_apply]; split_ifs <;> simp

private theorem Js_pow (k : ℕ) (i j : Fin n) : (Js E n ^ k) i j = if (i : ℕ) = j + k then 1 else 0 := by
  induction k generalizing i with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    have hJ : ∀ a b : Fin n, Js E n a b = if (a : ℕ) = b + 1 then 1 else 0 := fun _ _ => rfl
    simp only [ih, hJ]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j + k, by omega⟩]
      · simp; omega
      · intro b _ hb
        rw [if_neg (c := (b : ℕ) = j + k) fun e => hb (Fin.ext e), mul_zero]
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs <;> first | omega | simp

private theorem pow_near (hr : r ≤ 1) {Y : Matrix (Fin n) (Fin n) E} (hY : Bd r Y) (k : ℕ) :
    Bd 1 (Js E n ^ k) ∧ Bd r ((Js E n + Y) ^ k - Js E n ^ k) := by
  induction k with
  | zero => exact ⟨by simpa using bd_one, fun i j => by simp⟩
  | succ k ih =>
    refine ⟨by simpa [pow_succ] using ih.1.mul Js_bd, ?_⟩
    have e : (Js E n + Y) ^ (k + 1) - Js E n ^ (k + 1) =
        ((Js E n + Y) ^ k - Js E n ^ k) * (Js E n + Y) + Js E n ^ k * Y := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    exact Bd.add (by simpa using ih.2.mul (Js_bd.add (hY.mono hr))) (by simpa using ih.1.mul hY)

private theorem cyclic (hr : r < 1) {Y Z u : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (hY : Bd r Y) (hZ : Bd r Z)
    (hu : ∀ j, u (Fin.last n) j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (Fin.last n) j)
    (e : (Js E _ + Y) * u = u * (Js E _ + Z)) : Bd r (u - 1) := by
  have ek : ∀ k : ℕ, (Js E _ + Y) ^ k * u = u * (Js E _ + Z) ^ k := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, e, mul_assoc, ← pow_succ']
  have hn : ∀ {W : Matrix (Fin (n + 1)) (Fin (n + 1)) E}, Bd r W →
      Bd r ((Matrix.of fun (i j : Fin (n + 1)) => ((Js E (n + 1) + W) ^ (n - (i : ℕ)) : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (Fin.last n) j) - 1) :=
    fun {W} hW i j => by
      have h1 := (pow_near hr.le hW (n - (i : ℕ))).2 (Fin.last n) j
      rw [Matrix.sub_apply, Js_pow] at h1
      rw [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
      convert h1 using 4
      rw [Fin.ext_iff, Fin.val_last]
      have := i.2; have := j.2
      omega
  refine near hr (hn hY) ?_ (hn hZ)
  ext i j
  have h1 := congrFun (congrFun (ek (n - (i : ℕ))) (Fin.last n)) j
  rw [Matrix.mul_apply, Matrix.mul_apply] at h1
  simp only [hu] at h1
  rw [← Matrix.mul_apply (M := 1), one_mul] at h1
  exact h1

section Local

variable [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem sep {V : Type} [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V] (S : Set V) (hS : S.Finite)
    (ht : Submodule.span E S = ⊤) (D : V) (hD : D ∉ Submodule.span 𝒪[E] S) :
    ∃ φ : V →ₗ[E] E, (∀ x ∈ S, valuation E (φ x) ≤ 1) ∧ 1 < valuation E (φ D) := by
  haveI : (Submodule.span 𝒪[E] S).IsLattice E := ⟨Submodule.fg_span hS, by rw [Submodule.span_span_of_tower, ht]⟩
  haveI : Module.Free 𝒪[E] (Submodule.span 𝒪[E] S) := inferInstance
  haveI : Module.Finite 𝒪[E] (Submodule.span 𝒪[E] S) := inferInstance
  let b := Module.Free.chooseBasis 𝒪[E] (Submodule.span 𝒪[E] S)
  let c := b.extendOfIsLattice E
  have hc : ∀ i, c i = b i := fun i => by simp [c]
  by_contra h
  push Not at h
  apply hD
  have h1 : ∀ i, valuation E (c.repr D i) ≤ 1 := fun i => h (c.coord i) fun x hx => by
    have e : x = ∑ j, ((b.repr ⟨x, Submodule.subset_span hx⟩ j : 𝒪[E]) : E) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, Submodule.subset_span hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc]
      exact (algebraMap_smul E _ _).symm
    rw [e, Module.Basis.coord_apply, c.repr_sum_self]
    exact (b.repr ⟨x, Submodule.subset_span hx⟩ i).2
  rw [← c.sum_repr D]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : c.repr D i • c i = (⟨c.repr D i, h1 i⟩ : 𝒪[E]) • (b i : V) := by
    rw [hc]
    exact algebraMap_smul E (⟨c.repr D i, h1 i⟩ : 𝒪[E]) _
  rw [e]
  exact Submodule.smul_mem _ _ (b i).2

private theorem dual (u w D : Matrix (Fin n) (Fin n) E) (h : ¬ ∃ Y Z, Bd 1 Y ∧ Bd 1 Z ∧ D = Z + w * Y * u) :
    ∃ X, Bd 1 X ∧ Bd 1 (u * X * w) ∧ 1 < valuation E (D * X).trace := by
  let S₁ : Set (Matrix (Fin n) (Fin n) E) := Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 1
  let S₂ : Set (Matrix (Fin n) (Fin n) E) := Set.range fun p : Fin n × Fin n => w * Matrix.single p.1 p.2 1 * u
  have hb : ∀ i j : Fin n, Bd 1 (Matrix.single i j (1 : E)) := fun i j a b => by
    rw [Matrix.single_apply]; split_ifs <;> simp
  have hz : Bd 1 (0 : Matrix (Fin n) (Fin n) E) := fun _ _ => by simp
  obtain ⟨φ, h1, h2⟩ := sep (E := E) (S₁ ∪ S₂) ((Set.finite_range _).union (Set.finite_range _)) (by
    refine eq_top_iff.2 fun M _ => ?_
    rw [Matrix.matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : E) by simp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨(i, j), rfl⟩))) D fun hD => h (by
      clear h
      induction hD using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨p, rfl⟩ | ⟨p, rfl⟩
        · exact ⟨0, _, hz, hb p.1 p.2, by simp⟩
        · exact ⟨_, 0, hb p.1 p.2, hz, by simp⟩
      | zero => exact ⟨0, 0, hz, hz, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨Y, Z, a1, a2, rfl⟩ := hx
        obtain ⟨Y', Z', b1, b2, rfl⟩ := hy
        exact ⟨Y + Y', Z + Z', a1.add b1, a2.add b2, by noncomm_ring⟩
      | smul a x _ hx =>
        obtain ⟨Y, Z, a1, a2, rfl⟩ := hx
        have ha : valuation E (a : E) * 1 ≤ 1 := by rw [mul_one]; exact a.2
        refine ⟨(a : E) • Y, (a : E) • Z, (a1.smul _).mono ha, (a2.smul _).mono ha, ?_⟩
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
        rfl)
  let X : Matrix (Fin n) (Fin n) E := Matrix.of fun j i => φ (Matrix.single i j 1)
  have hX : ∀ M : Matrix (Fin n) (Fin n) E, (M * X).trace = φ M := fun M => by
    conv_rhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply, X, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : E) by simp, map_smul, smul_eq_mul]
  refine ⟨X, fun j i => h1 _ (Or.inl ⟨(i, j), rfl⟩), fun j i => ?_, by rwa [hX]⟩
  have e : (u * X * w) j i = φ (w * Matrix.single i j 1 * u) := by
    rw [← hX, mul_assoc (w * _), mul_assoc w, Matrix.trace_mul_comm w, mul_assoc (Matrix.single i j 1), Matrix.trace_single_mul, one_smul]
  rw [e]
  exact h1 _ (Or.inr ⟨(i, j), rfl⟩)

private theorem sd_eq (g : GL (Fin n) E) : GlobalTheory.Whittaker.superDiag g = (Js E n * (g : Matrix (Fin n) (Fin n) E)).trace := by
  have hJ : ∀ a b : Fin n, Js E n a b = if (a : ℕ) = b + 1 then 1 else 0 := fun _ _ => rfl
  simp only [GlobalTheory.Whittaker.superDiag, Matrix.trace, Matrix.diag, Matrix.mul_apply, hJ, Finset.sum_filter, ite_mul, one_mul, zero_mul]
  exact Finset.sum_comm

theorem not_intertwine (p : Eˣ) (hp : valuation E (p : E) < 1) (ψ : AddChar E Circle)
    (hψ : ∀ x : E, valuation E ((p : E) * p) < valuation E x → ∃ y, valuation E y ≤ valuation E x ∧ ψ y ≠ 1)
    (u : GL (Fin n) E) (hu : u ∈ GlobalTheory.SmGL.unipB E (Fin n)) (h : ¬ Bd (valuation E (p : E)) ((u : Matrix (Fin n) (Fin n) E) - 1)) :
    ∃ k : GL (Fin n) E, Bd (valuation E (p : E)) ((k : Matrix (Fin n) (Fin n) E) - 1) ∧
      Bd (valuation E (p : E)) (((u * k * u⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) ∧
      ψ (GlobalTheory.Whittaker.superDiag (u * k * u⁻¹)) ≠ ψ (GlobalTheory.Whittaker.superDiag k) := by
  rcases n with _ | n
  · exact absurd (fun i => i.elim0) h
  obtain ⟨U, hU⟩ : ∃ U, U = (u : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = ((u⁻¹ : GL (Fin (n + 1)) E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := ⟨_, rfl⟩
  have hUW : U * W = 1 := by rw [hU, hW, Units.mul_inv]
  have hp0 : (p : E) ≠ 0 := p.ne_zero
  obtain ⟨X, h1, h2, h3⟩ := dual U W ((p : E)⁻¹ • (W * Js E _ * U - Js E _)) (by
    rintro ⟨Y, Z, a1, a2, e⟩
    refine h (cyclic (Y := (-(p : E)) • Y) (Z := (p : E) • Z) hp (by simpa using a1.smul (-(p : E))) (by simpa using a2.smul (p : E))
      (fun j => ?_) ?_)
    · rcases (Fin.le_last j).lt_or_eq with hj | rfl
      · rw [((GlobalTheory.SmGL.mem_unipB _).1 hu).1 _ _ hj, Matrix.one_apply_ne hj.ne']
      · rw [((GlobalTheory.SmGL.mem_unipB _).1 hu).2, Matrix.one_apply_eq]
    · have e2 := congrArg (fun M => U * ((p : E) • M)) e
      simp only [smul_smul, mul_inv_cancel₀ hp0, one_smul, smul_add, mul_sub, mul_add, ← mul_assoc, hUW, one_mul,
        Matrix.mul_smul] at e2
      rw [← hU, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, neg_smul, sub_eq_iff_eq_add.1 e2]
      abel)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h3
  generalize hT : ((W * Js E _ * U - Js E _) * X).trace = T at h3
  have hv : valuation E ((p : E) * p) < valuation E (p * T) := by
    rw [show (p : E) * T = p * p * ((p : E)⁻¹ * T) by field_simp, map_mul _ (p * p : E)]
    exact lt_mul_of_one_lt_right (zero_lt_iff.2 (by simp)) h3
  obtain ⟨y, hy, hy1⟩ := hψ _ hv
  have hx0 : (p : E) * T ≠ 0 := fun e => by rw [e, map_zero] at hv; exact not_lt_zero hv
  have ht : valuation E (y / (p * T) * p) * 1 ≤ valuation E (p : E) := by
    rw [mul_one, map_mul, map_div₀]
    exact mul_le_of_le_one_left' (div_le_one_of_le₀ hy zero_le)
  have hk : Bd (valuation E (p : E)) ((1 + (y / (p * T) * p) • X) - 1) := by
    rw [add_sub_cancel_left]
    exact (h1.smul _).mono ht
  obtain ⟨k, hk'⟩ := unit_of hp hk
  have hc : ((u * k * u⁻¹ : GL (Fin (n + 1)) E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E) = 1 + (y / (p * T) * p) • (U * X * W) := by
    rw [Units.val_mul, Units.val_mul, hk', ← hU, ← hW, mul_add, add_mul, mul_one, hUW, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨k, hk' ▸ hk, ?_, fun e => hy1 ?_⟩
  · rw [hc, add_sub_cancel_left]
    exact (h2.smul _).mono ht
  · have e2 : GlobalTheory.Whittaker.superDiag (u * k * u⁻¹) = GlobalTheory.Whittaker.superDiag k + y := by
      rw [sd_eq, sd_eq, hc, hk', mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      have e3 : (Js E _ * (U * X * W)).trace = T + (Js E _ * X).trace := by
        rw [← hT, sub_mul, Matrix.trace_sub, sub_add_cancel, ← mul_assoc, Matrix.trace_mul_comm _ W]
        simp only [mul_assoc]
      rw [e3, mul_add, mul_assoc (y / (p * T)), div_mul_cancel₀ _ hx0]
      ring
    rw [e2, AddChar.map_add_eq_mul] at e
    exact mul_eq_left.1 e

end Local

end UpperTheory.V.Z.Tf.L4
