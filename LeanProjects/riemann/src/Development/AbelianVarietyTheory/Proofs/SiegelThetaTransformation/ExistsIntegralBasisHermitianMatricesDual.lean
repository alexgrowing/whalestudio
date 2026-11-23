import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.HermLat

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_add (x y : E) : cc (x + y) = cc x + cc y := map_add _ _ _
theorem cc_zero : cc (0 : E) = 0 := map_zero _
theorem cc_cc (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
theorem cc_smul (q : ℚ) (x : E) : cc (q • x) = q • cc x :=
  map_rat_smul (IsCMField.complexConj E) q x

theorem sum_univ {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ, g σ = ∑ τ : Ψ, (g τ + g (ComplexEmbedding.conjugate τ.1)) := by
  rw [Finset.sum_coe_sort Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ)),
    Finset.sum_add_distrib, ← Finset.sum_add_sum_compl Ψ]
  congr 1
  symm
  refine Finset.sum_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ; exact Finset.mem_compl.2 ((hΨ τ).1 hτ)
  · intro τ hτ
    by_contra hc
    exact Finset.mem_compl.1 hτ ((hΨ τ).2 hc)
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl

theorem half_trace {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} (hx : cc x = x) :
    (((1 / 2 : ℚ) * Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : Ψ, τ.1 x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ x = ∑ σ : E →+* ℂ, σ x :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun _ => rfl)).symm
  rw [h2, sum_univ hΨ] at h
  have h3 : ∀ τ : Ψ, ComplexEmbedding.conjugate τ.1 x = τ.1 x := fun τ => by
    rw [ComplexEmbedding.conjugate_coe_eq, ← Base.map_cc, hx]
  simp only [h3, ← two_mul, ← Finset.mul_sum] at h
  have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := rfl
  rw [h4] at h
  push_cast
  rw [h]; ring

theorem indep {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (u v : Ψ → ℂ)
    (h : ∀ x : E, ∑ τ : Ψ, (τ.1 x * u τ + conj (τ.1 x) * v τ) = 0) : u = 0 := by
  let f : Ψ ⊕ Ψ → (E →* ℂ) := Sum.elim (fun τ => (τ.1 : E →* ℂ))
    (fun τ => (ComplexEmbedding.conjugate τ.1 : E →* ℂ))
  have inj : ∀ a b : E →+* ℂ, (a : E →* ℂ) = (b : E →* ℂ) → a = b := fun a b e =>
    RingHom.ext fun x => DFunLike.congr_fun e x
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) e
    · rw [Subtype.ext (inj _ _ e)]
    · exact absurd ((inj _ _ e) ▸ a.2) ((hΨ b.1).1 b.2)
    · exact absurd ((inj _ _ e).symm ▸ b.2) ((hΨ a.1).1 a.2)
    · have := congrArg ComplexEmbedding.conjugate (inj _ _ e)
      have e2 : a.1 = b.1 := (star_star a.1).symm.trans (this.trans (star_star b.1))
      rw [Subtype.ext e2]
  have li := (linearIndependent_monoidHom E ℂ).comp f hf
  have := Fintype.linearIndependent_iff.1 li (Sum.elim u v) (by
    funext x
    have := h x
    rw [Finset.sum_add_distrib] at this
    simpa [f, Fintype.sum_sum_type, Finset.sum_apply, mul_comm] using this)
  funext τ
  exact this (Sum.inl τ)

def HermSub (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) :
    Submodule ℚ (Matrix (Fin N) (Fin N) E) where
  carrier := {X | ccT X = X}
  add_mem' {X Y} hX hY := by
    ext a b
    have h1 := congrFun (congrFun hX a) b
    have h2 := congrFun (congrFun hY a) b
    simp only [ccT, transpose_apply, map_apply, Matrix.add_apply] at h1 h2 ⊢
    rw [cc_add, h1, h2]
  zero_mem' := by
    ext a b
    simp [ccT, cc_zero]
  smul_mem' q X hX := by
    ext a b
    have h1 := congrFun (congrFun hX a) b
    simp only [ccT, transpose_apply, map_apply, Matrix.smul_apply] at h1 ⊢
    rw [cc_smul, h1]

theorem cc_trace {N : ℕ} (X : Matrix (Fin N) (Fin N) E) : cc X.trace = (ccT X).trace := by
  simp only [Matrix.trace, diag_apply, ccT, transpose_apply, map_apply, cc, map_sum]

theorem cc_trace_mul {N : ℕ} (X Y : HermSub E N) : cc (X.1 * Y.1).trace = (X.1 * Y.1).trace := by
  have hX : ccT X.1 = X.1 := X.2
  have hY : ccT Y.1 = Y.1 := Y.2
  rw [cc_trace, Base.ccT_mul, hX, hY, trace_mul_comm]

def form (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) :
    LinearMap.BilinForm ℚ (HermSub E N) :=
  LinearMap.mk₂ ℚ (fun X Y => (1 / 2 : ℚ) * Algebra.trace ℚ E (X.1 * Y.1).trace)
    (fun X X' Y => by simp [add_mul, mul_add])
    (fun q X Y => by simp [mul_left_comm])
    (fun X Y Y' => by simp [mul_add])
    (fun q X Y => by simp [mul_left_comm])

theorem form_eq {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ} (X Y : HermSub E N) :
    ((form E N X Y : ℚ) : ℂ) = ∑ τ : Ψ, τ.1 (X.1 * Y.1).trace :=
  half_trace hΨ (cc_trace_mul X Y)

theorem form_self {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ} (X : HermSub E N)
    (h : form E N X X = 0) : X = 0 := by
  have h1 := form_eq hΨ X X
  rw [h] at h1
  have hX : ccT X.1 = X.1 := X.2
  have h2 : ∀ τ : Ψ, τ.1 (X.1 * X.1).trace =
      ((∑ a, ∑ b, normSq (τ.1 (X.1 a b)) : ℝ) : ℂ) := fun τ => by
    simp only [Matrix.trace, diag_apply, mul_apply, map_sum, map_mul]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h3 : cc (X.1 a b) = X.1 b a := congrFun (congrFun hX b) a
    rw [← h3, Base.map_cc, Complex.mul_conj]
  simp only [h2] at h1
  have h4 : ∑ τ : Ψ, ∑ a, ∑ b, normSq (τ.1 (X.1 a b)) = 0 := by exact_mod_cast h1.symm
  obtain ⟨τ⟩ : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hσ : σ ∈ Ψ
    · exact ⟨⟨σ, hσ⟩⟩
    · exact ⟨⟨ComplexEmbedding.conjugate σ, by
        by_contra hc; exact hσ ((hΨ σ).2 hc)⟩⟩
  apply Subtype.ext
  ext a b
  have n0 : ∀ (τ : Ψ) a b, 0 ≤ normSq (τ.1 (X.1 a b)) := fun _ _ _ => normSq_nonneg _
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => n0 τ a b).1 h4 τ (Finset.mem_univ _)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => n0 τ a b).1 h5 a (Finset.mem_univ _)
  have h7 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => n0 τ a b).1 h6 b (Finset.mem_univ _)
  simpa using h7

theorem form_nondeg {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    (form E N).Nondegenerate :=
  ⟨fun X hX => form_self hΨ X (hX X), fun X hX => form_self hΨ X (hX X)⟩

omit [IsCMField E] in

theorem exists_den {ι : Type} [Fintype ι] {N : ℕ} (X : ι → Matrix (Fin N) (Fin N) E) :
    ∃ c : ℕ, 0 < c ∧ ∀ i, IntM ((c : E) • X i) := by
  have h : ∀ p : ι × Fin N × Fin N, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * X p.1 p.2.1 p.2.2) := by
    intro p
    have ha : IsAlgebraic ℤ (X p.1 p.2.1 p.2.2) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨d, hd, hi⟩ := ha.exists_integral_multiple
    refine ⟨d.natAbs, Int.natAbs_pos.2 hd, ?_⟩
    rw [zsmul_eq_mul] at hi
    rcases Int.natAbs_eq d with e | e
    · rw [e] at hi; simpa using hi
    · rw [e] at hi; simpa using hi.neg
  choose d hd hi using h
  refine ⟨∏ p, d p, Finset.prod_pos fun p _ => hd p, fun i a b => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, a, b)), Matrix.smul_apply, smul_eq_mul,
    Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi (i, a, b))
  simpa using isIntegral_algebraMap (R := ℤ) (A := E)
    (x := ((∏ p ∈ Finset.univ.erase (i, a, b), d p : ℕ) : ℤ))

theorem functional_eq_zero {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ}
    (L : CM Ψ N N →ₗ[ℂ] ℂ) (h : ∀ X : HermSub E N, L (fun τ => X.1.map τ.1) = 0) : L = 0 := by
  have key : ∀ (τ : Ψ) (a b : Fin N), L (Pi.single τ (Matrix.single a b 1)) = 0 := by
    intro τ a b
    have := indep hΨ (fun τ => L (Pi.single τ (Matrix.single a b 1)))
      (fun τ => L (Pi.single τ (Matrix.single b a 1))) (fun x => by
        have hm : Matrix.single a b x + Matrix.single b a (cc x) ∈ HermSub E N := by
          show ccT _ = _
          ext k l
          simp only [ccT, transpose_apply, map_apply, Matrix.add_apply, Matrix.single_apply, cc_add,
            apply_ite cc, cc_cc, cc_zero, and_comm]
          rw [add_comm]
        rw [← h ⟨_, hm⟩]
        simp only [← smul_eq_mul, ← map_smul, ← map_add, ← map_sum]
        congr 1
        funext σ
        rw [Finset.sum_apply, Finset.sum_eq_single σ]
        · ext k l
          simp [Matrix.single_apply, apply_ite σ.1, Base.map_cc]
        · intro τ _ hτ
          simp [Pi.single_eq_of_ne hτ.symm]
        · simp)
    exact congrFun this τ
  refine LinearMap.pi_ext fun τ Z => ?_
  have hZ : (Pi.single τ Z : CM Ψ N N) =
      ∑ a, ∑ b, Z a b • (Pi.single τ (Matrix.single a b 1) : CM Ψ N N) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single,
        smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single Z
    · simp [Finset.sum_apply, Pi.single_eq_of_ne hσ]
  rw [hZ]
  simp only [map_sum, map_smul, key, smul_zero, Finset.sum_const_zero]
  simp

theorem exists_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N R : ℕ, 0 < R → ∃ (m : ℕ) (β T : Fin m → Matrix (Fin N) (Fin N) E) (c : ℕ), 0 < c ∧ (∀ i, ccT (β i) = β i ∧ ccT (T i) = T i ∧ Den c (T i) ∧ ∃ y : Matrix (Fin N) (Fin N) E, IntM y ∧ ccT y = y ∧ β i = (R : E) • y) ∧ (∀ i j, ∑ τ : Ψ, τ.1 (T i * β j).trace = if i = j then 1 else 0) ∧ ∀ Z : CM Ψ N N, Z = fun τ => ∑ j, (∑ σ : Ψ, ((T j).map σ.1 * Z σ).trace) • (β j).map τ.1 := by
  intro E _ _ _ Ψ hΨ N R hR
  let b₀ := Module.finBasis ℚ (HermSub E N)
  obtain ⟨d, hd, hdi⟩ := exists_den (fun i => (b₀ i).1)
  have hu : ((R : ℚ) * d) ≠ 0 := by positivity
  let b := b₀.unitsSMul (fun _ => Units.mk0 _ hu)
  have hb : ∀ i, (b i).1 = (R : E) • ((d : E) • (b₀ i).1) := fun i => by
    simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, Submodule.coe_smul]
    ext k l
    simp [Rat.smul_def, mul_assoc]
  let t := (form E N).dualBasis (form_nondeg hΨ N) b
  have ht : ∀ i j, form E N (t i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [LinearMap.BilinForm.apply_dualBasis_left]
    simp only [eq_comm]
  obtain ⟨c, hc, hci⟩ := exists_den (fun i => (t i).1)
  refine ⟨_, fun i => (b i).1, fun i => (t i).1, c, hc, fun i => ⟨(b i).2, (t i).2, hci i,
    _, hdi i, ?_, hb i⟩, fun i j => ?_, fun Z => ?_⟩
  · have : (d : E) • (b₀ i).1 = ((d : ℚ) • b₀ i).1 := by
      ext k l
      simp [Rat.smul_def]
    rw [this]
    exact ((d : ℚ) • b₀ i).2
  · rw [← form_eq hΨ, ht]
    split_ifs <;> simp
  · have hrep : ∀ (X : HermSub E N) j, b.repr X j = form E N (t j) X := fun X j => by
      conv_rhs => rw [← b.sum_repr X]
      simp only [map_sum, map_smul, ht, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    funext τ
    ext k l
    let L : CM Ψ N N →ₗ[ℂ] ℂ :=
      { toFun := fun Z => Z τ k l -
          (∑ j, (∑ σ : Ψ, (((t j).1).map σ.1 * Z σ).trace) • ((b j).1).map τ.1) k l
        map_add' := fun Z W => by
          simp only [Pi.add_apply, Matrix.mul_add, trace_add, Finset.sum_add_distrib, add_smul,
            Matrix.add_apply]
          ring
        map_smul' := fun s Z => by
          simp only [Pi.smul_apply, Matrix.mul_smul, trace_smul, ← Finset.smul_sum, smul_assoc,
            Matrix.smul_apply, RingHom.id_apply, smul_sub] }
    have hL : L = 0 := functional_eq_zero hΨ L fun X => by
      have h1 : ∀ j, (∑ σ : Ψ, (((t j).1).map σ.1 * X.1.map σ.1).trace) =
          ((b.repr X j : ℚ) : ℂ) := fun j => by
        rw [hrep, form_eq hΨ]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Matrix.map_mul, AddMonoidHom.map_trace]
      show τ.1 (X.1 k l) - (∑ j, (∑ σ : Ψ, (((t j).1).map σ.1 * X.1.map σ.1).trace) •
        ((b j).1).map τ.1) k l = 0
      simp only [h1]
      have h2 : X.1 = ∑ j, b.repr X j • (b j).1 := by
        conv_lhs => rw [← b.sum_repr X]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      rw [sub_eq_zero]
      conv_lhs => rw [h2]
      simp [Matrix.sum_apply, Rat.smul_def]
    exact sub_eq_zero.1 (LinearMap.congr_fun hL Z)

end

end GlobalTheory.SW.HermLat
