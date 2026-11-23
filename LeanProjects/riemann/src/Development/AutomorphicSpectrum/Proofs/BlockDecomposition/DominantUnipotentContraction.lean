import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantElementsGlValued

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.DomGLVal
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.DomUnitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}
variable (D : CassData (GU σ n))

theorem mem_J_iff (hJ : D.J = IwU σ n) (x : GU σ n) : x ∈ D.J ↔ (x : GL (Fin n) L) ∈ IwGL L n := by
  rw [hJ, IwU, Subgroup.mem_subgroupOf]

theorem upper_facts (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.N) :
    IsUniM (x : GL (Fin n) L) ∧ IsUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hN _).1 hx.2, (hN _).1 (inv_mem hx.2), h.1, h.2⟩

theorem lower_facts (hJ : D.J = IwU σ n) (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.Nm) :
    IsLowUniM (x : GL (Fin n) L) ∧ IsLowUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hNm _).1 hx.2, (hNm _).1 (inv_mem hx.2), h.1, h.2⟩

theorem dom_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hmono : ∀ i j : Fin n, i ≤ j → ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
      ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) :
    (∀ x ∈ D.J ⊓ D.N, τ * x * τ⁻¹ ∈ D.J ⊓ D.N) ∧ (∀ x ∈ D.J ⊓ D.Nm, τ⁻¹ * x * τ ∈ D.J ⊓ D.Nm) ∧
      ∀ x ∈ D.J ⊓ D.T, τ * x * τ⁻¹ ∈ D.J ⊓ D.T ∧ τ⁻¹ * x * τ ∈ D.J ⊓ D.T := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hmono' : ∀ i j, i ≤ j → ordL (d j) ≤ ordL (d i) := by simpa only [hdd] using hmono
  have hle : ∀ i j, i ≤ j → Valued.v (d i) * Valued.v (d j)⁻¹ ≤ 1 := fun i j hij =>
    ratio_le (hne j) (v_le_of_ordL_le (hne j) (hne i) (hmono' i j hij))
  have hle' : ∀ i j, j ≤ i → Valued.v (d i)⁻¹ * Valued.v ((d j)⁻¹)⁻¹ ≤ 1 := fun i j hij => by
    rw [inv_inv, mul_comm]
    exact hle j i hij
  have hs' := val_inv_diag hne hd
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u1, u2, i1, i2⟩ := upper_facts D hJ hN hx
    have := up_mem hne hd u1 u2 (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i1.1 i j))
      (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i2.1 i j))
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have := low_mem (fun i => inv_ne_zero (hne i)) hs' l1 l2
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i1.2 i j hij))
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i2.2 i j hij))
    rw [inv_inv] at this
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hNm _).2 this.2⟩
  · obtain ⟨hdx, -⟩ := diag_data ((hT _).1 hx.2)
    have hc : τ * x = x * τ := by
      apply Subtype.ext
      apply Units.ext
      show ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      rw [hd, hdx, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have e1 : τ * x * τ⁻¹ = x := by rw [hc, mul_inv_cancel_right]
    have e2 : τ⁻¹ * x * τ = x := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [e1, e2]
    exact ⟨hx, hx⟩

theorem strict_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hst : IsStrictDom (τ : GL (Fin n) L)) :
    (∀ x ∈ D.N, ∃ j : ℕ, τ ^ j * x * (τ ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
      ∀ U : Set (GU σ n), IsOpen U → (1 : GU σ n) ∈ U →
        ∃ j : ℕ, ∀ x ∈ D.J ⊓ D.Nm, (τ ^ j)⁻¹ * x * τ ^ j ∈ U := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hst' : ∀ i j, i < j → ordL (d j) < ordL (d i) := by
    intro i j hij
    have := hst i j hij
    rwa [hdd, hdd] at this
  have hr : ∀ i j, i < j → ∀ m : ℕ, Valued.v (d i ^ m) * Valued.v (d j ^ m)⁻¹ ≤ cc ^ m := fun i j hij m =>
    ratio_pow_le (hne j) (v_le_of_ordL_lt (hne j) (hne i) (hst' i j hij)) m
  have hpow : ∀ m : ℕ, (((τ ^ m : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => d i ^ m) := fun m => by
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow]
    rfl
  have hnep : ∀ m : ℕ, ∀ i, d i ^ m ≠ 0 := fun m i => pow_ne_zero _ (hne i)
  refine ⟨fun x hx => ?_, fun U hU h1 => ?_⟩
  · have u1 : IsUniM (x : GL (Fin n) L) := (hN _).1 hx
    have u2 : IsUniM (x : GL (Fin n) L)⁻¹ := (hN _).1 (inv_mem hx)
    choose f hf using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v (((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    choose f' hf' using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v ((((x : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    have hM : ∀ p, f p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_left (Finset.le_sup (Finset.mem_univ p))
    have hM' : ∀ p, f' p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p))
    generalize Finset.univ.sup f ⊔ Finset.univ.sup f' = M at hM hM'
    have key : ∀ (y : L) (i j : Fin n), i < j → cc ^ M * Valued.v y ≤ 1 →
        Valued.v (d i ^ M * y * (d j ^ M)⁻¹) ≤ 1 := by
      intro y i j hij hy
      rw [map_mul, map_mul, mul_right_comm]
      have h2 := hr i j hij M
      calc Valued.v (d i ^ M) * Valued.v (d j ^ M)⁻¹ * Valued.v y ≤ cc ^ M * Valued.v y := by gcongr
        _ ≤ 1 := hy
    have := up_mem (hnep M) (hpow M) u1 u2
      (fun i j hij => key _ i j hij (hf (i, j) M (hM _)))
      (fun i j hij => key _ i j hij (hf' (i, j) M (hM' _)))
    exact ⟨M, (mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨m, hm⟩ := open_shrink W hW h1
    refine ⟨m, fun x hx => ?_⟩
    obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have hs := val_inv_diag (hnep m) (hpow m)
    have hes : ∀ i, (d i ^ m)⁻¹ ≠ 0 := fun i => inv_ne_zero (hnep m i)
    have hb : ∀ a b, b < a → Valued.v (d a ^ m)⁻¹ * Valued.v ((d b ^ m)⁻¹)⁻¹ ≤ cc ^ m := fun a b hab => by
      rw [inv_inv, mul_comm]
      exact hr b a hab m
    have c1 := low_close hes hs l1 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i1.1 a b))
    have c2 := low_close hes hs l2 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i2.1 a b))
    have := hm _ c1 (by rw [GlobalTheory.CompanionTheory.DomGLVal.conj_inv]; exact c2)
    rw [inv_inv] at this
    exact this

theorem domU : PositivityTheory.SphericalProduct.DomU := by
  intro L _ _ _ ϖ σ q _ n D hJ hN hNm hT t
  refine ⟨fun h => dom_core D hJ hN hNm hT t t.2 h, fun h => ⟨?_, strict_core D hJ hN hNm hT t t.2 h⟩⟩
  exact dom_core D hJ hN hNm hT t t.2 fun i j hij => by
    rcases hij.lt_or_eq with hij | rfl
    · exact (h i j hij).le
    · exact le_rfl

end GlobalTheory.CompanionTheory.DomUnitary
