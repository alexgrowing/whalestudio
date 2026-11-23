import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix

namespace LateralTheory.DivDb.DegPoly₂

theorem exists_minor {F ι : Type*} [Field F] [Fintype ι] {k : ℕ} (v : Fin k → ι → F)
    (hv : LinearIndependent F v) :
    ∃ l : Fin k → ι, (Matrix.of fun a b => v b (l a)).det ≠ 0 := by
  classical
  let r : ι → Fin k → F := fun i b => v b i
  let V : Matrix ι (Fin k) F := Matrix.of r
  have h1 : V.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have : V.col = v := by funext b i; rfl
    rw [this, finrank_span_eq_card hv, Fintype.card_fin]
  have h2 : Submodule.span F (Set.range r) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Matrix.rank_eq_finrank_span_row V
    rw [h1] at this
    rw [Module.finrank_fin_fun]
    exact this.symm
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' F r
  rw [h2] at hsp
  let bs := Module.Basis.mk hli (by rw [hsp])
  have : Finite κ := Module.Finite.finite_basis bs
  haveI : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = k := by
    rw [← Module.finrank_eq_card_basis bs, Module.finrank_fin_fun]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ?_⟩
  have hrows : LinearIndependent F (Matrix.of fun a' b => v b ((a ∘ e) a')).row :=
    hli.comp e e.injective
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hrows
  exact hrows.ne_zero

theorem not_li_iff {F ι : Type*} [Field F] [Fintype ι] {k : ℕ} (v : Fin k → ι → F) :
    ¬ LinearIndependent F v ↔ ∀ l : Fin k → ι, (Matrix.of fun a b => v b (l a)).det = 0 := by
  classical
  constructor
  · intro h l
    rw [Fintype.not_linearIndependent_iff] at h
    obtain ⟨g, hg, i, hi⟩ := h
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨g, fun h0 => hi (by rw [h0]; rfl), ?_⟩
    funext a
    have := congrFun hg (l a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  · intro h hv
    obtain ⟨l, hl⟩ := exists_minor v hv
    exact hl (h l)

theorem deg_iff_not_li {F : Type} [Field F] {N n : ℕ} (x : Mat F N) :
    Deg n x ↔ ¬ LinearIndependent F (fun (b : Fin (n+1)) (p : Fin N × Fin N) => (x ^ (b : ℕ)) p.1 p.2) := by
  classical
  rw [Fintype.not_linearIndependent_iff]
  constructor
  · rintro ⟨q, hq0, hqd, hqx⟩
    refine ⟨fun b => q.coeff b, ?_, ?_⟩
    · have h1 : q = ∑ i ∈ Finset.range (n+1), Polynomial.monomial i (q.coeff i) :=
        q.as_sum_range' (n+1) (by omega)
      have h2 : Polynomial.aeval x q = ∑ b : Fin (n+1), q.coeff b • x ^ (b : ℕ) := by
        conv_lhs => rw [h1]
        rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.aeval x (Polynomial.monomial i (q.coeff i)))]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Polynomial.aeval_monomial, Algebra.smul_def]
      rw [h2] at hqx
      funext p
      have := congrArg (fun M : Mat F N => M p.1 p.2) hqx
      simpa [Matrix.sum_apply, Finset.sum_apply] using this
    · by_contra hall
      push Not at hall
      apply hq0
      ext i
      by_cases hi : i < n + 1
      · simpa using hall ⟨i, hi⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · rintro ⟨g, hg, i, hi⟩
    refine ⟨∑ b : Fin (n+1), Polynomial.monomial (b : ℕ) (g b), ?_, ?_, ?_⟩
    · intro h0
      apply hi
      have := congrArg (fun q => Polynomial.coeff q (i : ℕ)) h0
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
      · simp
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro b _
      exact (Polynomial.natDegree_monomial_le _).trans (by omega)
    · rw [map_sum]
      ext j k
      have := congrFun hg (j, k)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Polynomial.aeval_monomial, Matrix.sum_apply, Matrix.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]

noncomputable def gen (C : Type) [Field C] (N : ℕ) : Mat (MP C N) N :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

noncomputable def fam (C : Type) [Field C] (N n : ℕ) : Set (MP C N) :=
  Set.range fun l : Fin (n+1) → Fin N × Fin N =>
    (Matrix.of fun a b : Fin (n+1) => (gen C N ^ (b : ℕ)) (l a).1 (l a).2).det

theorem eval_fam {C : Type} [Field C] {N n : ℕ} {F : Type} [Field F] [Algebra C F] (x : Mat F N)
    (l : Fin (n+1) → Fin N × Fin N) :
    MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2)
      ((Matrix.of fun a b : Fin (n+1) => (gen C N ^ (b : ℕ)) (l a).1 (l a).2).det) =
    (Matrix.of fun a b : Fin (n+1) => (x ^ (b : ℕ)) (l a).1 (l a).2).det := by
  set φ := MvPolynomial.aeval (R := C) (fun p : Fin N × Fin N => x p.1 p.2)
  have hG : φ.mapMatrix (gen C N) = x := by
    ext i j; simp [gen, φ, AlgHom.mapMatrix_apply]
  have hpow : ∀ b : ℕ, φ.mapMatrix (gen C N ^ b) = x ^ b := fun b => by rw [map_pow, hG]
  rw [AlgHom.map_det]
  congr 1
  ext a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← hpow b,
    AlgHom.mapMatrix_apply, Matrix.map_apply]

theorem DegPoly_of : DegPoly := by
  intro C _ N n
  refine ⟨fam C N n, ?_⟩
  intro F _ _ x
  rw [deg_iff_not_li, not_li_iff]
  constructor
  · rintro h f ⟨l, rfl⟩
    rw [eval_fam]; exact h l
  · intro h l
    rw [← eval_fam (C := C)]; exact h _ ⟨l, rfl⟩

end LateralTheory.DivDb.DegPoly₂
