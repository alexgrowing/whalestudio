import ReciprocityTheory.DualLattices.CotangentSurjective

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.Smith

section general

variable {R : Type} [CommRing R]

def consEquiv (a : R) {b : ℕ} (c : Fin b → R) :
    ((R ⧸ Ideal.span {a}) × ((k : Fin b) → R ⧸ Ideal.span {c k})) ≃ₗ[R]
      ((j : Fin (b + 1)) → R ⧸ Ideal.span {(Fin.cons a c : Fin (b + 1) → R) j}) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, fun k => x k.succ)
  map_add' p q := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  map_smul' r p := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  left_inv p := rfl
  right_inv x := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl

theorem eq_of_removeNth {b : ℕ} (i0 : Fin (b + 1)) {x y : Fin (b + 1) → R} (h0 : x i0 = y i0)
    (h : Fin.removeNth i0 x = Fin.removeNth i0 y) : x = y := by
  rw [← Fin.insertNth_self_removeNth i0 x, ← Fin.insertNth_self_removeNth i0 y, h0, h]

theorem pivot_equiv {b : ℕ} {ι : Type} [Fintype ι] (g : ι → Fin (b + 1) → R) (i0 : Fin (b + 1))
    (a : R) (u : Fin (b + 1) → R) (s : ι → R) (hu : u i0 = 1)
    (hau : a • u ∈ Submodule.span R (Set.range g)) (hs : ∀ j, g j i0 = a * s j) :
    Nonempty (((Fin (b + 1) → R) ⧸ Submodule.span R (Set.range g)) ≃ₗ[R]
      ((R ⧸ Ideal.span {a}) × ((Fin b → R) ⧸
        Submodule.span R (Set.range fun j => Fin.removeNth i0 (g j - s j • a • u))))) := by
  classical
  set K'' := Submodule.span R (Set.range fun j => Fin.removeNth i0 (g j - s j • a • u)) with hK''
  let P : (Fin (b + 1) → R) →ₗ[R] (Fin (b + 1) → R) :=
    LinearMap.id - (LinearMap.proj i0).smulRight u
  let rem : (Fin (b + 1) → R) →ₗ[R] (Fin b → R) := LinearMap.funLeft R R i0.succAbove
  have hP : ∀ x, P x = x - x i0 • u := fun x => rfl
  have hrem : ∀ x, rem x = Fin.removeNth i0 x := fun x => rfl
  let Φ : (Fin (b + 1) → R) →ₗ[R] (R ⧸ Ideal.span {a}) × ((Fin b → R) ⧸ K'') :=
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.proj i0).prod (K''.mkQ ∘ₗ rem ∘ₗ P)
  have hΦ : ∀ x, Φ x = (Submodule.Quotient.mk (x i0), Submodule.Quotient.mk
      (Fin.removeNth i0 (x - x i0 • u))) := fun x => rfl
  have hsurj : Function.Surjective Φ := by
    rintro ⟨q1, q2⟩
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q1
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q2
    refine ⟨r • u + (Fin.insertNth i0 (0 : R) y : Fin (b + 1) → R), ?_⟩
    have hx0 : (r • u + (Fin.insertNth i0 (0 : R) y : Fin (b + 1) → R)) i0 = r := by
      simp [hu]
    rw [hΦ, hx0]
    congr 2
    ext k
    simp [Fin.removeNth, Fin.insertNth_apply_succAbove]
  have hker : LinearMap.ker Φ = Submodule.span R (Set.range g) := by
    ext x
    rw [LinearMap.mem_ker, hΦ, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      have hx : x = t • (a • u) + ∑ j, cc j • (g j - s j • a • u) := by
        have hsum : x - x i0 • u = ∑ j, cc j • (g j - s j • a • u) := by
          apply eq_of_removeNth i0
          · have hz : ∀ j, (cc j • (g j - s j • a • u)) i0 = 0 := by
              intro j; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs, hu]; ring
            rw [Finset.sum_apply, Finset.sum_eq_zero (fun j _ => hz j)]
            simp [hu]
          · rw [← hcc]
            ext k
            simp [Fin.removeNth, Finset.sum_apply]
        rw [← hsum, ← mul_smul, ht]
        abel
      rw [hx]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hau) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
          (Submodule.smul_mem _ _ hau)))
    · intro hx
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
      have hx0 : (∑ j, r j • g j) i0 = (∑ j, r j * s j) * a := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hs, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      refine ⟨Ideal.mem_span_singleton'.2 ⟨_, hx0.symm⟩, ?_⟩
      have e : (∑ j, r j • g j) - (∑ j, r j • g j) i0 • u =
          ∑ j, r j • (g j - s j • a • u) := by
        rw [hx0]
        simp only [smul_sub, Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_mul, Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_smul, mul_assoc]
      rw [e]
      have hlin : Fin.removeNth i0 (∑ j, r j • (g j - s j • a • u)) =
          ∑ j, r j • Fin.removeNth i0 (g j - s j • a • u) := by
        ext k; simp [Fin.removeNth, Finset.sum_apply]
      rw [hlin]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩

instance instSubsingletonQuotientFinZero (K : Submodule R (Fin 0 → R)) :
    Subsingleton ((Fin 0 → R) ⧸ K) :=
  ⟨fun x y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]⟩

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem exists_pivot (hv : v.Integers R) {b : ℕ} {ι : Type} [Fintype ι]
    (g : ι → Fin (b + 1) → R) :
    ∃ (i0 : Fin (b + 1)) (a : R) (u : Fin (b + 1) → R) (s : ι → R), u i0 = 1 ∧
      a • u ∈ Submodule.span R (Set.range g) ∧ (∀ j, g j i0 = a * s j) ∧
      (a = 0 → ∀ j, g j = 0) ∧ (a ≠ 0 → ∃ j0, g j0 = a • u ∧ s j0 = 1) := by
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  by_cases hall : ∀ j, g j = 0
  · refine ⟨0, 0, Pi.single 0 1, 0, by simp, by simp, fun j => by simp [hall j],
      fun _ => hall, fun h => absurd rfl h⟩
  · push Not at hall
    obtain ⟨j1, hj1⟩ := hall
    obtain ⟨i1, hi1⟩ : ∃ i, g j1 i ≠ 0 := by
      by_contra h; push Not at h; exact hj1 (funext h)
    obtain ⟨⟨j0, i0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ι × Fin (b + 1)))
      (fun p => v (algebraMap R C (g p.1 p.2))) ⟨(j1, i1), Finset.mem_univ _⟩
    set a := g j0 i0 with ha
    have hdvd : ∀ j i, a ∣ g j i := fun j i =>
      hv.dvd_of_le (hmax (j, i) (Finset.mem_univ _))
    have ha0 : a ≠ 0 := by
      intro h0
      have := hmax (j1, i1) (Finset.mem_univ _)
      rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at this
      exact hi1 (hv.hom_inj (by rw [this, map_zero]))
    choose u hu using hdvd j0
    choose s hs using fun j => hdvd j i0
    have hu0 : u i0 = 1 := by
      have h1 : a * u i0 = a * 1 := by rw [← hu i0, mul_one]
      exact mul_left_cancel₀ ha0 h1
    have hau : a • u = g j0 := by ext i; simp [hu i]
    refine ⟨i0, a, u, s, hu0, hau ▸ Submodule.subset_span ⟨j0, rfl⟩, hs, fun h => absurd h ha0,
      fun _ => ⟨j0, hau.symm, ?_⟩⟩
    have h1 : a * s j0 = a * 1 := by rw [← hs j0, mul_one]
    exact mul_left_cancel₀ ha0 h1

theorem smith_gen (hv : v.Integers R) : ∀ (b : ℕ) {ι : Type} [Fintype ι] (g : ι → Fin b → R),
    ∃ c : Fin b → R, Nonempty (((Fin b → R) ⧸ Submodule.span R (Set.range g)) ≃ₗ[R]
      ((i : Fin b) → R ⧸ Ideal.span {c i}))
  | 0, _, _, g => ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | b + 1, _, _, g => by
    obtain ⟨i0, a, u, s, hu, hau, hs, -, -⟩ := exists_pivot hv g
    obtain ⟨e1⟩ := pivot_equiv g i0 a u s hu hau hs
    obtain ⟨c', ⟨e2⟩⟩ := smith_gen hv b (fun j => Fin.removeNth i0 (g j - s j • a • u))
    exact ⟨Fin.cons a c', ⟨(e1.trans ((LinearEquiv.refl R _).prodCongr e2)).trans (consEquiv a c')⟩⟩

theorem hasLen_coker_gen (hv : v.Integers R) {b : ℕ} {ι : Type} [Fintype ι] (g : ι → Fin b → R) :
    HasLen v R ((Fin b → R) ⧸ Submodule.span R (Set.range g))
      (∏ i, v (algebraMap R C ((smith_gen hv b g).choose i))) :=
  ⟨b, _, (smith_gen hv b g).choose_spec, rfl⟩

theorem det_colop {b : ℕ} (X : Matrix (Fin (b + 1)) (Fin (b + 1)) R) (j0 : Fin (b + 1))
    (s : Fin (b + 1) → R) :
    (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0).det = X.det := by
  set V : Matrix (Fin (b + 1)) (Fin (b + 1)) R := Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))
    with hV
  have hXV : (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0) = X * V := by
    ext i l
    simp only [Matrix.of_apply, Matrix.mul_apply, hV]
    by_cases hl : l = j0
    · simp [hl]
    · simp only [hl, if_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
  have hV1 : V.det = 1 := by
    rw [Matrix.det_succ_column V j0, Finset.sum_eq_single j0]
    · have hsub : V.submatrix j0.succAbove j0.succAbove = 1 := by
        ext k l
        simp only [Matrix.submatrix_apply, hV, Matrix.of_apply, Fin.succAbove_ne, if_false,
          sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
      rw [hsub, Matrix.det_one]
      simp [hV, ← two_mul, pow_mul]
    · intro k _ hk
      simp [hV, hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hXV, Matrix.det_mul, hV1, mul_one]

theorem smith_sq (hv : v.Integers R) : ∀ (b : ℕ) (X : Matrix (Fin b) (Fin b) R),
    ∃ c : Fin b → R, Nonempty (((Fin b → R) ⧸ LinearMap.range X.mulVecLin) ≃ₗ[R]
      ((i : Fin b) → R ⧸ Ideal.span {c i})) ∧
      v (algebraMap R C X.det) = ∏ i, v (algebraMap R C (c i))
  | 0, X => ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩
  | b + 1, X => by
    classical
    set g : Fin (b + 1) → Fin (b + 1) → R := fun j i => X i j with hg
    have hrange : LinearMap.range X.mulVecLin = Submodule.span R (Set.range g) := by
      rw [Matrix.range_mulVecLin]; rfl
    obtain ⟨i0, a, u, s, hu, hau, hs, hz, hnz⟩ := exists_pivot hv g
    obtain ⟨e1⟩ := pivot_equiv g i0 a u s hu hau hs
    set h : Fin (b + 1) → Fin (b + 1) → R := fun j => g j - s j • a • u with hh
    have e0 := Submodule.quotEquivOfEq _ _ hrange
    have hprod : ∀ c' : Fin b → R, ∏ i, v (algebraMap R C ((Fin.cons a c' : Fin (b + 1) → R) i)) =
        v (algebraMap R C a) * ∏ k, v (algebraMap R C (c' k)) := by
      intro c'
      rw [Fin.prod_univ_succ]
      rfl
    by_cases ha : a = 0
    · obtain ⟨c', ⟨e2⟩⟩ := smith_gen hv b (fun j => Fin.removeNth i0 (g j - s j • a • u))
      refine ⟨Fin.cons a c', ⟨(e0.trans (e1.trans ((LinearEquiv.refl R _).prodCongr e2))).trans
        (consEquiv a c')⟩, ?_⟩
      have hX : X = 0 := by
        ext i j
        have := congrFun (hz ha j) i
        simpa [hg] using this
      rw [hprod, hX, Matrix.det_zero, ha]
      simp
    · obtain ⟨j0, hj0, hs0⟩ := hnz ha
      set X'' : Matrix (Fin b) (Fin b) R :=
        Matrix.of fun k l => h (j0.succAbove l) (i0.succAbove k) with hX''
      have hspan'' : Submodule.span R (Set.range fun j => Fin.removeNth i0 (g j - s j • a • u)) =
          LinearMap.range X''.mulVecLin := by
        rw [Matrix.range_mulVecLin]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          by_cases hj : j = j0
          · subst hj
            have : g j - s j • a • u = 0 := by rw [hj0, hs0, one_smul, sub_self]
            have hz0 : Fin.removeNth i0 (0 : Fin (b + 1) → R) = 0 := rfl
            show Fin.removeNth i0 (g j - s j • a • u) ∈ _
            rw [this, hz0]
            exact Submodule.zero_mem _
          · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
            exact Submodule.subset_span ⟨l, rfl⟩
        · rw [Submodule.span_le]
          rintro _ ⟨l, rfl⟩
          exact Submodule.subset_span ⟨j0.succAbove l, rfl⟩
      obtain ⟨c', ⟨e2⟩, hdet''⟩ := smith_sq hv b X''
      refine ⟨Fin.cons a c', ⟨(e0.trans (e1.trans ((LinearEquiv.refl R _).prodCongr
        ((Submodule.quotEquivOfEq _ _ hspan'').trans e2)))).trans (consEquiv a c')⟩, ?_⟩
      rw [hprod, ← hdet'', ← det_colop X j0 s, Matrix.det_succ_row _ i0,
        Finset.sum_eq_single j0]
      · have hsub : (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0).submatrix
            i0.succAbove j0.succAbove = X'' := by
          ext k l
          simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_ne, if_false, hX'', hh,
            hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have : X (i0.succAbove k) j0 = a * u (i0.succAbove k) := by
            have := congrFun hj0 (i0.succAbove k)
            simpa [hg] using this
          rw [this]
        have hX0 : X i0 j0 = a := by
          have := congrFun hj0 i0
          simpa [hg, hu] using this
        simp only [Matrix.of_apply, if_true, hsub, hX0, map_mul, map_pow, map_neg, map_one]
        simp
      · intro j _ hj
        have hX0 : X i0 j0 = a := by
          have := congrFun hj0 i0
          simpa [hg, hu] using this
        have hXj : X i0 j = a * s j := hs j
        simp [hj, hXj, hX0, mul_comm]
      · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hasLen_coker_det (hv : v.Integers R) {n : ℕ} (X : Matrix (Fin n) (Fin n) R) :
    HasLen v R ((Fin n → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  obtain ⟨c, e, h⟩ := smith_sq hv n X
  exact ⟨n, c, e, h.symm⟩

end ReciprocityTheory.PGsh.Up.Smith
