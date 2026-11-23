import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundOfEdgeCount

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def emb (w : Fin k → W) : Fin k → Qq := fun i => algebraMap W Qq (w i)

abbrev mapM (N : Matrix (Fin k) (Fin k) W) : Matrix (Fin k) (Fin k) Qq := (algebraMap W Qq).mapMatrix N

theorem mem_colSpan_iff (h : Matrix (Fin k) (Fin k) Qq) (x : Fin k → Qq) :
    x ∈ colSpan W h ↔ ∃ y : Fin k → W, x = fun i => ∑ c, h i c * algebraMap W Qq (y c) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]

theorem colSpan_mul_le (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) :
    colSpan W (h * mapM N) ≤ colSpan W h := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  refine (mem_colSpan_iff h _).2 ⟨fun j => N j c, funext fun i => ?_⟩
  simp [Matrix.mul_apply, mapM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem colSpan_unimod (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) (hN : IsUnit N.det) :
    colSpan W (h * mapM N) = colSpan W h := by
  refine le_antisymm (colSpan_mul_le h N) ?_
  have h1 : h * mapM N * mapM N⁻¹ = h := by
    rw [Matrix.mul_assoc, ← map_mul, Matrix.mul_nonsing_inv N hN, map_one, Matrix.mul_one]
  calc colSpan W h = colSpan W (h * mapM N * mapM N⁻¹) := by rw [h1]
    _ ≤ colSpan W (h * mapM N) := colSpan_mul_le _ _

theorem map_colSpan (g : GL (Fin k) Qq) (h : Matrix (Fin k) (Fin k) Qq) :
    (colSpan W h).map (nt_phi W g) = colSpan W ((g : Matrix (Fin k) (Fin k) Qq) * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

def dj (j : Fin k) (c : Qq) : Matrix (Fin k) (Fin k) Qq := Matrix.diagonal fun i => if i = j then c else 1

theorem dj_det (j : Fin k) (c : Qq) : (dj j c).det = c := by
  simp [dj, Matrix.det_diagonal]

theorem dj_mul (j : Fin k) (c d : Qq) : dj j c * dj j d = dj j (c * d) := by
  simp only [dj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dj_one (j : Fin k) : dj j (1 : Qq) = 1 := by
  simp [dj]

end Gen

section Base

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

theorem RS.injW : Function.Injective (algebraMap R.W R.Qq) := by
  haveI := R.std.1.frac_alt
  exact IsFractionRing.injective R.W R.Qq

theorem RS.pQ_ne : (p : R.Qq) ≠ 0 := by
  have h1 : (p : R.W) ≠ 0 := R.std.1.p_unif.ne_zero
  rw [← map_natCast (algebraMap R.W R.Qq)]
  exact fun h => h1 ((map_eq_zero_iff _ (RS.injW R)).1 h)

def embLin (R : RS p n') (k : ℕ) : (Fin k → R.W) →ₗ[R.W] (Fin k → R.Qq) where
  toFun := emb
  map_add' := by intro x y; funext i; simp [emb]
  map_smul' := by intro c x; funext i; simp [emb, Algebra.smul_def]

theorem embLin_inj : Function.Injective (embLin R k) := by
  intro x y hxy
  funext i
  exact RS.injW R (congrFun hxy i)

theorem colSpan_one_eq : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) = LinearMap.range (embLin R k) := by
  ext x
  rw [mem_colSpan_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]

theorem mem_dj_iff (j : Fin k) (x : Fin k → R.Qq) :
    x ∈ colSpan R.W (dj j (p : R.Qq)) ↔ ∃ y : Fin k → R.W, x = emb (fun i => (if i = j then (p : R.W) else 1) * y i) := by
  rw [mem_colSpan_iff]
  constructor <;> rintro ⟨y, rfl⟩ <;> refine ⟨y, funext fun i => ?_⟩ <;>
    by_cases hij : i = j <;> simp [dj, emb, Matrix.diagonal_apply, hij]

theorem baseEdge (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  classical
  have hstd := R.std.1
  have htgt : ∀ x, x ∈ colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ↔ ∃ y, embLin R k y = x := by
    intro x
    rw [colSpan_one_eq R]
    exact LinearMap.mem_range
  have hsrc : ∀ x, x ∈ colSpan R.W (dj j (p : R.Qq)) ↔
      ∃ y : Fin k → R.W, x = emb y ∧ y j ∈ Ideal.span {(p : R.W)} := by
    intro x
    rw [mem_dj_iff R]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨_, rfl, ?_⟩
      simp only [if_pos rfl]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rintro ⟨y, rfl, hy⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨fun i => if i = j then z else y i, ?_⟩
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij
        simp [← hz, mul_comm]
      · simp [hij]
  let e := LinearEquiv.ofInjective (embLin R k) (embLin_inj R)
  let E : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ≃ₗ[R.W] (Fin k → R.W) :=
    (LinearEquiv.ofEq _ _ (colSpan_one_eq R)).trans e.symm
  have hE : ∀ x, emb (E x) = (x : Fin k → R.Qq) := by
    intro x
    have h2 := congrArg Subtype.val (e.apply_symm_apply (LinearEquiv.ofEq _ _ (colSpan_one_eq R) x))
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let ψ : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) →ₗ[R.W] R.W ⧸ Ideal.span {(p : R.W)} :=
    (Ideal.span {(p : R.W)}).mkQ ∘ₗ LinearMap.proj j ∘ₗ E.toLinearMap
  have hψ : ∀ x, ψ x = (Submodule.Quotient.mk (E x j) : R.W ⧸ Ideal.span {(p : R.W)}) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨E.symm (Pi.single j a), ?_⟩
    rw [hψ, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  have hker : Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
      (colSpan R.W (dj j (p : R.Qq))) = LinearMap.ker ψ := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, hsrc]
    constructor
    · rintro ⟨y, hy, hyj⟩
      have hxy : E x = y := embLin_inj R ((hE x).trans hy)
      rw [hxy]
      exact hyj
    · intro h
      exact ⟨E x, (hE x).symm, h⟩
  refine ⟨⟨dj j (p : R.Qq), ?_, rfl⟩, ⟨1, by simp, rfl⟩, ?_, ?_, ?_⟩
  · rw [dj_det]
    exact isUnit_iff_ne_zero.2 (RS.pQ_ne R)
  · intro x hx
    obtain ⟨y, rfl, -⟩ := (hsrc x).1 hx
    exact (htgt _).2 ⟨y, rfl⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := (htgt x).1 hx
    refine (hsrc _).2 ⟨(p : R.W) • y, ?_, ?_⟩
    · funext i
      simp [embLin, emb, Algebra.smul_def]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · show Nat.card (↥(colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)) ⧸
      Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
        (colSpan R.W (dj j (p : R.Qq)))) = p ^ (n' * 1)
    rw [hker, Nat.card_congr (ψ.quotKerEquivOfSurjective hsurj).toEquiv, hstd.res_card, mul_one]

end Base

end Formalism.MainNotions.flipOneThree.Pf

end
