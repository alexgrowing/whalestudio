import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag

noncomputable section
namespace GlobalTheory.GLGen
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

theorem single_neg' (x y : Fin n) (a : R) : single x y (-a) = -single x y a := by
  ext p q; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp

theorem diag_transv_diag (a b : Fin n → R) (hab : ∀ k, a k * b k = 1) {i j : Fin n} (hij : i ≠ j) (c : R) :
    diagonal a * transvection i j c * diagonal b = transvection i j (a i * c * b j) := by
  have h1 : diagonal a * diagonal b = (1 : Matrix (Fin n) (Fin n) R) := by
    rw [diagonal_mul_diagonal]; simp [hab]
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  congr 1
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h <;> simp_all

theorem w_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-((u⁻¹ : Rˣ) : R)) * transvection i j (u : R) =
      1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1 := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, z1, z2, z3, z4]
  simp only [mul_neg, neg_mul, Units.mul_inv, Units.inv_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, single_neg', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]
  abel

theorem ww_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    (1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) *
      (1 + single i j ((-1 : Rˣ) : R) + single j i (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) =
      diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1) := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, z1, z2, z3, z4]
  clear z1 z2 z3 z4
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hji : j ≠ i := Ne.symm hij
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi; simp [hij, hji]
    · by_cases hpj : p = j
      · subst hpj; simp [hij, hji]
      · simp [hpi, hpj, Ne.symm hpi, Ne.symm hpj]
  · by_cases hpi : p = i <;> by_cases hqi : q = i <;> by_cases hpj : p = j <;> by_cases hqj : q = j <;>
      simp_all [eq_comm]

def diagU (u : Fin n → Rˣ) : GL (Fin n) R :=
  ⟨diagonal (fun k => (u k : R)), diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem diagU_val (u : Fin n → Rˣ) : ((diagU u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (u k : R)) := rfl

theorem diagU_inv_val (u : Fin n → Rˣ) :
    (((diagU u)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)) := rfl

theorem diagU_mul (u v : Fin n → Rˣ) : diagU (u * v) = diagU u * diagU v := by
  ext : 1
  simp only [Units.val_mul, diagU_val, diagonal_mul_diagonal, Pi.mul_apply]

theorem diagU_one : diagU (1 : Fin n → Rˣ) = 1 := by
  ext : 1
  simp [diagU_val]

def transvGL {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]⟩

def transvSet (R : Type) [CommRing R] (n : ℕ) : Set (GL (Fin n) R) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin n) (Fin n) R) = transvection i j c}

def elem (R : Type) [CommRing R] (n : ℕ) : Subgroup (GL (Fin n) R) := Subgroup.closure (transvSet R n)

theorem transvGL_mem {i j : Fin n} (hij : i ≠ j) (c : R) : transvGL hij c ∈ elem R n :=
  Subgroup.subset_closure ⟨i, j, c, hij, rfl⟩

theorem conj_mem (u : Fin n → Rˣ) {e : GL (Fin n) R} (he : e ∈ elem R n) :
    diagU u * e * (diagU u)⁻¹ ∈ elem R n := by
  have hle : elem R n ≤ (elem R n).comap (MulAut.conj (diagU u)).toMonoidHom := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨i, j, (u i : R) * c * ((u j)⁻¹ : Rˣ), hij, ?_⟩
    rw [Units.val_mul, Units.val_mul, hg, diagU_val, diagU_inv_val]
    exact diag_transv_diag _ _ (fun k => Units.mul_inv (u k)) hij c
  simpa using hle he

theorem whitehead_mem {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) ∈ elem R n := by
  have e : diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) =
      transvGL hij (u : R) * transvGL hij.symm (-((u⁻¹ : Rˣ) : R)) * transvGL hij (u : R) *
      (transvGL hij ((-1 : Rˣ) : R) * transvGL hij.symm (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) *
        transvGL hij ((-1 : Rˣ) : R)) := by
    ext : 1
    simp only [Units.val_mul, transvGL, diagU_val]
    rw [w_eq hij u, w_eq hij (-1), ww_eq hij u]
    congr 1
    funext k
    split_ifs <;> rfl
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) <;> exact transvGL_mem _ _

theorem diagU_inv (u : Fin n → Rˣ) : diagU u⁻¹ = (diagU u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagU_mul, inv_mul_cancel, diagU_one])

def diagHomU : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun := diagU
  map_one' := diagU_one
  map_mul' := diagU_mul

theorem pair_mem_elem (i j : Fin n) (a : Rˣ) :
    diagU (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) ∈ elem R n := by
  by_cases hij : i = j
  · subst hij
    have : (Pi.mulSingle i a * Pi.mulSingle i a⁻¹ : Fin n → Rˣ) = 1 := by
      rw [← Pi.mulSingle_mul]; simp
    rw [this, diagU_one]
    exact one_mem _
  · have hji : j ≠ i := fun h => hij h.symm
    have : (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) =
        fun k => if k = i then a else if k = j then a⁻¹ else 1 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    rw [this]
    exact whitehead_mem hij a

theorem diag_mem_of_prod (u : Fin n → Rˣ) (hu : ∏ k, u k = 1) : diagU u ∈ elem R n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : diagU u = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
    exact one_mem _
  · let j : Fin n := ⟨0, hpos⟩
    have key : u = ∏ k, (Pi.mulSingle k (u k) * Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ) := by
      rw [Finset.prod_mul_distrib, Finset.univ_prod_mulSingle]
      have : (∏ k, (Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)) = 1 := by
        have h := map_prod (MonoidHom.mulSingle (fun _ : Fin n => Rˣ) j) (fun k => (u k)⁻¹)
          Finset.univ
        rw [Finset.prod_inv_distrib, hu, inv_one, map_one] at h
        exact h.symm
      rw [this, mul_one]
    have : u ∈ (elem R n).comap (diagHomU (R := R) (n := n)) := by
      rw [key]
      exact Subgroup.prod_mem _ (fun k _ => pair_mem_elem k j (u k))
    exact this

theorem det_eq_one_of_mem {e : GL (Fin n) R} (he : e ∈ elem R n) : GeneralLinearGroup.det e = 1 := by
  have hle : elem R n ≤ (GeneralLinearGroup.det : GL (Fin n) R →* Rˣ).ker := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ hij]
    rfl
  exact hle he

theorem mem_of_det_eq_one : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) →
    ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R),
      u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  intro R _ hsr n H hH a ha
  have hEH : elem R n ≤ H := Subgroup.closure_le _ |>.2 (by
    rintro g ⟨i, j, c, hij, hg⟩; exact hH i j hij c g hg)
  have hSR : PI.VolSemiDirect.W.Cj.HasStableRangeOne R := fun a b x y h =>
    hsr a b ⟨x, y, by rw [← h]; ring⟩
  have hmem := PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag R hSR n a
  have key : ∀ g ∈ Subgroup.closure ({g : GL (Fin n) R | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin n → R, (g : Matrix (Fin n) (Fin n) R) = Matrix.diagonal d}),
      ∃ u : Fin n → Rˣ, g * diagU u ∈ elem R n := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨i, j, c, hij, hg⟩ | ⟨d, hd⟩
      · exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.subset_closure ⟨i, j, c, hij, hg⟩⟩
      · have hu : ∀ k, IsUnit (d k) := fun k => by
          have h : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          have h' := congrFun (congrFun h k) k
          rw [hd, Matrix.mul_diagonal, one_apply_eq] at h'
          exact ⟨⟨d k, _, by rw [mul_comm]; exact h', h'⟩, rfl⟩
        refine ⟨fun k => (hu k).unit⁻¹, ?_⟩
        have e : g * diagU (fun k => (hu k).unit⁻¹) = 1 := by
          ext : 1
          rw [Units.val_mul, hd, diagU_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
          congr 1
          funext k
          exact (hu k).mul_val_inv
        rw [e]; exact Subgroup.one_mem _
    | one => exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨v * u, ?_⟩
      have h := Subgroup.mul_mem _ hu (conj_mem u⁻¹ hv)
      rw [diagU_inv, inv_inv] at h
      convert h using 1
      rw [diagU_mul]
      group
    | inv x _ hx =>
      obtain ⟨u, hu⟩ := hx
      refine ⟨u⁻¹, ?_⟩
      have h := conj_mem u (Subgroup.inv_mem _ hu)
      rw [diagU_inv]
      convert h using 1
      group
  obtain ⟨u, hu⟩ := key a hmem
  have h1 := det_eq_one_of_mem hu
  rw [map_mul, ha, one_mul] at h1
  have hprod : ∏ k, u k = 1 := by
    have h2 := congrArg Units.val h1
    rw [GeneralLinearGroup.val_det_apply, diagU_val, det_diagonal] at h2
    ext
    rw [Units.coe_prod]
    simpa using h2
  have hd := diag_mem_of_prod u hprod
  have e : a = (a * diagU u) * (diagU u)⁻¹ := by group
  rw [e]
  exact hEH (Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hd))

end GlobalTheory.GLGen
