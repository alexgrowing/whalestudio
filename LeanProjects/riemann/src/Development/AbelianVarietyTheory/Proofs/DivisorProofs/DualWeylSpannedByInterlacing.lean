import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCompare.Surj

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

variable {K : Type} [Field K]

theorem rowAct_initMinor_mem {r m s : ℕ} (g : Matrix (Fin r) (Fin r) K) (I : Fin s → Fin r) (hs : s ≤ m) :
    rowAct K g (initMinor K I hs) ∈ Submodule.span K (Set.range fun J : Fin s → Fin r => initMinor K J hs) := by
  classical
  have h1 : rowAct K g (initMinor K I hs) =
      (Matrix.detRowAlternating (n := Fin s) (R := MvPolynomial (Fin r × Fin m) K)).toMultilinearMap
        (fun p => ∑ b : Fin r, (C (g (I p) b) : MvPolynomial (Fin r × Fin m) K) •
          fun q : Fin s => (X (b, Fin.castLE hs q) : MvPolynomial (Fin r × Fin m) K)) := by
    unfold initMinor
    rw [AlgHom.map_det]
    change Matrix.det _ = Matrix.det _
    congr 1
    ext p q : 2
    simp [rowAct, Finset.sum_apply]
  rw [h1, MultilinearMap.map_sum]
  refine Submodule.sum_mem _ fun J _ => ?_
  rw [MultilinearMap.map_smul_univ, ← map_prod, smul_eq_mul, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)

theorem prod_mem_span_range {A ι : Type} [CommRing A] [Algebra K A] [Fintype ι] {J : ι → Type}
    (f : ∀ i, J i → A) (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (Set.range (f i))) :
    ∏ i, x i ∈ Submodule.span K (Set.range fun t : ∀ i, J i => ∏ i, f i (t i)) := by
  classical
  refine Submodule.span_mono ?_ (GlobalTheory.OrbitSpan.prod_mem_span_prod Finset.univ _ x hx)
  intro y hy
  rw [Set.mem_fintype_prod] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  choose t ht using hz
  exact ⟨t, Finset.prod_congr rfl fun i _ => ht i⟩

theorem rowAct_piGen_mem {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) (g : Matrix (Fin n) (Fin n) K)
    (t : Gen lam sg) : rowAct K g (piGen K lam sg t) ∈ Submodule.span K (Set.range (piGen K lam sg)) := by
  unfold piGen
  simp only [map_mul, map_prod]
  have h1 := prod_mem_span_range (K := K) _ _ fun i : Fin n => prod_mem_span_range _ _
    fun k : Fin (aNum lam sg i) => rowAct_initMinor_mem g (t.1 i k) (Nat.succ_le_of_lt i.isLt)
  have h2 := prod_mem_span_range (K := K) _ _ fun i : Fin n => prod_mem_span_range _ _
    fun k : Fin (bNum lam sg i) => rowAct_initMinor_mem g (t.2 i k) i.isLt.le
  have h3 := Submodule.mul_mem_mul h1 h2
  rw [Submodule.span_mul_span] at h3
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩
  exact ⟨(u, v), rfl⟩

theorem prod_shift {A : Type} [CommMonoid A] {n : ℕ} (D : ℕ → A) (h0 : D 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, D i.val ^ b i = ∏ i : Fin n, D (i.val + 1) ^ nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    have h1 : nuNext b (Fin.last m) = 0 := by simp [nuNext]
    rw [h1, pow_zero, mul_one, Fin.val_zero, h0, one_pow, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 : nuNext b i.castSucc = b i.succ := by
      unfold nuNext
      rw [dif_pos (by simp)]
      rfl
    rw [h2]
    rfl

theorem aNum_add_bNext {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (h : Interlace lam sg)
    (he : EqualLast lam sg) (i : Fin n) :
    aNum lam sg i + nuNext (bNum lam sg) i = sg.natW i - nuNext sg.natW i := by
  have hn : 0 < n := Fin.pos i
  unfold nuNext
  simp only [aNum, bNum, DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have h1 := (h i).1
  split_ifs with hi
  · have h2 := (h ⟨i.val + 1, hi⟩).2
    have h3 : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := rfl
    have h4 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w ⟨i.val + 1, hi⟩ := sg.anti (by simp [Fin.le_def]; omega)
    rw [h3] at h2 ⊢
    omega
  · have h2 := he i (by omega)
    have h3 : i.succ = Fin.last n := Fin.ext (by simp; omega)
    have h4 : (⟨n - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    rw [h3, h4]
    omega

theorem hw_eq_piGen {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (h : Interlace lam sg)
    (he : EqualLast lam sg) :
    hw K le_rfl sg.natW = piGen K lam sg
      (fun i _ => Fin.castLE (Nat.succ_le_of_lt i.isLt), fun i _ => Fin.castLE i.isLt.le) := by
  let D : ℕ → MvPolynomial (Fin n × Fin n) K := fun k => if hk : k ≤ n then lpMinor K k hk hk else 1
  have hD : ∀ k (hk : k ≤ n), initMinor K (Fin.castLE hk) hk = D k := fun k hk => by
    simp only [D, dif_pos hk]; rfl
  have hD' : ∀ k (hk : k ≤ n), lpMinor K k hk hk = D k := hD
  have h0 : D 0 = 1 := by
    rw [← hD' 0 (Nat.zero_le _)]; simp [lpMinor]
  unfold piGen hw
  simp only [hD, hD', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_shift D h0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, aNum_add_bNext h he]

theorem dualWeyl_le_span_piGen (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight (n + 1))
    (sg : DomWeight n) (h : Interlace lam sg) (he : EqualLast lam sg) :
    dualWeyl K n n sg.natW ≤ Submodule.span K (Set.range (piGen K lam sg)) := by
  refine (GlobalTheory.OrbitSpan.dualWeyl_le_span_orbit K le_rfl sg.natW (Formalism.L2.Col.natW_anti sg)).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  beta_reduce
  rw [hw_eq_piGen h he]
  exact rowAct_piGen_mem lam sg _ _

end GlobalTheory.BrCompare.Surj
