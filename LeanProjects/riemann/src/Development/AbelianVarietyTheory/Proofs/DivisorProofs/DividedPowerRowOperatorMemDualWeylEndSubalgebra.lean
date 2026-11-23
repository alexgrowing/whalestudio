import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowDivMem
variable {O : Type} [CommRing O] {N : ℕ}

def wZ (N : ℕ) : Fin N × Fin N → (Fin N → ℤ) := fun v => Pi.single v.1 1

def δ (a b : Fin N) : Fin N → ℤ := Pi.single a 1 - Pi.single b 1

def PSh (a b : Fin N) (u : Fin N → ℤ) (P : Polynomial (MvPolynomial (Fin N × Fin N) O)) : Prop :=
  ∀ j : ℕ, IsWeightedHomogeneous (wZ N) (P.coeff j) (u + (j : ℤ) • δ a b)

theorem PSh.mul {a b : Fin N} {u u' : Fin N → ℤ} {P Q : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (hQ : PSh a b u' Q) : PSh a b (u + u') (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have h := (hP x.1).mul (hQ x.2)
  have hx' : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  convert h using 1
  rw [← hx']; push_cast; rw [add_smul]; abel

theorem PSh.one (a b : Fin N) : PSh (O := O) a b 0 1 := by
  intro j
  rcases j with _ | j
  · simpa using isWeightedHomogeneous_one O (wZ N)
  · rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero j)]
    exact isWeightedHomogeneous_zero _ _ _

theorem PSh.pow {a b : Fin N} {u : Fin N → ℤ} {P : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (n : ℕ) : PSh a b (n • u) (P ^ n) := by
  induction n with
  | zero => simpa using PSh.one (O := O) a b
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem PSh.prod {a b : Fin N} {ι : Type} (s : Finset ι) (u : ι → Fin N → ℤ)
    (P : ι → Polynomial (MvPolynomial (Fin N × Fin N) O)) (h : ∀ i ∈ s, PSh a b (u i) (P i)) :
    PSh a b (∑ i ∈ s, u i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSh.one (O := O) a b
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem PSh_rowGen_X (a b : Fin N) (hab : a ≠ b) (v : Fin N × Fin N) :
    PSh a b (wZ N v) (rowGen O a b (X v)) := by
  intro j
  simp only [rowGen, aeval_X]
  rcases j with _ | _ | j
  · by_cases hv : v.1 = b
    · simp [hv]; exact isWeightedHomogeneous_X O (wZ N) v
    · simp [hv]; exact isWeightedHomogeneous_X O (wZ N) v
  · by_cases hv : v.1 = b
    · simp [hv]
      convert isWeightedHomogeneous_X O (wZ N) (a, v.2) using 1
      simp [wZ, δ, hv]
    · simp [hv]; exact isWeightedHomogeneous_zero _ _ _
  · by_cases hv : v.1 = b
    · simp [hv, Polynomial.coeff_X, Polynomial.coeff_C]
      exact isWeightedHomogeneous_zero _ _ _
    · simp [hv, Polynomial.coeff_C]; exact isWeightedHomogeneous_zero _ _ _

theorem PSh.add {a b : Fin N} {u : Fin N → ℤ} {P Q : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (hQ : PSh a b u Q) : PSh a b u (P + Q) := fun j => by
  rw [Polynomial.coeff_add]; exact (hP j).add (hQ j)

theorem PSh.zero (a b : Fin N) (u : Fin N → ℤ) : PSh (O := O) a b u 0 := fun j => by
  rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero _ _ _

theorem PSh_rowGen_C (a b : Fin N) (r : O) : PSh a b 0 (rowGen O a b (C r)) := by
  intro j
  rw [show (C r : MvPolynomial (Fin N × Fin N) O) = algebraMap O _ r from rfl, AlgHom.commutes,
    Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp only [Nat.cast_zero, zero_smul, add_zero]
    exact isWeightedHomogeneous_C (wZ N) r
  · exact isWeightedHomogeneous_zero _ _ _

theorem PSh_rowGen (a b : Fin N) (hab : a ≠ b) (u : Fin N → ℤ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (wZ N) f u) : PSh a b u (rowGen O a b f) := by
  classical
  rw [f.as_sum, map_sum]
  have key : ∀ d ∈ f.support, PSh a b u (rowGen O a b (monomial d (coeff d f))) := by
    intro d hd
    have hw : Finsupp.weight (wZ N) d = u := hf (mem_support_iff.mp hd)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have h1 := (PSh_rowGen_C a b (coeff d f)).mul
      (PSh.prod d.support (fun v => d v • wZ N v) (fun v => rowGen O a b (X v ^ d v)) fun v _ => by
        rw [map_pow]; exact (PSh_rowGen_X a b hab v).pow (d v))
    rw [zero_add] at h1
    convert h1 using 1
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_induction _ (PSh a b u) (fun _ _ => PSh.add) (PSh.zero a b u) key

theorem weight_wZ (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (wZ N) d c = (Finsupp.weight (rowW N N) d c : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wZ, rowW, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

def shiftW (a b : Fin N) (k : ℕ) (w : Fin N → ℕ) : Fin N → ℕ :=
  fun c => w c + (if c = a then k else 0) - (if c = b then k else 0)

theorem rowDiv_isWH (a b : Fin N) (hab : a ≠ b) (j : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    IsWeightedHomogeneous (wZ N) (rowDiv O a b j f) ((fun c => (w c : ℤ)) + (j : ℤ) • δ a b) := by
  have hf' : IsWeightedHomogeneous (wZ N) f (fun c => (w c : ℤ)) := by
    intro d hd
    funext c
    rw [weight_wZ, hf hd]
  exact PSh_rowGen a b hab _ f hf' j

theorem proj_rowDiv (a b : Fin N) (hab : a ≠ b) (j k : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    weightedHomogeneousComponent (rowW N N) (shiftW a b k w) (rowDiv O a b j f) =
      if j = k then rowDiv O a b k f else 0 := by
  classical
  have hg := rowDiv_isWH a b hab j w f hf
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h1 h2 h2
  · subst h2; rfl
  · by_contra hne
    have := congrFun (hg hne) a
    rw [weight_wZ, h1] at this
    simp [shiftW, δ, hab, Pi.single_apply] at this
    omega
  · subst h2
    by_contra hne
    apply h1
    funext c
    have := congrFun (hg (Ne.symm hne)) c
    rw [weight_wZ] at this
    simp only [shiftW, δ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul] at this ⊢
    split_ifs at this ⊢ <;> omega
  · simp

theorem rowAct_transvection (a b : Fin N) (h : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (Matrix.transvection b a (1 : O)) h = Polynomial.eval 1 (rowGen O a b h) := by
  classical
  have key : (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b (n := N)).toRingHom =
      (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rowGen, rowAct]
    · intro v
      simp [rowGen, rowAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul]
      by_cases hv : v.1 = b
      · subst hv; simp
      · simp [hv, Ne.symm hv]
  exact (RingHom.congr_fun key h).symm

theorem proj_rowAct (a b : Fin N) (hab : a ≠ b) (k : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    weightedHomogeneousComponent (rowW N N) (shiftW a b k w) (rowAct O (Matrix.transvection b a (1 : O)) f) =
      rowDiv O a b k f := by
  classical
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one, map_sum]
  have : ∀ j, (rowGen O a b f).coeff j = rowDiv O a b j f := fun j => rfl
  simp only [this, proj_rowDiv a b hab _ k w f hf, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hk
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem rowW_le_total (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← Finset.mul_sum]
  simp [Pi.single_apply]
  split_ifs <;> simp

def box (ν : Fin N → ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ : Fin N => Finset.range (∑ s, ν s + 1)

theorem decomp (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    f = ∑ w ∈ box ν, weightedHomogeneousComponent (rowW N N) w f := by
  classical
  have hcol : IsWeightedHomogeneous (colW N N) f ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hf).1
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, Finset.sum_ite_eq, ]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hw := hcol hne
    simp only [box, Fintype.mem_piFinset, Finset.mem_range]
    intro c
    have := rowW_le_total d c
    rw [hw] at this
    omega

end GlobalTheory.RowDivMem

namespace GlobalTheory.GenCoef
open GlobalTheory.RowDivMem

theorem rowDiv_mem_dwAlg : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ,
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := by
  intro O _ N ν a b hab k
  classical
  let g : GL (Fin N) O :=
    ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
      by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
      by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
  have hg : ((g⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O) = Matrix.transvection b a 1 := rfl
  refine ⟨∑ w ∈ box ν, GlobalTheory.ExpFrame.rowProj O N ν (shiftW a b k w) * Formalism.UG.dualWeylRep O N N ν g *
      GlobalTheory.ExpFrame.rowProj O N ν w, ?_, fun f => ?_⟩
  · refine Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · rw [LinearMap.sum_apply, Submodule.coe_sum]
    conv_rhs => rw [decomp ν (f : MvPolynomial (Fin N × Fin N) O) f.2]
    have hlin : ∀ (s : Finset (Fin N → ℕ)) (F : (Fin N → ℕ) → MvPolynomial (Fin N × Fin N) O),
        rowDiv O a b k (∑ w ∈ s, F w) = ∑ w ∈ s, rowDiv O a b k (F w) := by
      intro s F
      simp only [rowDiv, map_sum, Polynomial.finset_sum_coeff]
    rw [hlin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Module.End.mul_apply]
    change weightedHomogeneousComponent (rowW N N) (shiftW a b k w)
      (Formalism.UG.dwAct O N N g (weightedHomogeneousComponent (rowW N N) w (f : MvPolynomial (Fin N × Fin N) O))) = _
    rw [Formalism.UG.dwAct, hg]
    exact proj_rowAct a b hab k w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.GenCoef
