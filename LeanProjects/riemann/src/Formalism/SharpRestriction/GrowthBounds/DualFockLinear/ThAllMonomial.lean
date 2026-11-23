import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DgFalseDiag

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv)

abbrev Aset (k d : ℕ) := {α : Fin k →₀ ℕ // ∑ c, α c = d}

instance Aset_finite (k d : ℕ) : Finite (Aset k d) := by
  have : ({α : Fin k →₀ ℕ | ∑ c, α c = d}).Finite := by
    refine (Finset.finite_toSet (Finset.univ.finsuppAntidiag d)).subset ?_
    intro α hα
    simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    exact ⟨hα, Finset.subset_univ _⟩
  exact this.to_subtype

theorem XsFinP (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : (Xs m top vec ν).Finite :=
  (sSIdxFinite (m + 1) (m + 1) ν).subset fun _ he => he.1

instance XsFinP' (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Finite (Xs m top vec ν) :=
  (XsFinP m top vec ν).to_subtype

def glue {n' k : ℕ} {d : Fin n' → ℕ} (a : ∀ s, Aset k (d s)) : Fin n' × Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (a v.1).1 v.2

theorem glue_apply {n' k : ℕ} {d : Fin n' → ℕ} (a : ∀ s, Aset k (d s)) (s : Fin n') (c : Fin k) :
    glue a (s, c) = (a s).1 c := rfl

theorem expand {R : Type} [CommRing R] {n' k : ℕ} {d : Fin n' → ℕ} [Fintype (∀ s, Aset k (d s))]
    (Q : MvPolynomial (Fin n' × Fin k) R) (hQ : IsMultiHom d Q) :
    Q = ∑ a : (∀ s, Aset k (d s)), monomial (glue a) (coeff (glue a) Q) := by
  classical
  ext e
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases he : e ∈ Q.support
  · let a : ∀ s, Aset k (d s) := fun s =>
      ⟨Finsupp.equivFunOnFinite.symm fun c => e (s, c), by simpa using hQ e he s⟩
    have ha : glue a = e := by
      ext v
      rfl
    rw [Finset.sum_eq_single a]
    · rw [if_pos ha, ha]
    · intro a' _ hne
      rw [if_neg]
      intro h
      apply hne
      funext s
      apply Subtype.ext
      ext c
      have := DFunLike.congr_fun (h.trans ha.symm) (s, c)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : coeff e Q = 0 := by simpa using he
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [h, h0]
    · rfl

theorem thAll_monomial (F : Type) [CommRing F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ)
    (a : ∀ s, Aset (m + 1) (d s)) (r : F) :
    thAll F n' m vec (monomial (glue a) r) = r • ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
  unfold thAll
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Algebra.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_pow]
  rfl

section Core

variable (F : Type) [Field F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ) {X : Fin n' → Type}
  (b : ∀ s, X s → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F)

def famG (z : (∀ s, Aset (m + 1) (d s)) × (∀ s, X s)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) F :=
  ∏ s, blockEmb F s ((∏ c, Nv F m (vec s) c ^ ((z.1 s).1 c)) * b s (z.2 s))

def fam1 (s : Fin n') (y : Aset (m + 1) (d s) × X s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F :=
  (∏ c, Nv F m (vec s) c ^ (y.1.1 c)) * b s y.2

def pairUp {n' : ℕ} {A X : Fin n' → Type} (z : (∀ s, A s) × (∀ s, X s)) : ∀ s, A s × X s := fun s => (z.1 s, z.2 s)

theorem pairUp_inj {n' : ℕ} {A X : Fin n' → Type} : Function.Injective (pairUp (A := A) (X := X)) := by
  intro z z' h
  refine Prod.ext ?_ ?_
  · funext s
    exact congrArg Prod.fst (congrFun h s)
  · funext s
    exact congrArg Prod.snd (congrFun h s)

theorem famG_li (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s)) :
    LinearIndependent F (famG F n' m vec d b) := by
  have hli : LinearIndependent F (fun i : (∀ s, Aset (m + 1) (d s) × X s) =>
      ∏ s, blockEmb F s (fam1 F n' m vec d b s (i s))) :=
    ldtensor_prod_linInd_field F (fam1 F n' m vec d b) hpos
  have h2 := hli.comp (pairUp (A := fun s => Aset (m + 1) (d s)) (X := X)) pairUp_inj
  exact h2

theorem famG_sum [Fintype (∀ s, Aset (m + 1) (d s))] (Q : MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : IsMultiHom d Q)
    (i : ∀ s, X s) :
    (∑ a : (∀ s, Aset (m + 1) (d s)), coeff (glue a) Q • famG F n' m vec d b (a, i)) =
      thAll F n' m vec Q * ∏ s, blockEmb F s (b s (i s)) := by
  have e := expand Q hQ
  have e2 : thAll F n' m vec Q =
      ∑ a : (∀ s, Aset (m + 1) (d s)), coeff (glue a) Q •
        ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
    conv_lhs => rw [e]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => thAll_monomial F n' m vec d a _
  rw [e2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  unfold famG
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul]

theorem big_core [∀ s, Finite (X s)] (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s))
    (J : Finset (∀ s, X s)) (Q : (∀ s, X s) → MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : ∀ i, IsMultiHom d (Q i))
    (hsum : ∑ i ∈ J, thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) = 0) : ∀ i ∈ J, Q i = 0 := by
  classical
  have : Fintype (∀ s, Aset (m + 1) (d s)) := Fintype.ofFinite _
  have : Fintype (∀ s, X s) := Fintype.ofFinite _
  have hli2 := famG_li F n' m vec d b hpos
  rw [Fintype.linearIndependent_iff] at hli2
  have key := hli2 (fun z => if z.2 ∈ J then coeff (glue z.1) (Q z.2) else 0) ?_
  · intro i hi
    rw [expand (Q i) (hQ i)]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h1 := key (a, i)
    simp only [hi, if_true] at h1
    rw [h1, monomial_zero]
  · rw [Fintype.sum_prod_type_right, ← hsum]
    have h1 : ∀ i : (∀ s, X s),
        (∑ a : (∀ s, Aset (m + 1) (d s)), (if i ∈ J then coeff (glue a) (Q i) else 0) • famG F n' m vec d b (a, i)) =
        if i ∈ J then thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) else 0 := by
      intro i
      by_cases hi : i ∈ J
      · simp only [hi, if_true]
        exact famG_sum F n' m vec d b (Q i) (hQ i) i
      · simp only [hi, if_false, zero_smul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_ite_mem, Finset.univ_inter]

end Core

theorem bigInd : BigInd := by
  intro F _ n' m hm top vec d ν htop hν b hb J Q hQ hsum
  exact big_core F n' m vec d b
    (fun s => posInd F m hm (top s) (vec s) (d s) (ν s) (htop s) (hν s) (b s) (hb s)) J Q hQ hsum

end Formalism.MainNotions.TestSideCounting
