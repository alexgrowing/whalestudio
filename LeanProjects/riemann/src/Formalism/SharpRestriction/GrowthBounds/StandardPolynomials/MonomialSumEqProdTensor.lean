import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreSys
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DivDerZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [instance] PreSys.finC PreSys.finM

def TCoreBody (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (n : ℕ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (Std : MonH X) : Prop :=
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (ju : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ j i, ju j i ≤ L.lv j i) →
    ∀ (Gu : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
      (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ),
      (∀ j, Gu j ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)) →
      (∀ j, Gu j ∈ Pol (KK O) X.m (du j)) → (∀ j a, du j a ≤ (L.LL j).deg a) →
      (∀ j k, Gu j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,
      (∀ l, ∑ c, (Std (l, c) - A (l, c)) ≤ X.p ^ X.G' * e) → (∀ l, ∑ c, (A (l, c) - Std (l, c)) ≤ X.p ^ X.G' * e) →
      (∀ j c, A ((topEnd X j, false), c) = Std ((topEnd X j, false), c)) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) →
      (∀ m ∈ ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1).support, ndM X m ≤ ordFam C0 CE1 CE2 X β + e) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e

section Small

theorem sum_split {κ : Type} [Fintype κ] (mult u d : κ → ℕ) (hu : ∀ a, u a ≤ mult a) :
    ∑ a, (mult a - u a) * d a + ∑ a, u a * d a = ∑ a, mult a * d a := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Nat.add_mul, Nat.sub_add_cancel (hu a)]

theorem chain_pol_one (K : Type) [CommRing K] {ι : Type} {n : ℕ} : (1 : MvPolynomial (ι × Fin n) K) ∈ Pol K n (fun _ : ι => 0) := by
  have h := Formalism.MainNotions.G.Joints.StandardMonomialSpace.hom_Pol_C K (ι := ι) (n := n) (1 : K)
  rw [C_1] at h
  exact h

theorem chain_pol_pow (K : Type) [CommRing K] {ι : Type} {n : ℕ} {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) K}
    (h : P ∈ Pol K n d) (u : ℕ) : P ^ u ∈ Pol K n (fun i => u * d i) := by
  induction u with
  | zero => simpa using chain_pol_one K (ι := ι) (n := n)
  | succ u ih =>
    rw [pow_succ]
    have := Formalism.MainNotions.G.Joints.StandardMonomialSpace.hom_Pol_mul K ih h
    have e : ((fun i => u * d i) + d) = fun i => (u + 1) * d i := by funext i; simp [Nat.succ_mul]
    rwa [e] at this

theorem chain_pol_prod (K : Type) [CommRing K] {ι κ : Type} {n : ℕ} (s : Finset κ) (d : κ → ι → ℕ)
    (P : κ → MvPolynomial (ι × Fin n) K) (h : ∀ a ∈ s, P a ∈ Pol K n (d a)) :
    ∏ a ∈ s, P a ∈ Pol K n (fun i => ∑ a ∈ s, d a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using chain_pol_one K (ι := ι) (n := n)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := Formalism.MainNotions.G.Joints.StandardMonomialSpace.hom_Pol_mul K (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    have e : (d a + fun i => ∑ a ∈ s, d a i) = fun i => ∑ b ∈ insert a s, d b i := by
      funext i; simp [Finset.sum_insert ha]
    rwa [e] at this

theorem glIntOne {O : Type} [CommRing O] [IsDomain O] {σ : Type} : (1 : MvPolynomial σ (KK O)) ∈ IntPol O σ := ⟨1, by simp⟩

theorem glIntMul {O : Type} [CommRing O] [IsDomain O] {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ)
    (hy : y ∈ IntPol O σ) : x * y ∈ IntPol O σ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

theorem glIntPow {O : Type} [CommRing O] [IsDomain O] {σ : Type} {x : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (u : ℕ) :
    x ^ u ∈ IntPol O σ := by
  induction u with
  | zero => simpa using glIntOne (O := O) (σ := σ)
  | succ u ih => rw [pow_succ]; exact glIntMul ih hx

theorem glIntProd {O : Type} [CommRing O] [IsDomain O] {σ κ : Type} (s : Finset κ) (P : κ → MvPolynomial σ (KK O))
    (h : ∀ a ∈ s, P a ∈ IntPol O σ) : ∏ a ∈ s, P a ∈ IntPol O σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using glIntOne (O := O) (σ := σ)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact glIntMul (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem monomial_sum_eq_prod_tensor {X : Loc} {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) := by
  have := mono_sum (O := O) s (fun _ => 1) a
  simpa using this

end Small

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mu : ℝ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 mu X β} {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

def PreSys.sgR (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : RHH O X :=
  (∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial P.R 1

def PreSys.sgC (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (j : Fin (numSeg X.TT)) (a : P.ιC j) : RHH O X :=
  monomial (P.pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (P.Kc j a))

def PreSys.sgH (_P : PreSys C0 CE1 CE2 X O w mu β L G Std) (j : Fin (numSeg X.TT))
    (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) : RHH O X :=
  ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i)

theorem PreSys.ident (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (nC : ∀ j, P.ιC j → ℕ)
    (nH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ) (nM : P.ιM → ℕ) (M : MonH X) :
    P.sgR * ((∏ j, ∏ a, P.sgC j a ^ nC j a) * ((∏ j, ∏ i, P.sgH j i ^ nH j i) *
        ∏ a, (monomial (P.aM a) (1 : KK O) : RHH O X) ^ nM a)) * monomial M 1 =
      (∏ j, L.head O j (nH j) (∏ a, P.Kc j a ^ nC j a)) *
        monomial (P.R + ((∑ j, ∑ a, nC j a • P.pl j a) + ∑ a, nM a • P.aM a) + M) 1 := by
  have e1 : (monomial (P.R + ((∑ j, ∑ a, nC j a • P.pl j a) + ∑ a, nM a • P.aM a) + M) (1 : KK O) : RHH O X) =
      monomial P.R 1 * ((∏ j, ∏ a, (monomial (P.pl j a) (1 : KK O) : RHH O X) ^ nC j a) *
        ∏ a, (monomial (P.aM a) (1 : KK O) : RHH O X) ^ nM a) * monomial M 1 := by
    rw [← mono_sum, ← Finset.prod_congr rfl (fun j _ => mono_sum (O := O) Finset.univ (nC j) (P.pl j)), ← monomial_sum_eq_prod_tensor]
    simp only [monomial_mul, one_mul]
  rw [e1]
  unfold PreSys.sgR PreSys.sgC PreSys.sgH LvDat.head
  simp only [map_mul, map_prod, map_pow, mul_pow, Finset.prod_mul_distrib]
  ring

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
