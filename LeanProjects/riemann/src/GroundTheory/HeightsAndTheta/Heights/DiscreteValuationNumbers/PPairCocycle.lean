import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorsCommute
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section PolyValues

variable {K : Type*} {σ τ : Type*}

def polyVal (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) : ℤ :=
  ∑ μ ∈ H.support, H.coeff μ * A (classList cls μ)

theorem polyVal_eq_sum_of_subset (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ}
    {S : Finset (σ →₀ ℕ)} (h : H.support ⊆ S) :
    polyVal A cls H = ∑ μ ∈ S, H.coeff μ * A (classList cls μ) :=
  Finset.sum_subset h fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]

theorem polyVal_add (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ) :
    polyVal A cls (H₁ + H₂) = polyVal A cls H₁ + polyVal A cls H₂ := by
  classical
  rw [polyVal_eq_sum_of_subset A cls (S := H₁.support ∪ H₂.support) support_add,
    polyVal_eq_sum_of_subset A cls (S := H₁.support ∪ H₂.support) Finset.subset_union_left,
    polyVal_eq_sum_of_subset A cls (S := H₁.support ∪ H₂.support) Finset.subset_union_right]
  simp only [coeff_add, add_mul, Finset.sum_add_distrib]

def polyValHom (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) : MvPolynomial σ ℤ →+ ℤ where
  toFun := polyVal A cls
  map_zero' := by simp [polyVal]
  map_add' := polyVal_add A cls

theorem polyVal_sub (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ) :
    polyVal A cls (H₁ - H₂) = polyVal A cls H₁ - polyVal A cls H₂ :=
  map_sub (polyValHom A cls) H₁ H₂

theorem polyVal_monomial (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (μ : σ →₀ ℕ) (c : ℤ) :
    polyVal A cls (monomial μ c) = c * A (classList cls μ) := by
  classical
  rw [polyVal_eq_sum_of_subset A cls support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

theorem polyVal_fun_sub (A₁ A₂ : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) :
    polyVal (fun l => A₁ l - A₂ l) cls H = polyVal A₁ cls H - polyVal A₂ cls H := by
  unfold polyVal
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => mul_sub _ _ _

theorem polyVal_fun_neg (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) :
    polyVal (fun l => -A l) cls H = -polyVal A cls H := by
  unfold polyVal
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => mul_neg _ _

def PermInv (A : List (K → ℤ) → ℤ) : Prop := ∀ l l' : List (K → ℤ), l.Perm l' → A l = A l'

def HeadAdd (A : List (K → ℤ) → ℤ) : Prop :=
  ∀ (u v : K → ℤ) (l : List (K → ℤ)), A ((u + v) :: l) = A (u :: l) + A (v :: l)

theorem HeadAdd.sub {A : List (K → ℤ) → ℤ} (hA : HeadAdd A) (u v : K → ℤ) (l : List (K → ℤ)) :
    A ((u - v) :: l) = A (u :: l) - A (v :: l) := by
  have h := hA (u - v) v l
  rw [sub_add_cancel] at h
  linarith

theorem classList_single_add (cls : σ → K → ℤ) (s : σ) (μ : σ →₀ ℕ) :
    (classList cls (Finsupp.single s 1 + μ)).Perm (cls s :: classList cls μ) := by
  unfold classList
  rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_toList, Multiset.coe_toList]
  simp [Finsupp.toMultiset_single]

theorem polyVal_X_mul {A : List (K → ℤ) → ℤ} (hA : PermInv A) (cls : σ → K → ℤ) (s : σ)
    (H : MvPolynomial σ ℤ) :
    polyVal A cls (X s * H) = polyVal (fun l => A (cls s :: l)) cls H := by
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [X, monomial_mul, one_mul, polyVal_monomial, polyVal_monomial,
      hA _ _ (classList_single_add cls s μ)]
  | add p q hp hq => rw [mul_add, polyVal_add, polyVal_add, hp, hq]

theorem polyVal_rename (A : List (K → ℤ) → ℤ) (cls : τ → K → ℤ) (ρ : σ → τ)
    (H : MvPolynomial σ ℤ) :
    polyVal A cls (rename ρ H) = polyVal A (cls ∘ ρ) H := by
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [rename_monomial, polyVal_monomial, polyVal_monomial]
    unfold classList
    rw [← Finsupp.toMultiset_map, Multiset.map_map]
  | add p q hp hq => rw [map_add, polyVal_add, polyVal_add, hp, hq]

end PolyValues

section Geometric

variable {R : Type*} [CommRing R]

def geoSum (k : ℕ) (p q : R) : R := ∑ j ∈ Finset.range k, p ^ j * q ^ (k - 1 - j)

def geoSum3 : ℕ → R → R → R → R
  | 0, _, _, _ => 0
  | k + 1, a, b, c => c * geoSum3 k a b c + geoSum k a b

theorem geoSum_succ (k : ℕ) (p q : R) : geoSum (k + 1) p q = p ^ k + q * geoSum k p q := by
  unfold geoSum
  rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, add_comm,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ]
  ring

theorem geoSum_mul (k : ℕ) (p q : R) : (p - q) * geoSum k p q = p ^ k - q ^ k := by
  rw [mul_comm]
  exact (Commute.all p q).geom_sum₂_mul k

theorem geoSum_sub_right (k : ℕ) (a b c : R) :
    geoSum k a c - geoSum k a b = (c - b) * geoSum3 k a b c := by
  induction k with
  | zero => simp [geoSum, geoSum3]
  | succ k ih =>
    rw [geoSum_succ, geoSum_succ, geoSum3]
    linear_combination c * ih

theorem geoSum_sub_left (k : ℕ) (a b c : R) :
    geoSum k a c - geoSum k b c = (a - b) * geoSum3 k a b c := by
  induction k with
  | zero => simp [geoSum, geoSum3]
  | succ k ih =>
    rw [geoSum_succ, geoSum_succ, geoSum3]
    linear_combination c * ih - geoSum_mul k a b

end Geometric

section Triangle

variable {K : Type*}

def geoVal (A : List (K → ℤ) → ℤ) (k : ℕ) (u v : K → ℤ) : ℤ :=
  polyVal A ![u, v] (geoSum k (X 0) (X 1) : MvPolynomial (Fin 2) ℤ)

theorem geoSum_rename {σ τ : Type*} (ρ : σ → τ) (k : ℕ) (s t : σ) :
    rename ρ (geoSum k (X s) (X t) : MvPolynomial σ ℤ) = geoSum k (X (ρ s)) (X (ρ t)) := by
  simp [geoSum, map_sum, rename_X]

theorem polyVal_geoSum_three (A : List (K → ℤ) → ℤ) (k : ℕ) (a b c : K → ℤ) (i j : Fin 3) :
    polyVal A ![a, b, c] (geoSum k (X i) (X j)) = geoVal A k (![a, b, c] i) (![a, b, c] j) := by
  have e : (geoSum k (X i) (X j) : MvPolynomial (Fin 3) ℤ) =
      rename ![i, j] (geoSum k (X 0) (X 1)) := by
    rw [geoSum_rename]; rfl
  rw [e, polyVal_rename, geoVal]
  congr 1
  funext m
  fin_cases m <;> rfl

theorem geoVal_sub_right {A : List (K → ℤ) → ℤ} (hp : PermInv A) (ha : HeadAdd A) (k : ℕ)
    (a b c : K → ℤ) :
    geoVal A k a c - geoVal A k a b =
      -polyVal (fun l => A ((b - c) :: l)) ![a, b, c] (geoSum3 k (X 0) (X 1) (X 2)) := by
  have e1 : geoVal A k a c = polyVal A ![a, b, c] (geoSum k (X 0) (X 2)) :=
    (polyVal_geoSum_three A k a b c 0 2).symm
  have e2 : geoVal A k a b = polyVal A ![a, b, c] (geoSum k (X 0) (X 1)) :=
    (polyVal_geoSum_three A k a b c 0 1).symm
  rw [e1, e2, ← polyVal_sub, geoSum_sub_right, sub_mul, polyVal_sub, polyVal_X_mul hp,
    polyVal_X_mul hp, ← polyVal_fun_sub, ← polyVal_fun_neg]
  congr 1
  funext l
  show A (c :: l) - A (b :: l) = -A ((b - c) :: l)
  rw [ha.sub]
  ring

theorem geoVal_sub_left {A : List (K → ℤ) → ℤ} (hp : PermInv A) (ha : HeadAdd A) (k : ℕ)
    (a b c : K → ℤ) :
    geoVal A k a c - geoVal A k b c =
      polyVal (fun l => A ((a - b) :: l)) ![a, b, c] (geoSum3 k (X 0) (X 1) (X 2)) := by
  have e1 : geoVal A k a c = polyVal A ![a, b, c] (geoSum k (X 0) (X 2)) :=
    (polyVal_geoSum_three A k a b c 0 2).symm
  have e2 : geoVal A k b c = polyVal A ![a, b, c] (geoSum k (X 1) (X 2)) :=
    (polyVal_geoSum_three A k a b c 1 2).symm
  rw [e1, e2, ← polyVal_sub, geoSum_sub_left, sub_mul, polyVal_sub, polyVal_X_mul hp,
    polyVal_X_mul hp, ← polyVal_fun_sub]
  congr 1
  funext l
  show A (a :: l) - A (b :: l) = A ((a - b) :: l)
  rw [ha.sub]

end Triangle

section CycleSums

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_add_cycle {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) :
    cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by
  unfold cycEval
  simp only [Pi.add_apply, add_mul]
  exact finsum_add_distrib (h₁.subset (Function.support_mul_subset_left _ _))
    (h₂.subset (Function.support_mul_subset_left _ _))

theorem cycEval_fun_sub {n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite) :
    cycEval (fun W => n₁ W - n₂ W) Z = cycEval n₁ Z - cycEval n₂ Z := by
  unfold cycEval
  simp only [mul_sub]
  exact finsum_sub_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))

theorem cycEval_fun_add {n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite) :
    cycEval (fun W => n₁ W + n₂ W) Z = cycEval n₁ Z + cycEval n₂ Z := by
  unfold cycEval
  simp only [mul_add]
  exact finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))

theorem cycEval_congr {n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (h : ∀ W, Z W ≠ 0 → n₁ W = n₂ W) :
    cycEval n₁ Z = cycEval n₂ Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW]

theorem cycEval_eq_sum_finite {n Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite) :
    cycEval n Z = ∑ W ∈ hZ.toFinset, Z W * n W := by
  unfold cycEval
  refine finsum_eq_sum_of_support_subset _ fun W hW => ?_
  rw [Set.Finite.coe_toFinset]
  exact Function.support_mul_subset_left _ _ hW

theorem cycEval_polyVal {σ : Type*} {Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (F : Ideal (MRing ι R) → List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) :
    cycEval (fun W => polyVal (F W) cls H) Z = polyVal (fun l => cycEval (fun W => F W l) Z) cls H := by
  simp only [cycEval_eq_sum_finite hZ]
  unfold polyVal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem cycEval_geoVal_cocycle {A : Ideal (MRing ι R) → List (K → ℤ) → ℤ}
    {Z Z' : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (hZ' : (Function.support Z').Finite) (hp : ∀ W, PermInv (A W))
    (ha : ∀ W, Z W ≠ 0 → HeadAdd (A W)) (ha' : ∀ W, Z' W ≠ 0 → HeadAdd (A W)) (k : ℕ)
    (a b c : K → ℤ)
    (hC : ∀ l, cycEval (fun W => A W ((b - c) :: l)) Z = cycEval (fun W => A W ((a - b) :: l)) Z') :
    cycEval (fun W => geoVal (A W) k a c) (Z + Z') =
      cycEval (fun W => geoVal (A W) k a b) Z + cycEval (fun W => geoVal (A W) k b c) Z' := by
  have e1 : cycEval (fun W => geoVal (A W) k a c) Z = cycEval (fun W => geoVal (A W) k a b -
      polyVal (fun l => A W ((b - c) :: l)) ![a, b, c] (geoSum3 k (X 0) (X 1) (X 2))) Z :=
    cycEval_congr fun W hW => by
      have := geoVal_sub_right (hp W) (ha W hW) k a b c
      linarith
  have e2 : cycEval (fun W => geoVal (A W) k a c) Z' = cycEval (fun W => geoVal (A W) k b c +
      polyVal (fun l => A W ((a - b) :: l)) ![a, b, c] (geoSum3 k (X 0) (X 1) (X 2))) Z' :=
    cycEval_congr fun W hW => by
      have := geoVal_sub_left (hp W) (ha' W hW) k a b c
      linarith
  have e3 : cycEval (fun W => polyVal (fun l => A W ((b - c) :: l)) ![a, b, c]
        (geoSum3 k (X 0) (X 1) (X 2))) Z =
      cycEval (fun W => polyVal (fun l => A W ((a - b) :: l)) ![a, b, c]
        (geoSum3 k (X 0) (X 1) (X 2))) Z' := by
    rw [cycEval_polyVal hZ (fun W l => A W ((b - c) :: l)),
      cycEval_polyVal hZ' (fun W l => A W ((a - b) :: l))]
    congr 1
    funext l
    exact hC l
  rw [cycEval_add_cycle hZ hZ', e1, e2, cycEval_fun_sub hZ, cycEval_fun_add hZ', e3]
  ring

end CycleSums

section Models

universe u

theorem divCycleFiniteSupport : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  rw [Function.mem_support] at hW
  unfold divCycle at hW
  split_ifs at hW with h
  · exact h.1
  · exact absurd rfl hW

variable {K : Type} [DecidableEq K] {ι : K → Type}

omit [DecidableEq K] in
theorem diffStep_swap (b b' : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' h) = diffStep b' (diffStep b h) := by
  funext m
  simp only [diffStep]
  rw [sub_right_comm m b b']
  ring

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNumL_eq_of_perm (W : Ideal (MRing ι O)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    vNumL W l = vNumL W l' := by
  unfold vNumL vNum intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get]
  congr 1
  exact h.foldr_eq' (fun x _ y _ z => diffStep_swap y x z) _

theorem vNumL_cons (W : Ideal (MRing ι O)) (u : K → ℤ) (l : List (K → ℤ)) :
    vNumL W (u :: l) = vNum W (Matrix.vecCons u l.get) := by
  unfold vNumL vNum intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.ofFn_get]

def listNum (W : Ideal (MRing ι O)) (Q : List (K → ℤ)) (d : ℕ) (l : List (K → ℤ)) : ℤ :=
  if l.length + Q.length = d then vNumL W (l ++ Q) else 0

theorem listNum_perm (W : Ideal (MRing ι O)) (Q : List (K → ℤ)) (d : ℕ) :
    PermInv (listNum W Q d) := by
  intro l l' h
  unfold listNum
  rw [h.length_eq, vNumL_eq_of_perm W (h.append_right Q)]

variable [Fintype K] [∀ k, Fintype (ι k)]

theorem vNumL_add_head (h3 : IntNumAddFirst.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)} (hW : ratDiv P f g W ≠ 0)
    (u v : K → ℤ) (l : List (K → ℤ)) (hl : l.length + 1 = d) :
    vNumL W ((u + v) :: l) = vNumL W (u :: l) + vNumL W (v :: l) := by
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes := by
    intro h e he hW'
    unfold divCycle at hW'
    split_ifs at hW' with hW''
    · exact ⟨MinimalPrimeMultiHomog.proof O K ι _ W
        (SupSpanMultiHomog.proof O K ι P h e hPmh he) hW''.1, hW''.1⟩
    · exact absurd rfl hW'
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
  have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    by_cases hWf : divCycle P f W = 0
    · have hWg : divCycle P g W ≠ 0 := by
        intro hWg; apply hW; simp [ratDiv, hWf, hWg]
      obtain ⟨hm, hmin⟩ := hmh g bg hbg hWg
      exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    · obtain ⟨hm, hmin⟩ := hmh f bf hbf hWf
      exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
  obtain ⟨hWm, hWp, hPW⟩ := hWdata
  have := hWp
  have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
  have hdrop := DimStrictDrop.proof (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]
    have e : d + 1 + Fintype.card K = l.length + 2 + Fintype.card K := by omega
    rw [e] at hdrop
    exact lt_natCast_of_add_one_le hdrop
  have key := h3 (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W)
    (SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.proof O K ι W hWm)
    hdim u v l.get
  rw [vNumL_cons, vNumL_cons, vNumL_cons]
  exact key

theorem listNum_headAdd (h3 : IntNumAddFirst.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)} (hW : ratDiv P f g W ≠ 0)
    (Q : List (K → ℤ)) : HeadAdd (listNum W Q d) := by
  intro u v l
  unfold listNum
  simp only [List.length_cons, List.cons_append]
  split_ifs with h
  · exact vNumL_add_head h3 hϖ hP hD hW u v (l ++ Q) (by simp only [List.length_append]; omega)
  · simp

theorem listNum_commute (hC2 : VerticalDivisorsCommute.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g')
    (Q l : List (K → ℤ)) :
    cycEval (fun W => listNum W Q d (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => listNum W Q d (b :: l)) (ratDiv P f' g') := by
  unfold listNum
  simp only [List.length_cons, List.cons_append]
  by_cases h : l.length + 1 + Q.length = d
  · simp only [if_pos h]
    obtain rfl : d = (l ++ Q).length + 1 := by simp only [List.length_append]; omega
    simp only [vNumL_cons]
    exact hC2 O ϖ hϖ K ι P (l ++ Q).length hP b b' f g f' g' hD hD' (l ++ Q).get
  · simp [if_neg h, cycEval]

omit [DecidableEq K] in

theorem ratDiv_mul {P : Ideal (MRing ι O)} [P.IsPrime] {f g f' g' : MRing ι O} (hf : f ∉ P)
    (hg : g ∉ P) (hf' : f' ∉ P) (hg' : g' ∉ P) :
    ratDiv P (f * f') (g * g') = ratDiv P f g + ratDiv P f' g' := by
  funext W
  simp only [ratDiv, Pi.add_apply]
  rw [DivCycleMul.proof O K ι P f f' ‹_› hf hf', DivCycleMul.proof O K ι P g g' ‹_› hg hg']
  simp only [Pi.add_apply]
  ring

theorem isVerticalDivisor_mul {P : Ideal (MRing ι O)} [P.IsPrime] {ϖ : O} {b b' : K → ℤ}
    {f g f' g' : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    (hD' : IsVerticalDivisor P ϖ b' f' g') :
    IsVerticalDivisor P ϖ (b + b') (f * f') (g * g') where
  degrees := by
    obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    obtain ⟨bf', bg', hf', hg', hb'⟩ := hD'.degrees
    refine ⟨bf + bf', bg + bg', IsWeightedHomogeneous.mul hf hf',
      IsWeightedHomogeneous.mul hg hg', ?_⟩
    rw [← hb, ← hb']
    funext k
    simp only [Pi.add_apply, Nat.cast_add]
    ring
  num_not_mem := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hD.num_not_mem hD'.num_not_mem
  den_not_mem := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hD.den_not_mem hD'.den_not_mem
  vertical := by
    intro W hW
    rw [ratDiv_mul hD.num_not_mem hD.den_not_mem hD'.num_not_mem hD'.den_not_mem,
      Pi.add_apply] at hW
    by_cases h1 : ratDiv P f g W = 0
    · rw [h1, zero_add] at hW
      exact hD'.vertical W hW
    · exact hD.vertical W h1
  unit_off_special := by
    intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    obtain ⟨u', v', hu', hv', h'⟩ := hD'.unit_off_special W hW hPW hrel hϖ
    refine ⟨u * u', v * v', fun hm => (hW.mem_or_mem hm).elim hu hu',
      fun hm => (hW.mem_or_mem hm).elim hv hv', ?_⟩
    have e : u * u' * (f * f') - v * v' * (g * g') =
        (u' * f') * (u * f - v * g) + (v * g) * (u' * f' - v' * g') := by ring
    rw [e]
    exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ h')

end Models

section Flags

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O] in
theorem sameGenericFibre_trans {τ : Type*} {x : τ → Ω} {ϖ : O} {B B' B'' : ChartBundle O x N E}
    (h₁ : SameGenericFibre ϖ B B') (h₂ : SameGenericFibre ϖ B' B'') : SameGenericFibre ϖ B B'' := by
  intro c hc
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨n, hn⟩ := (h₁ c hc).1 v hv
    obtain ⟨m, hm⟩ := (h₂ c hc).1 _ hn
    exact ⟨m + n, by rw [pow_add, mul_smul]; exact hm⟩
  · obtain ⟨n, hn⟩ := (h₂ c hc).2 v hv
    obtain ⟨m, hm⟩ := (h₁ c hc).2 _ hn
    exact ⟨m + n, by rw [pow_add, mul_smul]; exact hm⟩

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O] in
theorem sameGenericFibre_symm {τ : Type*} {x : τ → Ω} {ϖ : O} {B B' : ChartBundle O x N E}
    (h : SameGenericFibre ϖ B B') : SameGenericFibre ϖ B' B :=
  fun c hc => (h c hc).symm

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra O Ω] in

theorem repr_chain (w w' : Module.Basis (Fin N) Ω E) (v : E) (j : Fin N) :
    w.repr v j = ∑ m, w'.repr v m * w.repr (w' m) j := by
  have e := congrArg (fun z => w.repr z j) (w'.sum_repr v)
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at e
  exact e.symm

theorem isFlagPair_comp {ϖ : O} {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime]
    {B B' B'' : ChartBundle O (segreVec y) N E} {w w' w'' : Module.Basis (Fin N) Ω E}
    {x x' x'' : Fin N → K → ℤ} {f g f' g' : Fin N → MRing ι O}
    (hp₁ : IsFlagPair ϖ y B B' w w' x x' f g) (hp₂ : IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g') :
    IsFlagPair ϖ y B B'' w w'' x x'' (fun i => f i * f' i) (fun i => g i * g' i) where
  flag := hp₁.flag
  flag' := hp₂.flag'
  sameFlag := by
    intro i j hij
    rw [repr_chain w w' (w'' i) j]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge i m with h | h
    · rw [hp₂.sameFlag i m h, zero_mul]
    · rw [hp₁.sameFlag m j (lt_of_le_of_lt h hij), mul_zero]
  vertical := fun i => by
    have h := isVerticalDivisor_mul (hp₁.vertical i) (hp₂.vertical i)
    rwa [sub_add_sub_cancel] at h
  generic := fun i => by
    simp only [map_mul]
    rw [hp₁.generic i, hp₂.generic i, repr_chain w w' (w'' i) i, Finset.sum_eq_single i]
    · ring
    · intro m _ hmi
      rcases lt_or_gt_of_ne hmi with h | h
      · rw [hp₁.sameFlag m i h, mul_zero]
      · rw [hp₂.sameFlag i m h, zero_mul]
    · simp

omit [∀ k, Fintype (ι k)] in

theorem isFlagPair_refl {ϖ : O} {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (hf : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) where
  flag := hf
  flag' := hf
  sameFlag := by
    intro i j hij
    simp [Module.Basis.repr_self, hij.ne]
  vertical := fun i => by
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  generic := fun i => by simp [Module.Basis.repr_self]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem pairNum_one (P : Ideal (MRing ι O)) (x : Fin N → K → ℤ)
    (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ) (Q : List (K → ℤ)) :
    pairNum P x x (fun _ => 1) (fun _ => 1) Gs Q = 0 := by
  simp [pairNum, cycEval, ratDiv, divCycle_one]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem classNum_eq_polyVal {σ : Type*} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {Q : List (K → ℤ)} {d : ℕ} (hn : n + Q.length = d)
    (W : Ideal (MRing ι O)) : classNum cls H Q W = polyVal (listNum W Q d) cls H := by
  unfold classNum polyVal listNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [if_pos]
  have h1 := hH (mem_support_iff.mp hμ)
  rw [← hn, ← h1]
  congr 1
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply]
  simp [Finsupp.sum]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem classNum_psumExpansion (u v : Fin N → K → ℤ) (k : ℕ) (i : Fin N) {Q : List (K → ℤ)}
    {d : ℕ} (hQ : Q.length + k = d + 1) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim u v) (psumExpansion N k i) Q W = geoVal (listNum W Q d) k (u i) (v i) := by
  cases k with
  | zero => simp [classNum, psumExpansion, geoVal, geoSum, polyVal]
  | succ m =>
    have e : psumExpansion N (m + 1) i =
        rename ![Sum.inl i, Sum.inr i] (geoSum (m + 1) (X 0) (X 1)) := by
      rw [geoSum_rename]; rfl
    have hc : (Sum.elim u v ∘ ![Sum.inl i, Sum.inr i]) = ![u i, v i] := by
      funext j
      fin_cases j <;> rfl
    rw [classNum_eq_polyVal (Q := Q) (d := d) _ (isHomogeneous_psumExpansion N (m + 1) i)
      (by omega), e, polyVal_rename, hc, geoVal]

end Flags

theorem pairNum_cocycle (hFI : FlagIndependence.Statement)
    (hC2 : VerticalDivisorsCommute.Statement.{0}) (h3 : IntNumAddFirst.Statement.{0})
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ} (hP : IsModelOver (pointIdeal O y) d)
    {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {B B' B'' : ChartBundle O (segreVec y) N E}
    (hS : SameGenericFibre ϖ B B') (hS' : SameGenericFibre ϖ B' B'')
    {w w' w'' : Module.Basis (Fin N) Ω E} {x x' x'' : Fin N → K → ℤ}
    {f g f' g' f'' g'' : Fin N → MRing ι O}
    (hp₁ : IsFlagPair ϖ y B B' w w' x x' f g) (hp₂ : IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g')
    (hp₃ : IsFlagPair ϖ y B B'' w w'' x x'' f'' g'')
    {k : ℕ} {Gs Gs' Gs'' : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ}
    (hG : IsPairExpansion k (psum (Fin N) ℤ k) Gs) (hG' : IsPairExpansion k (psum (Fin N) ℤ k) Gs')
    (hG'' : IsPairExpansion k (psum (Fin N) ℤ k) Gs'')
    {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum (pointIdeal O y) x x'' f'' g'' Gs'' Q =
      pairNum (pointIdeal O y) x x' f g Gs Q + pairNum (pointIdeal O y) x' x'' f' g' Gs' Q := by
  have : (pointIdeal O y).IsPrime := hP.multiProj.isPrime
  have hpm := isFlagPair_comp hp₁ hp₂
  have hS'' := sameGenericFibre_trans hS hS'
  have ek := isPairExpansion_psum N k
  have hsym := psum_isSymmetric (Fin N) ℤ k
  have hhom := isHomogeneous_psum N k
  rw [hFI O ϖ hϖ Ω K ι y d hP N E B B'' hS'' w w'' w w'' x x'' x x'' f'' g'' _ _ hp₃ hpm k _
      hhom hsym Gs'' _ hG'' ek Q hQ,
    hFI O ϖ hϖ Ω K ι y d hP N E B B' hS w w' w w' x x' x x' f g f g hp₁ hp₁ k _ hhom hsym Gs _
      hG ek Q hQ,
    hFI O ϖ hϖ Ω K ι y d hP N E B' B'' hS' w' w'' w' w'' x' x'' x' x'' f' g' f' g' hp₂ hp₂ k _
      hhom hsym Gs' _ hG' ek Q hQ]
  unfold pairNum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  beta_reduce
  rw [ratDiv_mul (hp₁.vertical i).num_not_mem (hp₁.vertical i).den_not_mem
    (hp₂.vertical i).num_not_mem (hp₂.vertical i).den_not_mem]
  simp only [classNum_psumExpansion _ _ k i hQ]
  exact cycEval_geoVal_cocycle
    (ratDiv_support_finite divCycleFiniteSupport.{0} _ _ _)
    (ratDiv_support_finite divCycleFiniteSupport.{0} _ _ _)
    (fun W => listNum_perm W Q d)
    (fun W hW => listNum_headAdd h3 hϖ hP (hp₁.vertical i) hW Q)
    (fun W hW => listNum_headAdd h3 hϖ hP (hp₂.vertical i) hW Q) k (x i) (x' i) (x'' i)
    (fun l => listNum_commute hC2 hϖ hP (hp₁.vertical i) (hp₂.vertical i) Q l)

theorem PairCocycle.proof (hFI : FlagIndependence.Statement)
    (hC2 : VerticalDivisorsCommute.Statement.{0}) (h3 : IntNumAddFirst.Statement.{0}) :
    PairCocycle.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hP N E _ _ B B' B'' hS hS' w w' w'' x x' x'' f g f' g'
    f'' g'' hp₁ hp₂ hp₃ k Gs Gs' Gs'' hG hG' hG'' Q hQ
  refine ⟨pairNum_cocycle hFI hC2 h3 hϖ hP hS hS' hp₁ hp₂ hp₃ hG hG' hG'' hQ,
    fun fr gr Gr hpr hGr => ?_⟩
  have : (pointIdeal O y).IsPrime := hP.multiProj.isPrime
  have h := pairNum_cocycle hFI hC2 h3 hϖ hP hS (sameGenericFibre_symm hS) hp₁ hpr
    (isFlagPair_refl hp₁.flag) hG hGr (isPairExpansion_psum N k) hQ
  rw [pairNum_one] at h
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
