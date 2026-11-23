import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TrivBundleIsTwistedForms
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FlagTypings

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

section Points

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]

def coords (pt : MRingOver R ι →ₐ[R] Ω) : (Σ k, ι k) → Ω := fun p => pt (X p)

theorem pointConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {s : MRingOver R ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) :
    NumbersDVR.pointConeMap R y s = C (aeval y s) * ∏ k, X k ^ a k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [NumbersDVR.pointConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  have hB : ∏ x : (Σ k, ι k), (X x.1 : MvPolynomial K Ω) ^ m x = ∏ k, X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i : ι k, (X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [hB, MvPolynomial.algebraMap_apply]

end Points

section Lines

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]

end Lines

section Flags

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

def scaleBasis (u : Module.Basis (Fin N) Ω E) {ω : Fin N → Ω} (hω : ∀ l, ω l ≠ 0) :
    Module.Basis (Fin N) Ω E :=
  u.unitsSMul fun l => Units.mk0 (ω l) (hω l)

end Flags

section Twisted

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Twisted

section Generic

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Generic

section Degrees

variable {K : Type*} [Fintype K]

end Degrees

section Triangular

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem triangular_flip (w w' : Module.Basis (Fin N) Ω E)
    (h : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) :
    (∀ i j : Fin N, i < j → w'.repr (w i) j = 0) ∧ ∀ i, w.repr (w' i) i ≠ 0 := by
  have hA : (w.toMatrix w').BlockTriangular id := fun i j hji => by
    rw [Module.Basis.toMatrix_apply]
    exact h j i hji
  have : Invertible (w.toMatrix w') := w.invertibleToMatrix w'
  have hinv : (w.toMatrix w')⁻¹ = w'.toMatrix w :=
    Matrix.inv_eq_right_inv (w.toMatrix_mul_toMatrix_flip w')
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hB := Matrix.blockTriangular_inv_of_blockTriangular hA
    rw [hinv] at hB
    have := @hB j i hij
    rwa [Module.Basis.toMatrix_apply] at this
  · have hdet : (w.toMatrix w').det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (w.toMatrix_mul_toMatrix_flip w')).ne_zero
    rw [Matrix.det_of_isUpperTriangular hA] at hdet
    have := Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
    rwa [Module.Basis.toMatrix_apply] at this

end Triangular

section MultiHomog

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

theorem weight_blockWeight (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) d k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem isMultiHomog_iff (f : MRingOver R ι) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ IsMultiHomog f a := by
  constructor
  · intro h d hd k
    rw [← weight_blockWeight]
    exact congrFun (h (mem_support_iff.mp hd)) k
  · intro h d hd
    funext k
    rw [weight_blockWeight]
    exact h d (mem_support_iff.mpr hd) k

end MultiHomog

section FlagPairs

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end FlagPairs

section Numbers

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    NumbersDVR.diffStep a (NumbersDVR.diffStep b h) =
      NumbersDVR.diffStep b (NumbersDVR.diffStep a h) := by
  funext m
  simp only [NumbersDVR.diffStep]
  rw [sub_right_comm m a b]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem intNumL_perm (F : Type*) [Field F] (V : Ideal (MRingOver F ι)) {L₁ L₂ : List (K → ℤ)}
    (h : L₁.Perm L₂) : NumbersDVR.intNumL F V L₁ = NumbersDVR.intNumL F V L₂ := by
  have : LeftCommutative (NumbersDVR.diffStep (K := K)) := ⟨diffStep_comm⟩
  simp only [NumbersDVR.intNumL, NumbersDVR.intNum, NumbersDVR.mixedDiff, List.ofFn_get]
  rw [h.foldr_eq]

theorem coe_monoList {N : ℕ} (μ : Fin N →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.monoList μ : List (Fin N)) : Multiset (Fin N)) = Finsupp.toMultiset μ := by
  ext a
  rw [Multiset.coe_count, Finsupp.count_toMultiset]
  simp only [IndefiniteRowSideFullHecke.NumbersDVR.monoList, List.count_flatMap]
  rw [← Fin.sum_univ_def]
  simp [List.count_replicate]

theorem monoList_perm {N : ℕ} (cls : Fin N → K → ℤ) (μ : Fin N →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).map cls).Perm (NumbersDVR.classList cls μ) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, coe_monoList, NumbersDVR.classList,
    Multiset.coe_toList]

omit [Fintype K] [DecidableEq K] in
theorem length_monoList {N : ℕ} {Q : MvPolynomial (Fin N) ℤ} {d : ℕ} (hQ : Q.IsHomogeneous d)
    {μ : Fin N →₀ ℕ} (hμ : μ ∈ Q.support) : (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length = d := by
  have h1 : (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length = Multiset.card (Finsupp.toMultiset μ) := by
    rw [← coe_monoList, Multiset.coe_card]
  have h2 := hQ (mem_support_iff.mp hμ)
  rw [h1, Finsupp.card_toMultiset, ← h2, Finsupp.weight_apply]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rfl

end Numbers

section Divisors

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem divCycle_eq {R : Type*} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRingOver R ι))
    (f : MRingOver R ι) (W : Ideal (MRingOver R ι)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W : ℤ) := by
  classical
  have hL : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W : ℕ) =
      if W ∈ divSupp P f then multAt (P ⊔ Ideal.span {f}) W else 0 := rfl
  rw [NumbersDVR.divCycle, hL]
  by_cases h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ NumbersDVR.IsRelevant W
  · have h' : W ∈ divSupp P f := h
    rw [dif_pos h, if_pos h', multAt, dif_pos h.1.1.1]
    rfl
  · have h' : W ∉ divSupp P f := h
    rw [dif_neg h, if_neg h']
    simp

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem cycEval_finsupp {R : Type*} [CommRing R] (n : Ideal (MRingOver R ι) → ℤ)
    (Z : Ideal (MRingOver R ι) →₀ ℤ) : NumbersDVR.cycEval n ⇑Z = Z.sum fun W c => c * n W := by
  unfold NumbersDVR.cycEval
  rw [finsum_eq_sum_of_support_subset _ (s := Z.support) ?_]
  · rfl
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hW (by rw [h0, zero_mul])

end Divisors

section Monomials

def listMono {σ : Type*} [DecidableEq σ] (l : List σ) : σ →₀ ℕ :=
  Multiset.toFinsupp (l : Multiset σ)

end Monomials

section Koszul

variable {N : ℕ}

def koszulTerm (ls : List (Fin N)) (k : ℕ) : MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  ((ls.take k).map fun l => X (Sum.inr l)).prod * ((ls.drop (k + 1)).map fun l => X (Sum.inl l)).prod

def koszulExp (G : MvPolynomial (Fin N) ℤ) (i : Fin N) : MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  ∑ μ ∈ G.support, C (G.coeff μ) *
    ∑ k : Fin (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length,
      if (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).get k = i then koszulTerm (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ) k else 0

end Koszul

section PairNumbers

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N : ℕ}

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem vNumL_perm (W : Ideal (MRingOver O ι)) {L₁ L₂ : List (K → ℤ)} (h : L₁.Perm L₂) :
    NumbersDVR.vNumL W L₁ = NumbersDVR.vNumL W L₂ :=
  intNumL_perm (IsLocalRing.ResidueField O) _ h

def koszulList (m m' : Fin N → K → ℤ) (ls : List (Fin N)) (k : ℕ) : List (K → ℤ) :=
  (ls.take k).map m' ++ (ls.drop (k + 1)).map m

end PairNumbers

section Vertical

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Vertical

section ProjBundle

variable {Ω : Type*} [Field Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N : ℕ}

def lineMap (t : Fin N → Φ) : MvPolynomial (Fin N) Ω →+* Polynomial Φ :=
  eval₂Hom (Polynomial.C.comp (algebraMap Ω Φ)) fun l => Polynomial.C (t l) * Polynomial.X

variable {K : Type*}

def genericLineMap (t : Fin N → Φ) : MvPolynomial (K ⊕ Fin N) Ω →+* MvPolynomial (Option K) Φ :=
  eval₂Hom ((C : Φ →+* MvPolynomial (Option K) Φ).comp (algebraMap Ω Φ))
    (Sum.elim (fun k => X (some k)) fun l => C (t l) * X none)

variable [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {M : ℕ}

def bundleToExt (ι : K → Type) (M : ℕ) :
    (Σ o, NumbersDVR.bundleIdx ι M o) → Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι (Fin M) o
  | ⟨none, l⟩ => ⟨none, l⟩
  | ⟨some k, i⟩ => ⟨some k, i⟩

def extToBundle (ι : K → Type) (M : ℕ) :
    (Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι (Fin M) o) → Σ o, NumbersDVR.bundleIdx ι M o
  | ⟨none, l⟩ => ⟨none, l⟩
  | ⟨some k, i⟩ => ⟨some k, i⟩

variable {F : Type*} [Field F] [Algebra F Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

end ProjBundle

end FlagTypings

end GroundTheory.Heights₂.Heights
