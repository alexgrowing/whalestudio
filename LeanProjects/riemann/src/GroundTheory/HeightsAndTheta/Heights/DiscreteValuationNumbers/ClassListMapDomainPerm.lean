import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)

set_option linter.unusedSectionVars false

universe u

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mcIdeal_eq_pointIdeal (R : Type*) [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal R y = pointIdeal R y := rfl

end Coord

section Model

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_iff (P : Ideal (MRing ι O)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P ↔ IsMultiProjPrime P := by
  have hI := VocabMultiHomogIdeal.proof VocabMultiHomog.proof O K ι P
  constructor
  · rintro ⟨hp, hh, hr⟩
    exact ⟨hp, hI.1 hh, hr⟩
  · rintro ⟨hp, hh, hr⟩
    exact ⟨hp, hI.2 hh, hr⟩

theorem isModelOver_iff (P : Ideal (MRing ι O)) (d : ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d ↔ Nonempty K ∧ IsModelOver P d := by
  rw [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver, isMultiProjPrime_iff]
  constructor
  · rintro ⟨hK, hP, ht, hd⟩
    exact ⟨hK, hP, ht, hd⟩
  · rintro ⟨hK, hP, ht, hd⟩
    exact ⟨hK, hP, ht, hd⟩

end Model

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem exists_const_iff {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω}
    (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V) (s : ∀ k, ι k) (v : V) :
    (∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B.lat s) ↔
      ∃ n : ℕ, algebraMap O Ω ϖ ^ n • v ∈ B.lat s := by
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨n, ?_⟩
    have h := B.stable s (algebraMap O Ω ↑u⁻¹) (Subalgebra.algebraMap_mem _ _) _ hv
    rwa [smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow] at h
  · rintro ⟨n, hn⟩
    exact ⟨ϖ ^ n, pow_ne_zero _ hϖ.ne_zero, by rwa [map_pow]⟩

theorem sameGeneric_iff {ϖ : O} (hϖ : Irreducible ϖ) (x : (Σ k, ι k) → Ω)
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' ↔ SameGenericFibre ϖ E E' := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric SameGenericFibre
  refine forall_congr' fun s => imp_congr_right fun _ => and_congr ?_ ?_
  · exact forall₂_congr fun v _ => exists_const_iff hϖ E' s v
  · exact forall₂_congr fun v _ => exists_const_iff hϖ E s v

end Generic

section Cycles

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ratCyc_eq (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    ⇑(IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g) = ratDiv P f g := by
  funext W
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, ratDiv, FlagTypings.divCycle_eq]

theorem redIdeal_eq (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W = specialIdeal W := rfl

theorem vEval_eq (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (Z : Ideal (MRing ι O) →₀ ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J Z = cycEval (fun W => J (specialIdeal W)) ⇑Z := by
  rw [FlagTypings.cycEval_finsupp]
  rfl

end Cycles

section PairNumbers

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem monoList_eq {r : ℕ} {A : Type*} (deg : Fin r → A) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ = (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).map deg := by
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, IndefiniteRowSideFullHecke.NumbersDVR.monoList, List.map_flatMap,
    List.map_replicate]

theorem intNum_get_cast (F : Type*) [Field F] (V : Ideal (MRing ι F)) (L : List (K → ℤ)) (n : ℕ)
    (h : L.length = n) : intNum F V (fun j => L.get (Fin.cast h.symm j)) = intNumL F V L := by
  subst h
  rfl

theorem classList_mapDomain_perm {σ τ : Type*} (e : σ → τ) (cls : τ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls (μ.mapDomain e)).Perm (classList (cls ∘ e) μ) := by
  rw [← Multiset.coe_eq_coe, classList, classList, Multiset.coe_toList, Multiset.coe_toList,
    ← Finsupp.toMultiset_map, Multiset.map_map]

theorem polyNum_eq_classNum {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m : ℕ} (deg : Fin m → K → ℤ) {τ : Type*} [DecidableEq τ] (e : Fin m ≃ τ) (cls : τ → K → ℤ)
    (hcls : cls ∘ e = deg) {H : MvPolynomial (Fin m) ℤ} {d : ℕ} (hH : H.IsHomogeneous d)
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ L => intNum (IsLocalRing.ResidueField O) V L)
                              (specialIdeal W) d deg H = classNum cls (rename e H) [] W := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum classNum
  rw [support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [coeff_rename_mapDomain _ e.injective]
  congr 1
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d := by
    rw [monoList_eq, List.length_map, FlagTypings.length_monoList hH hμ]
  rw [dif_pos hlen]
  refine (intNum_get_cast _ _ _ _ hlen).trans ?_
  rw [List.append_nil]
  refine FlagTypings.intNumL_perm _ _ ?_
  rw [monoList_eq]
  refine ((FlagTypings.monoList_perm deg μ).trans ?_)
  rw [← hcls]
  exact (classList_mapDomain_perm e cls μ).symm

theorem sum_split {r : ℕ} (l : Fin r) (f : Fin r → ℕ) :
    ∑ j, f j = (∑ j ∈ Finset.univ.filter (fun j => j < l), f j) + f l +
      ∑ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < l),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · rw [Finset.sum_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩

theorem isHomogeneous_divDiff {r : ℕ} (l : Fin r) {G : MvPolynomial (Fin r) ℤ} {d : ℕ}
    (hG : G.IsHomogeneous (d + 1)) : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G).IsHomogeneous d := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  apply IsHomogeneous.sum
  intro μ hμ
  have hdeg : ∑ j, μ j = d + 1 := by
    have h := hG (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  by_cases h0 : μ l = 0
  · simp only [h0, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
    exact isHomogeneous_zero _ _ _
  · have hA := IsHomogeneous.prod (Finset.univ.filter fun j => j < l)
      (fun j => (X (Fin.natAdd r j) : MvPolynomial (Fin (r + r)) ℤ) ^ μ j) (fun j => μ j)
      fun j _ => isHomogeneous_X_pow _ _
    have hB := IsHomogeneous.prod (Finset.univ.filter fun j => l < j)
      (fun j => (X (Fin.castAdd r j) : MvPolynomial (Fin (r + r)) ℤ) ^ μ j) (fun j => μ j)
      fun j _ => isHomogeneous_X_pow _ _
    have hM : (∑ a ∈ Finset.range (μ l), (X (Fin.castAdd r l) : MvPolynomial (Fin (r + r)) ℤ) ^ a *
        X (Fin.natAdd r l) ^ (μ l - 1 - a)).IsHomogeneous (μ l - 1) := by
      apply IsHomogeneous.sum
      intro a ha
      have h := (isHomogeneous_X_pow (R := ℤ) (Fin.castAdd r l) a).mul
        (isHomogeneous_X_pow (R := ℤ) (Fin.natAdd r l) (μ l - 1 - a))
      have ha' := Finset.mem_range.mp ha
      rwa [show a + (μ l - 1 - a) = μ l - 1 by omega] at h
    have h := (((isHomogeneous_C _ (G.coeff μ)).mul hA).mul hM).mul hB
    have hs := sum_split l μ
    rw [hdeg] at hs
    convert h using 1
    omega

theorem pairNum_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (P : Ideal (MRing ι O)) (d : ℕ) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    {G : MvPolynomial (Fin r) ℤ} (hG : G.IsHomogeneous (d + 1)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
                              y y' f g G =
      pairNum P y y' f g
        (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G)) [] := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [vEval_eq, ratCyc_eq]
  congr 1
  funext W
  refine polyNum_eq_classNum (Fin.append y y') finSumFinEquiv.symm (Sum.elim y y') ?_
    (isHomogeneous_divDiff l hG) W
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.append_left]
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.append_right]

end PairNumbers

section DualGens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end DualGens

section ProjBundle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def optIdx (M : ℕ) :
    (Σ o : Option K, bundleIdx ι M o) → (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => Fin M) k)
  | ⟨none, l⟩ => ⟨Sum.inr (), l⟩
  | ⟨some k, i⟩ => ⟨Sum.inl k, i⟩

end ProjBundle

section Joins

variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem joinCoords_eq {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) :
    joinCoords y y' = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y y' := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem joinForm_eq {R : Type*} [CommRing R] (f : MRing ι R) :
    joinForm (ι' := ι') f = rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι') f := rfl

end Joins

section Degenerate

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]

def zeroPt : (Σ _ : Unit, Fin 1) → Ω := fun _ => 0

end Degenerate

end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
