import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Polynomial

variable (D : D7)

def tupOf (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))) : Tup2 D :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)

def ES (S : Set (Tup2 D)) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0g D.nd =>
    ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      (open Classical in if tupOf D a ∈ S then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0)

open Classical in

def labT : Finset (Tup2 D) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  (Finset.univ.image (tupOf D)).filter fun t => ∀ k v, IsLabel D k (t k v)

def zTup (t : Tup2 D) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  tensAlg (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    fun kv => D.ntypes.eSer kv.1 (t kv.1 kv.2)

local instance factTypePrime (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroTypePrime (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

variable {D}

theorem tupOf_apply (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))) (k : Fin 2)
    (v : D.nd.PlG k) : tupOf D a k v = Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩) := rfl

theorem tupOf_injective : Function.Injective (tupOf D) := fun a b h =>
  funext fun kv => PrimeDegreeVariant.Ten.monicOf_inj _ _ (congrFun (congrFun h kv.1) kv.2)

theorem mem_range_tupOf {t : Tup2 D} :
    t ∈ Set.range (tupOf D) ↔ ∀ k v, (t k v).Monic ∧ (t k v).natDegree = D.R.r := by
  constructor
  · rintro ⟨a, rfl⟩ k v
    exact ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf _, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf _⟩
  · intro h
    exact ⟨fun kv i => (t kv.1 kv.2).coeff i, funext fun k => funext fun v =>
      Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (h k v).1 (h k v).2⟩

theorem mem_labT {t : Tup2 D} : t ∈ labT D ↔ ∀ k v, IsLabel D k (t k v) := by
  classical
  unfold labT
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨a, ha⟩ := mem_range_tupOf.2 fun k v => ⟨(h k v).1, (h k v).2.1⟩
  exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩

theorem zTup_coeff (t : Tup2 D) (g : G0g D.nd) :
    (zTup D t).coeff g = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (t kv.1 kv.2)).coeff (g kv) := rfl

theorem zTup_eq_zero {t : Tup2 D} (h : t ∉ labT D) : zTup D t = 0 := by
  rw [mem_labT] at h
  push Not at h
  obtain ⟨k, v, h⟩ := h
  ext g
  rw [zTup_coeff]
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k)) ?_
  rw [D.ntypes.eSer_zero k (t k v) h]
  rfl

theorem zTup_mul_self (t : Tup2 D) : zTup D t * zTup D t = zTup D t :=
  (PrimeDegreeVariant.Ten.tens_mul _ _).trans (congrArg PrimeDegreeVariant.Ten.tens (funext fun _ => D.ntypes.eSer_idem _ _))

theorem zTup_mul_of_ne {t t' : Tup2 D} (h : t ≠ t') : zTup D t * zTup D t' = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 h
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hk
  refine (PrimeDegreeVariant.Ten.tens_mul _ _).trans ?_
  ext g
  rw [PrimeDegreeVariant.Ten.tens_coeff]
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k)) ?_
  rw [D.ntypes.eSer_orth k _ _ hv]
  rfl

theorem zTup_comm (t : Tup2 D) (a : MonoidAlgebra ℂ (G0g D.nd)) : zTup D t * a = a * zTup D t := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  | single x c =>
    ext g
    rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, zTup_coeff, zTup_coeff, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun kv _ => ?_
    have := congrArg (fun z => z.coeff (g kv))
      (D.ntypes.eSer_central kv.1 (t kv.1 kv.2) (MonoidAlgebra.single (x kv) 1))
    simpa only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
      Pi.mul_apply, Pi.inv_apply] using this

open Classical in

theorem ES_coeff (S : Set (Tup2 D)) (g : G0g D.nd) :
    (ES D S).coeff g = ∑ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      if tupOf D a ∈ S then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0 :=
  finsum_eq_sum_of_fintype _

theorem ES_good : ES D {t | D.ntypes.goodTuple t} = D.ntypes.e0 := rfl

open Classical in

theorem ES_eq_sum_coef (S : Set (Tup2 D)) :
    ES D S = ∑ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      if tupOf D a ∈ S then zTup D (tupOf D a) else 0 := by
  ext g
  rw [ES_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl

open Classical in

theorem ES_eq_sum (S : Set (Tup2 D)) : ES D S = ∑ t ∈ (labT D).filter (· ∈ S), zTup D t := by
  rw [ES_eq_sum_coef, ← Finset.sum_image (s := Finset.univ) (g := tupOf D)
    (f := fun t => if t ∈ S then zTup D t else 0) fun _ _ _ _ h => tupOf_injective h, Finset.sum_filter]
  symm
  refine Finset.sum_subset (by unfold labT; exact Finset.filter_subset _ _) fun t _ ht => ?_
  rw [zTup_eq_zero ht, ite_self]

theorem ES_eq_finsum (S : Set (Tup2 D)) : ES D S = ∑ᶠ t ∈ S, zTup D t := by
  classical
  rw [ES_eq_sum]
  symm
  refine finsum_mem_eq_sum_of_inter_support_eq _ (Set.ext fun t => ?_)
  simp only [Set.mem_inter_iff, Finset.coe_filter, Set.mem_setOf_eq, Function.mem_support]
  exact ⟨fun h => ⟨⟨by_contra fun h' => h.2 (zTup_eq_zero h'), h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

theorem ES_eq_zSet (S : Set (Tup2 D)) :
    ES D S = zSet (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      (Lab := fun kv => (ZMod (D.host.g kv.1))[X]) (fun kv => D.ntypes.eSer kv.1)
      {t | (fun k v => t ⟨k, v⟩) ∈ S} := by
  rw [ES_eq_finsum]
  symm
  refine finsum_mem_eq_of_bijOn (fun t k v => t ⟨k, v⟩) ⟨fun t ht => ht, fun t _ t' _ h => ?_, fun t ht => ?_⟩
    fun t _ => rfl
  · exact funext fun kv => congrFun (congrFun h kv.1) kv.2
  · exact ⟨fun kv => t kv.1 kv.2, ht, rfl⟩

theorem ES_coe (S : Finset (Tup2 D)) : ES D (S : Set (Tup2 D)) = ∑ t ∈ S, zTup D t := by
  rw [ES_eq_finsum, finsum_mem_coe_finset]

theorem ES_singleton (t : Tup2 D) : ES D {t} = zTup D t := by
  rw [ES_eq_finsum, finsum_mem_singleton]

theorem ES_empty : ES D ∅ = 0 := by
  rw [ES_eq_finsum, finsum_mem_empty]

theorem ES_congr {S T : Set (Tup2 D)} (h : ∀ t ∈ labT D, t ∈ S ↔ t ∈ T) : ES D S = ES D T := by
  classical
  rw [ES_eq_sum, ES_eq_sum, Finset.filter_congr h]

theorem ES_inter_labT (S : Set (Tup2 D)) : ES D (S ∩ labT D) = ES D S :=
  ES_congr fun _ ht => ⟨fun h => h.1, fun h => ⟨h, ht⟩⟩

theorem ES_univ : ES D Set.univ = 1 := by
  classical
  rw [ES_eq_sum_coef]
  simp only [Set.mem_univ, if_true]
  refine (PrimeDegreeVariant.Ten.sum_tens (PrimeDegreeVariant.Ten.ESer D)).trans ?_
  simp only [PrimeDegreeVariant.Ten.ESer_sum]
  exact PrimeDegreeVariant.Ten.tens_one

theorem sum_zTup : ∑ t ∈ labT D, zTup D t = 1 := by
  rw [← ES_coe, ← ES_univ]
  exact ES_congr fun _ ht => ⟨fun _ => trivial, fun _ => ht⟩

theorem isSeries_zTup : IsSeries (zTup D) :=
  ⟨zTup_mul_self, zTup_comm, fun _ _ => zTup_mul_of_ne, labT D, fun _ => zTup_eq_zero, sum_zTup⟩

open Classical in

theorem ES_mul_zTup (S : Set (Tup2 D)) (t : Tup2 D) :
    ES D S * zTup D t = if t ∈ S then zTup D t else 0 := by
  rw [ES_eq_sum, Finset.sum_mul]
  by_cases hl : t ∈ labT D
  · split_ifs with h
    · rw [Finset.sum_eq_single_of_mem t (Finset.mem_filter.2 ⟨hl, h⟩) fun _ _ => zTup_mul_of_ne, zTup_mul_self]
    · exact Finset.sum_eq_zero fun s hs => zTup_mul_of_ne fun e => h (e ▸ (Finset.mem_filter.1 hs).2)
  · simp [zTup_eq_zero hl]

theorem ES_mul (S T : Set (Tup2 D)) : ES D S * ES D T = ES D (S ∩ T) := by
  classical
  rw [ES_eq_sum T, Finset.mul_sum, ES_eq_sum (S ∩ T), Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ES_mul_zTup]
  by_cases h : t ∈ S <;> by_cases h' : t ∈ T <;> simp [h, h']

theorem ES_mul_self (S : Set (Tup2 D)) : ES D S * ES D S = ES D S := by
  rw [ES_mul, Set.inter_self]

theorem ES_comm (S : Set (Tup2 D)) (a : MonoidAlgebra ℂ (G0g D.nd)) : ES D S * a = a * ES D S := by
  rw [ES_eq_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => zTup_comm t a

theorem ES_mem_center (S : Set (Tup2 D)) : ES D S ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
  Subalgebra.mem_center_iff.2 fun a => (ES_comm S a).symm

theorem ES_union_add_inter (S T : Set (Tup2 D)) : ES D (S ∪ T) + ES D (S ∩ T) = ES D S + ES D T := by
  classical
  simp only [ES_eq_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t ∈ S <;> by_cases h' : t ∈ T <;> simp [h, h']

theorem ES_union {S T : Set (Tup2 D)} (h : Disjoint S T) : ES D (S ∪ T) = ES D S + ES D T := by
  rw [← ES_union_add_inter, Set.disjoint_iff_inter_eq_empty.1 h, ES_empty, add_zero]

theorem ES_compl (S : Set (Tup2 D)) : ES D Sᶜ = 1 - ES D S := by
  rw [eq_sub_iff_add_eq', ← ES_union disjoint_compl_right, Set.union_compl_self, ES_univ]

theorem ES_bad : ES D {t | ¬ D.ntypes.goodTuple t} = 1 - D.ntypes.e0 :=
  ES_compl {t | D.ntypes.goodTuple t}

theorem ES_pi (A : ∀ k, D.nd.PlG k → Finset (ZMod (D.host.g k))[X]) :
    ES D {t | ∀ k v, t k v ∈ A k v} =
      tensAlg (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
        fun kv => ∑ f ∈ A kv.1 kv.2, D.ntypes.eSer kv.1 f := by
  classical
  rw [ES_eq_zSet]
  have : {t : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X] |
      (fun k v => t ⟨k, v⟩) ∈ {t : Tup2 D | ∀ k v, t k v ∈ A k v}} =
      (Fintype.piFinset fun kv : (Σ k : Fin 2, D.nd.PlG k) => A kv.1 kv.2 : Finset _) := by
    ext t
    simp [Fintype.mem_piFinset, Sigma.forall]
  rw [this, zSet, finsum_mem_coe_finset]
  ext g
  rw [tensAlg_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [tensAlg_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.prod_univ_sum]

theorem ES_at (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]) :
    ES D {t | t k v = f} = atPlace D k v (D.ntypes.eSer k f) := by
  classical
  choose L hL hs using D.ntypes.eSer_sum
  let A : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Finset (ZMod (D.host.g kv.1))[X] :=
    Function.update (fun kv => L kv.1) ⟨k, v⟩ {f}
  have h1 : ES D {t | t k v = f} = ES D {t | ∀ k' v', t k' v' ∈ A ⟨k', v'⟩} := by
    refine ES_congr fun t ht => ⟨fun h k' v' => ?_, fun h => ?_⟩
    · by_cases e : (⟨k', v'⟩ : Σ k : Fin 2, D.nd.PlG k) = ⟨k, v⟩
      · cases e
        simpa [A] using h
      · simp only [A, Function.update_of_ne e]
        exact (hL _ _).2 (mem_labT.1 ht k' v')
    · simpa [A] using h k v
  rw [h1, ES_pi fun k' v' => A ⟨k', v'⟩]
  refine Eq.trans ?_ (PrimeDegreeVariant.Ten.mapDomain_mulSingle (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
    GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ (D.ntypes.eSer k f)).symm
  refine congrArg PrimeDegreeVariant.Ten.tens (funext fun kv => ?_)
  by_cases e : kv = ⟨k, v⟩
  · subst e
    simp [A]
  · rw [Function.update_of_ne e]
    show ∑ f ∈ A kv, _ = _
    simp only [A, Function.update_of_ne e]
    exact hs kv.1

theorem tupOf_one_mem_labT : tupOf D (fun _ _ => 1) ∈ labT D := by
  refine mem_labT.2 fun k v => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf _, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf _, ?_⟩
  rw [tupOf_apply]
  rcases Nat.eq_zero_or_pos D.R.r with h | h
  · have h1 := Formalism.CyclotomicNorms.Sqf.monic_monicOf (K := ZMod (D.host.g k)) (fun _ : Fin D.R.r => 1)
    rw [Monic, leadingCoeff, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf] at h1
    exact ((congrArg (coeff _) h).symm.trans h1).trans_ne one_ne_zero
  · exact (Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt _ ⟨0, h⟩).trans_ne one_ne_zero

example : ∃ t ∈ labT D, ES D {t} ≠ 0 := by
  by_contra h
  push Not at h
  refine one_ne_zero (α := MonoidAlgebra ℂ (G0g D.nd)) ?_
  rw [← sum_zTup]
  exact Finset.sum_eq_zero fun t ht => by rw [← ES_singleton, h t ht]

example (hr : 0 < D.R.r) (k : Fin 2) (v : D.nd.PlG k) : ES D {t | t k v = X ^ D.R.r} = 0 := by
  rw [← ES_empty]
  refine ES_congr fun t ht => ⟨fun h => (mem_labT.1 ht k v).2.2 ?_, False.elim⟩
  rw [show t k v = X ^ D.R.r from h, coeff_X_pow, if_neg hr.ne]

example (S₁ : Set (Tup D 0)) (S₂ : Set (Tup D 1)) :
    ES D (cyl D 0 S₁) * ES D (cyl D 1 S₂) = ES D {t | t 0 ∈ S₁ ∧ t 1 ∈ S₂} := ES_mul _ _

example : D.ntypes.e0 * ES D {t | ¬ D.ntypes.goodTuple t} = 0 := by
  rw [ES_bad, mul_sub, mul_one, ← ES_good, ES_mul_self, sub_self]

end GlobalTheory.RowLev
