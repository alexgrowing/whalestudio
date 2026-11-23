import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Approximation
import GroundTheory.FunctionField.ValuationAevalSubCoeffZeroLe
import GroundTheory.FunctionField.Divisor
import GroundTheory.FunctionField.DivisorDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module

section Abstract

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

theorem finiteDimensional_map_mkQ_trans {S T U : Submodule R M} (hST : S ≤ T) (hTU : T ≤ U)
    [FiniteDimensional R (T.map S.mkQ)] [FiniteDimensional R (U.map T.mkQ)] :
    FiniteDimensional R (U.map S.mkQ) ∧
      finrank R (U.map S.mkQ) = finrank R (T.map S.mkQ) + finrank R (U.map T.mkQ) := by
  let f : U.map S.mkQ →ₗ[R] M ⧸ T := (Submodule.factor hST).comp (U.map S.mkQ).subtype
  have hrange : LinearMap.range f = U.map T.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp,
      Submodule.factor_comp_mk]
  have hTU' : T.map S.mkQ ≤ U.map S.mkQ := Submodule.map_mono hTU
  have hker : LinearMap.ker f = (T.map S.mkQ).comap (U.map S.mkQ).subtype := by
    ext ⟨w, hw⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, f,
      LinearMap.coe_comp, Function.comp_apply]
    obtain ⟨m, -, rfl⟩ := Submodule.mem_map.1 hw
    rw [Submodule.mkQ_apply,
      show Submodule.factor hST (Submodule.Quotient.mk m) = Submodule.Quotient.mk m from rfl,
      Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm
      exact Submodule.mem_map_of_mem hm
    · intro hm
      obtain ⟨m', hm', he⟩ := Submodule.mem_map.1 hm
      have : m' - m ∈ S := (Submodule.Quotient.eq S).1 he
      have := hST this
      have h2 : m = m' - (m' - m) := by abel
      rw [h2]
      exact T.sub_mem hm' this
  have ek : LinearMap.ker f ≃ₗ[R] T.map S.mkQ :=
    (LinearEquiv.ofEq _ _ hker).trans (Submodule.comapSubtypeEquivOfLe hTU')
  have er : LinearMap.range f ≃ₗ[R] U.map T.mkQ := LinearEquiv.ofEq _ _ hrange
  have : FiniteDimensional R (LinearMap.ker f) := LinearEquiv.finiteDimensional ek.symm
  have : FiniteDimensional R (LinearMap.range f) := LinearEquiv.finiteDimensional er.symm
  have hrank := LinearMap.rank_range_add_rank_ker f
  have hfin : FiniteDimensional R (U.map S.mkQ) := by
    apply Module.rank_lt_aleph0_iff.1
    rw [← hrank]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 R _) (Module.rank_lt_aleph0 R _)
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [ek.finrank_eq, er.finrank_eq] at h1
  omega

end Abstract

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

theorem Place.finite_not_mem_ring (x : K) : {v : Place k K | x ∉ v.ring}.Finite :=
  (Place.finite_ord_ne_zero x).subset fun v (hv : x ∉ v.ring) => by
    have hx0 : x ≠ 0 := fun h => hv (h ▸ v.ring.zero_mem)
    show v.ord x ≠ 0
    intro h
    exact hv ((v.ord_nonneg_iff hx0).1 (by rw [h]))

variable (k K) in

def repartitions : Submodule k (Place k K → K) where
  carrier := {a | {v : Place k K | a v ∉ v.ring}.Finite}
  add_mem' {a b} ha hb := (ha.union hb).subset fun v (hv : a v + b v ∉ v.ring) => by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hv (add_mem h.1 h.2)
  zero_mem' := Set.finite_empty.subset fun v (hv : (0 : K) ∉ v.ring) => hv v.ring.zero_mem
  smul_mem' c a ha := ha.subset fun v (hv : c • a v ∉ v.ring) => by
    by_contra h
    rw [Set.mem_ofPred_eq, not_not] at h
    rw [Algebra.smul_def] at hv
    exact hv (mul_mem (v.algebraMap_mem c) h)

variable (k K) in

def Repartition : Type _ := repartitions k K

namespace Repartition

instance : AddCommGroup (Repartition k K) := inferInstanceAs (AddCommGroup (repartitions k K))

instance : Module k (Repartition k K) := inferInstanceAs (Module k (repartitions k K))

instance : FunLike (Repartition k K) (Place k K) K where
  coe a := Subtype.val (p := fun f => f ∈ repartitions k K) a
  coe_injective _ _ h := Subtype.ext h

def mk (f : Place k K → K) (hf : {v : Place k K | f v ∉ v.ring}.Finite) : Repartition k K :=
  (⟨f, hf⟩ : repartitions k K)

omit [IsFunctionField k K] in
@[simp]
theorem mk_apply (f : Place k K → K) (hf : {v : Place k K | f v ∉ v.ring}.Finite) (v : Place k K) :
    mk f hf v = f v :=
  rfl

omit [IsFunctionField k K] in
theorem finite_not_mem (a : Repartition k K) : {v : Place k K | a v ∉ v.ring}.Finite :=
  (show repartitions k K from a).2

omit [IsFunctionField k K] in
@[ext]
theorem ext {a b : Repartition k K} (h : ∀ v, a v = b v) : a = b :=
  DFunLike.ext _ _ h

omit [IsFunctionField k K] in
@[simp]
theorem add_apply (a b : Repartition k K) (v : Place k K) : (a + b) v = a v + b v :=
  rfl

omit [IsFunctionField k K] in
@[simp]
theorem sub_apply (a b : Repartition k K) (v : Place k K) : (a - b) v = a v - b v :=
  rfl

omit [IsFunctionField k K] in
@[simp]
theorem neg_apply (a : Repartition k K) (v : Place k K) : (-a) v = -a v :=
  rfl

omit [IsFunctionField k K] in
@[simp]
theorem zero_apply (v : Place k K) : (0 : Repartition k K) v = 0 :=
  rfl

omit [IsFunctionField k K] in
@[simp]
theorem smul_apply (c : k) (a : Repartition k K) (v : Place k K) :
    (c • a) v = algebraMap k K c * a v := by
  change c • a v = _
  rw [Algebra.smul_def]

noncomputable def mul (x : K) : Repartition k K →ₗ[k] Repartition k K where
  toFun a := mk (fun v => x * a v) (((Place.finite_not_mem_ring x).union a.finite_not_mem).subset
    fun v (hv : x * a v ∉ v.ring) => by
      by_contra h
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
      exact hv (mul_mem h.1 h.2))
  map_add' a b := by ext v; simp [mul_add]
  map_smul' c a := by ext v; simp only [mk_apply, smul_apply, RingHom.id_apply]; ring

@[simp]
theorem mul_apply (x : K) (a : Repartition k K) (v : Place k K) : mul x a v = x * a v :=
  rfl

theorem mul_mul (x y : K) (a : Repartition k K) : mul (x * y) a = mul x (mul y a) := by
  ext v; simp [_root_.mul_assoc]

theorem mul_one' (a : Repartition k K) : mul (1 : K) a = a := by
  ext v; simp

noncomputable def diag : K →ₗ[k] Repartition k K where
  toFun x := mk (fun _ => x) (Place.finite_not_mem_ring x)
  map_add' _ _ := rfl
  map_smul' c x := by ext v; simp [Algebra.smul_def]

@[simp]
theorem diag_apply (x : K) (v : Place k K) : diag (k := k) x v = x :=
  rfl

theorem diag_injective : Function.Injective (diag (k := k) (K := K)) := by
  intro x y h
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  have := congrArg (fun a : Repartition k K => a v) h
  simpa using this

theorem mul_diag (x y : K) : mul x (diag (k := k) y) = diag (x * y) := by
  ext v; simp

variable (k K) in

noncomputable def principal : Submodule k (Repartition k K) :=
  LinearMap.range (diag (k := k) (K := K))

theorem mem_principal {a : Repartition k K} : a ∈ principal k K ↔ ∃ x : K, diag x = a :=
  Iff.rfl

theorem diag_mem_principal (x : K) : diag x ∈ principal k K :=
  ⟨x, rfl⟩

theorem mul_mem_principal (x : K) {a : Repartition k K} (ha : a ∈ principal k K) :
    mul x a ∈ principal k K := by
  obtain ⟨y, rfl⟩ := ha
  rw [mul_diag]
  exact diag_mem_principal _

end Repartition

namespace Divisor

open Repartition

def A (D : Divisor k K) : Submodule k (Repartition k K) where
  carrier := {a | ∀ v : Place k K, v.valuation (a v) ≤ WithZero.exp (D v)}
  add_mem' {a b} ha hb v := by
    rw [Repartition.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (ha v) (hb v))
  zero_mem' v := by
    rw [Repartition.zero_apply, map_zero]
    exact zero_le
  smul_mem' c a ha v := by
    rw [Repartition.smul_apply, map_mul]
    exact (mul_le_of_le_one_left' ((v.valuation_le_one_iff _).2 (v.algebraMap_mem c))).trans (ha v)

theorem mem_A {D : Divisor k K} {a : Repartition k K} :
    a ∈ A D ↔ ∀ v : Place k K, v.valuation (a v) ≤ WithZero.exp (D v) :=
  Iff.rfl

theorem A_mono {D E : Divisor k K} (h : D ≤ E) : A D ≤ A E := fun _a ha v =>
  (ha v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 h v))

theorem diag_mem_A_iff {D : Divisor k K} {x : K} : diag x ∈ A D ↔ x ∈ L D :=
  Iff.rfl

omit [IsFunctionField k K] in

theorem add_single_apply_self (D : Divisor k K) (P : Place k K) :
    (D + Finsupp.single P 1 : Divisor k K) P = D P + 1 := by
  simp

omit [IsFunctionField k K] in
theorem add_single_apply_of_ne (D : Divisor k K) {P w : Place k K} (h : w ≠ P) :
    (D + Finsupp.single P 1 : Divisor k K) w = D w := by
  simp [Ne.symm h]

theorem mul_mem_ring_of_valuation {P : Place k K} {t z : K} {n : ℤ}
    (ht : P.valuation t = WithZero.exp (-n)) (hz : P.valuation z ≤ WithZero.exp n) :
    t * z ∈ P.ring := by
  rw [← P.valuation_le_one_iff, map_mul, ht]
  calc WithZero.exp (-n) * P.valuation z ≤ WithZero.exp (-n) * WithZero.exp n :=
        mul_le_mul' le_rfl hz
    _ = 1 := by rw [← WithZero.exp_add]; simp

noncomputable def residueMap (D : Divisor k K) (P : Place k K) {t : K}
    (ht : P.valuation t = WithZero.exp (-(D P + 1))) :
    A (D + Finsupp.single P 1) →ₗ[k] P.ResidueField where
  toFun a := IsLocalRing.residue P.ring ⟨t * (a : Repartition k K) P,
    mul_mem_ring_of_valuation ht (by rw [← add_single_apply_self D P]; exact a.2 P)⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    simp [mul_add]
  map_smul' c a := by
    rw [RingHom.id_apply, Algebra.smul_def,
      IsScalarTower.algebraMap_apply k P.ring P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
    congr 1
    ext
    change t * (c • (a : Repartition k K)) P =
      (algebraMap k P.ring c : K) * (t * (a : Repartition k K) P)
    rw [Repartition.smul_apply, Place.coe_algebraMap_apply]
    ring

theorem residueMap_apply (D : Divisor k K) (P : Place k K) {t : K}
    (ht : P.valuation t = WithZero.exp (-(D P + 1))) (a : A (D + Finsupp.single P 1)) :
    residueMap D P ht a = IsLocalRing.residue P.ring ⟨t * (a : Repartition k K) P,
      mul_mem_ring_of_valuation ht (by rw [← add_single_apply_self D P]; exact a.2 P)⟩ :=
  rfl

theorem residueMap_eq_zero_iff (D : Divisor k K) (P : Place k K) {t : K}
    (ht : P.valuation t = WithZero.exp (-(D P + 1))) (a : A (D + Finsupp.single P 1)) :
    residueMap D P ht a = 0 ↔ (a : Repartition k K) ∈ A D := by
  rw [residueMap_apply, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  change P.ring.valuation (t * (a : Repartition k K) P) < 1 ↔ _
  rw [← P.valuation_lt_one_iff, map_mul, ht]
  constructor
  · intro h w
    by_cases hw : w = P
    · subst hw
      by_cases hz : (a : Repartition k K) w = 0
      · rw [hz, map_zero]; exact zero_le
      · rw [w.valuation_eq_exp_neg_ord hz, ← WithZero.exp_add, ← WithZero.exp_zero,
          WithZero.exp_lt_exp] at h
        rw [w.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp]
        omega
    · rw [← add_single_apply_of_ne D hw]; exact a.2 w
  · intro h
    calc WithZero.exp (-(D P + 1)) * P.valuation ((a : Repartition k K) P)
        ≤ WithZero.exp (-(D P + 1)) * WithZero.exp (D P) := mul_le_mul' le_rfl (h P)
      _ < 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem residueMap_surjective (D : Divisor k K) (P : Place k K) {t : K}
    (ht : P.valuation t = WithZero.exp (-(D P + 1))) :
    Function.Surjective (residueMap D P ht) := by
  classical
  intro r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  have ht0 : t ≠ 0 := by
    intro h; rw [h, map_zero] at ht; exact WithZero.exp_ne_zero ht.symm
  let f : Place k K → K := Pi.single P (t⁻¹ * y)
  have hf : {v : Place k K | f v ∉ v.ring}.Finite := by
    refine (Set.finite_singleton P).subset fun v (hv : f v ∉ v.ring) => ?_
    by_contra hvP
    apply hv
    rw [Set.mem_singleton_iff] at hvP
    simp only [f, Pi.single_apply, hvP, if_false]
    exact v.ring.zero_mem
  let a : Repartition k K := Repartition.mk f hf
  have haA : a ∈ A (D + Finsupp.single P 1) := by
    intro w
    by_cases hw : w = P
    · subst hw
      change w.valuation (f w) ≤ _
      simp only [f, Pi.single_eq_same]
      rw [map_mul, map_inv₀, ht, add_single_apply_self, ← WithZero.exp_neg, neg_neg]
      exact mul_le_of_le_one_right' ((w.valuation_le_one_iff _).2 y.2)
    · change w.valuation (f w) ≤ _
      simp only [f, Pi.single_apply, hw, if_false, map_zero]
      exact zero_le
  refine ⟨⟨a, haA⟩, ?_⟩
  rw [residueMap_apply]
  congr 1
  ext
  change t * f P = y
  simp only [f, Pi.single_eq_same]
  field_simp

noncomputable def relSpace (D E : Divisor k K) :
    Submodule k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  (A E ⊔ principal k K).map (A D ⊔ principal k K).mkQ

omit [IsFunctionField k K] in
theorem le_add_single (D : Divisor k K) (P : Place k K) : D ≤ D + Finsupp.single P 1 :=
  le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one)

theorem relSpace_add_single (D : Divisor k K) (P : Place k K) :
    FiniteDimensional k (relSpace D (D + Finsupp.single P 1)) ∧
      (finrank k (relSpace D (D + Finsupp.single P 1)) : ℤ) +
        finrank k (L (D + Finsupp.single P 1)) = P.deg + finrank k (L D) := by
  classical
  set E : Divisor k K := D + Finsupp.single P 1 with hE
  obtain ⟨t, ht⟩ := P.valuation_surjective (WithZero.exp (-(D P + 1)))
  set ρ : A E →ₗ[k] P.ResidueField := residueMap D P ht with hρdef
  have hρ : Function.Surjective ρ := residueMap_surjective D P ht
  let F : A E →ₗ[k] Repartition k K ⧸ (A D ⊔ principal k K) :=
    (A D ⊔ principal k K).mkQ ∘ₗ (A E).subtype
  have hDE : A D ≤ A E := A_mono (le_add_single D P)
  have hLDE : L D ≤ L E := L_mono (le_add_single D P)
  have hrange : relSpace D E = LinearMap.range F := by
    rw [relSpace, Submodule.map_sup, LinearMap.range_comp, Submodule.range_subtype]
    have : (principal k K).map (A D ⊔ principal k K).mkQ = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      exact le_sup_right
    rw [this, sup_bot_eq]
  have hker : LinearMap.ker ρ ≤ LinearMap.ker F := fun a ha => by
    rw [LinearMap.mem_ker] at ha ⊢
    rw [hρdef, residueMap_eq_zero_iff] at ha
    change Submodule.Quotient.mk (p := A D ⊔ principal k K) (a : Repartition k K) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left ha
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective ρ (LinearMap.range_eq_top.2 hρ)
  let G : P.ResidueField →ₗ[k] Repartition k K ⧸ (A D ⊔ principal k K) := F ∘ₗ σ
  have hG : ∀ a, G (ρ a) = F a := by
    intro a
    have h0 : σ (ρ a) - a ∈ LinearMap.ker ρ := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    have h1 := hker h0
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    exact h1
  have hGrange : LinearMap.range G = LinearMap.range F := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨a, rfl⟩ := hρ r
      exact ⟨a, (hG a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ρ a, hG a⟩
  let ψ : L E →ₗ[k] A E :=
    (diag ∘ₗ (L E).subtype).codRestrict (A E) fun x => diag_mem_A_iff.2 x.2
  have hGker : LinearMap.ker G = LinearMap.range (ρ ∘ₗ ψ) := by
    ext r
    constructor
    · intro hr
      obtain ⟨a, rfl⟩ := hρ r
      rw [LinearMap.mem_ker, hG] at hr
      change Submodule.Quotient.mk (p := A D ⊔ principal k K) (a : Repartition k K) = 0 at hr
      rw [Submodule.Quotient.mk_eq_zero] at hr
      obtain ⟨b, hb, c, ⟨x, rfl⟩, hbc⟩ := Submodule.mem_sup.1 hr
      have hxE : x ∈ L E := by
        rw [← diag_mem_A_iff]
        have : diag x = (a : Repartition k K) - b := by rw [← hbc]; abel
        rw [this]
        exact (A E).sub_mem a.2 (hDE hb)
      refine ⟨⟨x, hxE⟩, ?_⟩
      have hsplit : a = ⟨b, hDE hb⟩ + ψ ⟨x, hxE⟩ := Subtype.ext hbc.symm
      rw [hsplit, map_add]
      have : ρ ⟨b, hDE hb⟩ = 0 := (residueMap_eq_zero_iff D P ht _).2 hb
      rw [this, zero_add]
      rfl
    · rintro ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      change G (ρ (ψ x)) = 0
      rw [hG]
      change Submodule.Quotient.mk (p := A D ⊔ principal k K) (diag (x : K)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right (diag_mem_principal _)
  have hkerψ : LinearMap.ker (ρ ∘ₗ ψ) = (L D).comap (L E).subtype := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hρdef, residueMap_eq_zero_iff]
    rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker (ρ ∘ₗ ψ)
  rw [hkerψ, (Submodule.comapSubtypeEquivOfLe hLDE).finrank_eq] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker G
  rw [hGker] at h2
  have hdeg : finrank k P.ResidueField = P.deg := rfl
  refine ⟨?_, ?_⟩
  · rw [hrange, ← hGrange]
    infer_instance
  · rw [hrange, ← hGrange]
    omega

theorem relSpace_finrank_of_le_of_deg_lt (n : ℕ) :
    ∀ {D E : Divisor k K}, D ≤ E → deg (E - D) < n →
      FiniteDimensional k (relSpace D E) ∧
        (finrank k (relSpace D E) : ℤ) + finrank k (L E) = deg E - deg D + finrank k (L D) := by
  classical
  induction n with
  | zero =>
    intro D E hDE hn
    have := deg_nonneg (sub_nonneg.2 hDE)
    omega
  | succ n ih =>
    intro D E hDE hn
    by_cases hED : E = D
    · subst hED
      have : relSpace E E = ⊥ := Submodule.mkQ_map_self _
      rw [this]
      refine ⟨inferInstance, ?_⟩
      simp
    obtain ⟨v, hv⟩ : ∃ v, D v < E v := by
      by_contra h
      push Not at h
      exact hED (le_antisymm (Finsupp.le_def.2 h) hDE)
    set E' := E - Finsupp.single v 1 with hE'
    have hDE' : D ≤ E' := Finsupp.le_def.2 fun w => by
      rw [hE', Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · have := Finsupp.le_def.1 hDE w; omega
    have hn' : deg (E' - D) < n := by
      have h1 : deg (E' - D) = deg (E - D) - v.deg := by
        rw [hE', map_sub, map_sub, map_sub, deg_single]; ring
      have := v.deg_pos
      omega
    obtain ⟨hfin', h'⟩ := ih hDE' hn'
    have hE : E = E' + Finsupp.single v 1 := by rw [hE']; abel
    obtain ⟨hfin1, h1⟩ := relSpace_add_single E' v
    rw [← hE] at hfin1 h1
    have hST : A D ⊔ principal k K ≤ A E' ⊔ principal k K := sup_le_sup_right (A_mono hDE') _
    have hTU : A E' ⊔ principal k K ≤ A E ⊔ principal k K := by
      refine sup_le_sup_right (A_mono ?_) _
      rw [hE]
      exact le_add_single E' v
    have e1 : relSpace D E' = (A E' ⊔ principal k K).map (A D ⊔ principal k K).mkQ := rfl
    have e2 : relSpace E' E = (A E ⊔ principal k K).map (A E' ⊔ principal k K).mkQ := rfl
    have e3 : relSpace D E = (A E ⊔ principal k K).map (A D ⊔ principal k K).mkQ := rfl
    rw [e1] at hfin' h'
    rw [e2] at hfin1 h1
    obtain ⟨hfin, hsum⟩ := finiteDimensional_map_mkQ_trans hST hTU
    rw [e3]
    refine ⟨hfin, ?_⟩
    rw [hsum]
    have hdeg : deg E = deg E' + v.deg := by rw [hE, map_add, deg_single, one_mul]
    push_cast
    omega

instance finiteDimensional_relSpace {D E : Divisor k K} [Fact (D ≤ E)] :
    FiniteDimensional k (relSpace D E) :=
  (relSpace_finrank_of_le_of_deg_lt ((deg (E - D)).toNat + 1) (Fact.out : D ≤ E) (by omega)).1

theorem finiteDimensional_relSpace_of_le {D E : Divisor k K} (h : D ≤ E) :
    FiniteDimensional k (relSpace D E) :=
  (relSpace_finrank_of_le_of_deg_lt ((deg (E - D)).toNat + 1) h (by omega)).1

theorem finrank_relSpace {D E : Divisor k K} (h : D ≤ E) :
    (finrank k (relSpace D E) : ℤ) =
      (deg E - deg D) - ((finrank k (L E) : ℤ) - finrank k (L D)) := by
  have := (relSpace_finrank_of_le_of_deg_lt ((deg (E - D)).toNat + 1) h (by omega)).2
  omega

end Divisor

end GroundTheory.FunctionField
