import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

@[reducible] def Ainf.weakTopology : TopologicalSpace (Ainf p R) :=
  (span {(p : Ainf p R)} ⊔ RingHom.ker (Ainf.theta p R)).adicTopology

instance Acris.topologicalSpace : TopologicalSpace (Acris p R) :=
  (span {(p : Acris p R)}).adicTopology

instance Acris.nonarchimedeanRing : NonarchimedeanRing (Acris p R) :=
  (span {(p : Acris p R)}).nonarchimedean

theorem Acris.isAdic : IsAdic (span {(p : Acris p R)}) := rfl

namespace BdRPlus

def nhd (nk : ℕ × ℕ) : AddSubgroup (BdRPlus p R) where
  carrier := {x | ∃ a : Ainf p R, eval p R nk.1 x = eval p R nk.1 (algebraMap _ _ (p ^ nk.2 * a))}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb, mul_add, map_add, map_add]⟩
  neg_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨-a, by rw [map_neg, ha, mul_neg, map_neg, map_neg]⟩

variable {p R}

theorem eval_eq_of_le {m n : ℕ} (h : m ≤ n) {x y : BdRPlus p R}
    (e : eval p R n x = eval p R n y) : eval p R m x = eval p R m y := by
  have h1 := factorPow_evalₐ (AinfInv.kerTheta p R) h x
  have h2 := factorPow_evalₐ (AinfInv.kerTheta p R) h y
  exact h1.symm.trans ((congrArg _ e).trans h2)

theorem nhd_anti {i j : ℕ × ℕ} (h : i ≤ j) : nhd p R j ≤ nhd p R i := by
  rintro x ⟨a, ha⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h.2
  refine ⟨p ^ c * a, ?_⟩
  rw [eval_eq_of_le h.1 ha, hc, pow_add, mul_assoc]

variable (p R)

theorem ringSubgroupsBasis : RingSubgroupsBasis (nhd p R) :=
  RingSubgroupsBasis.of_comm _
    (fun i j => ⟨i ⊔ j, le_inf (nhd_anti le_sup_left) (nhd_anti le_sup_right)⟩)
    (fun i => ⟨i, by
      rintro _ ⟨x, ⟨a, ha⟩, y, ⟨b, hb⟩, rfl⟩
      refine ⟨a * (p ^ i.2 * b), ?_⟩
      change eval p R i.1 (x * y) = _
      rw [map_mul, ha, hb, ← map_mul, ← map_mul, mul_assoc]⟩)
    (fun x i => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (eval p R i.1 x)
      obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj (p : Ainf p R) z
      refine ⟨(i.1, i.2 + m), ?_⟩
      rintro y ⟨a, ha⟩
      refine ⟨c * a, ?_⟩
      change eval p R i.1 (x * y) = _
      rw [map_mul, ha, ← hz, ← eval_algebraMap, ← map_mul,
        IsScalarTower.algebraMap_apply (Ainf p R) (AinfInv p R) (BdRPlus p R),
        IsScalarTower.algebraMap_apply (Ainf p R) (AinfInv p R) (BdRPlus p R), ← map_mul]
      congr 2
      simp only [map_mul, map_pow, pow_add, ← hc]
      ring)

instance topologicalSpace : TopologicalSpace (BdRPlus p R) := (ringSubgroupsBasis p R).topology

instance nonarchimedeanRing : NonarchimedeanRing (BdRPlus p R) :=
  (ringSubgroupsBasis p R).nonarchimedean

theorem hasBasis_nhds_zero :
    (nhds (0 : BdRPlus p R)).HasBasis (fun _ => True) fun i => (nhd p R i : Set (BdRPlus p R)) :=
  (ringSubgroupsBasis p R).hasBasis_nhds_zero

variable {p R} {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

theorem map_mem_nhd (f : R →+* S) {i : ℕ × ℕ} {x : BdRPlus p R} (hx : x ∈ nhd p R i) :
    map p f x ∈ nhd p S i := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨Ainf.map p f a, ?_⟩
  rw [eval_map, ha, ← eval_map, map_algebraMap_ainf, map_mul, map_pow, map_natCast]

theorem continuous_map (f : R →+* S) : Continuous (map p f) :=
  continuous_of_continuousAt_zero (map p f) (by
    rw [ContinuousAt, map_zero, (hasBasis_nhds_zero p R).tendsto_iff (hasBasis_nhds_zero p S)]
    exact fun i _ => ⟨i, trivial, fun x hx => map_mem_nhd f hx⟩)

instance {G : Type*} [Group G] [MulSemiringAction G R] : ContinuousConstSMul G (BdRPlus p R) :=
  ⟨fun _ => continuous_map _⟩

end BdRPlus

variable {p R}

theorem Acris.continuous_ringHom {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
    [IsAdicComplete (span {(p : S)}) S] (f : Acris p R →+* Acris p S) : Continuous f :=
  continuous_of_continuousAt_zero f (by
    rw [ContinuousAt, map_zero, (Ideal.hasBasis_nhds_zero_adic (span {(p : Acris p R)})).tendsto_iff
      (Ideal.hasBasis_nhds_zero_adic (span {(p : Acris p S)}))]
    exact fun i _ => ⟨i, trivial, fun x hx => pow_le_comap_pow (span_natCast_le_comap p f) i hx⟩)

instance {G : Type*} [Group G] [MulSemiringAction G R] : ContinuousConstSMul G (Acris p R) :=
  ⟨fun g => Acris.continuous_ringHom (Acris.map p (MulSemiringAction.toRingHom G R g))⟩

namespace Bst

variable (p R) in

def plus : Subring (Bst p R) :=
  Subring.closure (Set.range (fun x : BcrisPlus p R =>
    algebraMap (Bcris p R) (Bst p R) (algebraMap _ _ x)) ∪ Set.range logFlat)

theorem algebraMap_mem_plus (x : BcrisPlus p R) :
    algebraMap (Bcris p R) (Bst p R) (algebraMap _ _ x) ∈ plus p R :=
  Subring.subset_closure (Or.inl ⟨x, rfl⟩)

theorem logFlat_mem_plus (ϖ : PFlat p R) : logFlat ϖ ∈ plus p R :=
  Subring.subset_closure (Or.inr ⟨ϖ, rfl⟩)

theorem frob_mem_plus {x : Bst p R} (hx : x ∈ plus p R) : frob p R x ∈ plus p R := by
  refine (show plus p R ≤ (plus p R).comap (frob p R) from Subring.closure_le.2 ?_) hx
  rintro _ (⟨y, rfl⟩ | ⟨ϖ, rfl⟩)
  · simpa using algebraMap_mem_plus _
  · simpa using mul_mem (natCast_mem _ p) (logFlat_mem_plus ϖ)

theorem smul_mem_plus {G : Type*} [Group G] [MulSemiringAction G R] (g : G) {x : Bst p R}
    (hx : x ∈ plus p R) : g • x ∈ plus p R := by
  refine (show plus p R ≤ (plus p R).comap (MulSemiringAction.toRingHom G _ g) from
    Subring.closure_le.2 ?_) hx
  rintro _ (⟨y, rfl⟩ | ⟨ϖ, rfl⟩)
  · simpa [smul_algebraMap, Bcris.smul_algebraMap] using algebraMap_mem_plus _
  · simpa [smul_logFlat] using logFlat_mem_plus _

theorem monodromy_mem_plus {x : Bst p R} (hx : x ∈ plus p R) : monodromy p R x ∈ plus p R := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ | ⟨ϖ, rfl⟩ := hx
    · simp
    · simp
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx' hy) (mul_mem hy' hx)

end Bst

end Reformulated.AutPerF
