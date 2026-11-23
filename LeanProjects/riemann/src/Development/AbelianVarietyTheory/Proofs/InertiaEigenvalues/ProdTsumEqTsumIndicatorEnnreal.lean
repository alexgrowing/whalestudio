import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumExpNegAbsIntLtTop

open Filter Topology
open scoped ENNReal

namespace GlobalTheory.EulerSum

variable {I X : Type} [Zero X]

noncomputable def ofFinset (S : Finset I) (y : S → X) : I →₀ X := by
  classical
  exact Finsupp.onFinset S (fun i => if h : i ∈ S then y ⟨i, h⟩ else 0) (by
    intro i hi; by_contra h; exact hi (dif_neg h))

theorem ofFinset_apply (S : Finset I) (y : S → X) (i : S) : ofFinset S y i = y i := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, i.2]

theorem ofFinset_apply_of_notMem (S : Finset I) (y : S → X) {i : I} (h : i ∉ S) :
    ofFinset S y i = 0 := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, h]

theorem ofFinset_injective (S : Finset I) : Function.Injective (ofFinset (X := X) S) := by
  intro y z h; funext i; rw [← ofFinset_apply S y i, ← ofFinset_apply S z i, h]

theorem support_ofFinset_subset (S : Finset I) (y : S → X) : (ofFinset S y).support ⊆ S := by
  intro i hi
  by_contra h
  exact (Finsupp.mem_support_iff.1 hi) (ofFinset_apply_of_notMem S y h)

theorem mem_range_ofFinset (S : Finset I) (l : I →₀ X) (hl : l.support ⊆ S) :
    l ∈ Set.range (ofFinset S) := by
  refine ⟨fun i => l i, ?_⟩
  ext i
  by_cases h : i ∈ S
  · exact ofFinset_apply S _ ⟨i, h⟩
  · rw [ofFinset_apply_of_notMem S _ h]
    exact (Finsupp.notMem_support_iff.1 (fun hi => h (hl hi))).symm

theorem prod_ofFinset {M : Type} [CommMonoid M] (f : I → X → M) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) (y : S → X) : (ofFinset S y).prod f = ∏ i : S, f i (y i) := by
  rw [Finsupp.prod_of_support_subset _ (support_ofFinset_subset S y) f (fun i _ => hf0 i),
    ← Finset.prod_coe_sort S]
  exact Finset.prod_congr rfl fun i _ => by rw [ofFinset_apply]

theorem tsum_indicator_support_subset {R : Type} [CommSemiring R] [TopologicalSpace R]
    (f : I → X → R) (hf0 : ∀ v, f v 0 = 1) (S : Finset I) :
    ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) =
      ∑' y : S → X, ∏ i : S, f i (y i) := by
  refine ((ofFinset_injective S).tsum_eq ?_).symm.trans ?_
  · intro l hl
    by_contra h
    exact hl (Set.indicator_of_notMem (fun hs => h (mem_range_ofFinset S l hs)) _)
  · refine tsum_congr fun y => ?_
    rw [Set.indicator_of_mem (show ofFinset S y ∈ {l : I →₀ X | l.support ⊆ S} from
      support_ofFinset_subset S y), prod_ofFinset f hf0]

theorem prod_tsum_eq_tsum_indicator_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  rw [tsum_indicator_support_subset f hf0 S,
    GlobalTheory.VolBoxMajorant.tsum_pi_prod_ennreal' (fun (i : S) x => f i x),
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem prod_tsum_eq_tsum_indicator (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hv : ∀ v, Summable fun x => ‖f v x‖) (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  classical
  rw [tsum_indicator_support_subset f hf0 S,
    (GlobalTheory.hasSum_pi_prod_of_summable_norm S (fun _ => X) (fun i x => f i x)
      (fun i => hv i)).tsum_eq,
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem hasProd_tsum_finsupp_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hmono : Monotone (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) := by
    intro S T hST
    exact Finset.prod_le_prod_of_subset_of_one_le' hST
      (fun v _ _ => (hf0 v).symm.le.trans (ENNReal.le_tsum 0))
  have hsup : ⨆ S : Finset I, ∏ v ∈ S, ∑' x, f v x = ∑' l : I →₀ X, l.prod f := by
    simp_rw [prod_tsum_eq_tsum_indicator_ennreal f hf0]
    refine le_antisymm (iSup_le fun S => ENNReal.tsum_le_tsum fun l => ?_) ?_
    · exact Set.indicator_le_self _ _ l
    · rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun T => le_iSup_of_le (T.biUnion Finsupp.support) ?_
      calc ∑ l ∈ T, l.prod f
          = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
              (fun l => l.prod f) l) :=
            Finset.sum_congr rfl fun l hl =>
              (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
                from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod f)).symm
        _ ≤ _ := ENNReal.sum_le_tsum T
  have := tendsto_atTop_iSup hmono
  rw [hsup] at this
  exact this

theorem tsum_finsupp_eq_tprod_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    ∑' l : I →₀ X, l.prod f = ∏' v, ∑' x, f v x :=
  (hasProd_tsum_finsupp_ennreal f hf0).tprod_eq.symm

theorem summable_norm_local (f : I → X → ℂ)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) (v : I) :
    Summable fun x => ‖f v x‖ := by
  have h1 : Summable fun x : {x : X // x ≠ 0} => ‖f v x‖ :=
    ((summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum).1 v
  haveI : Finite ↥({x : X | x ≠ 0}ᶜ) :=
    ((Set.finite_singleton (0 : X)).subset (by intro x hx; simpa using hx)).to_subtype
  exact (summable_subtype_and_compl (s := {x : X | x ≠ 0})).1 ⟨h1, Summable.of_finite⟩

theorem summable_norm_finsupp_prod (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    Summable fun l : I →₀ X => ‖l.prod f‖ := by
  classical
  have hP := (summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum
  let a : I → ℝ := fun v => ∑' x : {x : X // x ≠ 0}, ‖f v x‖
  have hA : Summable a := hP.2
  have ha0 : ∀ v, 0 ≤ a v := fun v => tsum_nonneg fun _ => norm_nonneg _
  let g : I → X → ℝ≥0∞ := fun v x => ENNReal.ofReal ‖f v x‖
  have hg0 : ∀ v, g v 0 = 1 := by intro v; simp [g, hf0 v]
  have hgv : ∀ v, ∑' x, g v x = ENNReal.ofReal (1 + a v) := by
    intro v
    rw [ENNReal.tsum_eq_add_tsum_ite 0, hg0, ENNReal.ofReal_add zero_le_one (ha0 v),
      ENNReal.ofReal_one, ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hP.1 v)]
    congr 1
    refine Eq.trans ?_ (tsum_subtype {x : X | x ≠ 0} (fun x => ENNReal.ofReal ‖f v x‖)).symm
    refine tsum_congr fun x => ?_
    by_cases hx : x = 0 <;> simp [hx, g]
  have hprod : ∀ l : I →₀ X, ENNReal.ofReal ‖l.prod f‖ = l.prod g := by
    intro l
    simp only [Finsupp.prod, norm_prod, g]
    exact ENNReal.ofReal_prod_of_nonneg fun _ _ => norm_nonneg _
  refine summable_of_sum_le (c := Real.exp (∑' v, a v)) (fun _ => norm_nonneg _) fun T => ?_
  have hS := prod_tsum_eq_tsum_indicator_ennreal g hg0 (T.biUnion Finsupp.support)
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  calc ∑ l ∈ T, ENNReal.ofReal ‖l.prod f‖
      = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
          (fun l => l.prod g) l) :=
        Finset.sum_congr rfl fun l hl => by
          rw [hprod, Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
            from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod g)]
    _ ≤ _ := ENNReal.sum_le_tsum T
    _ = ∏ v ∈ T.biUnion Finsupp.support, ∑' x, g v x := hS.symm
    _ = ENNReal.ofReal (∏ v ∈ T.biUnion Finsupp.support, (1 + a v)) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun v _ => by linarith [ha0 v]]
        exact Finset.prod_congr rfl fun v _ => hgv v
    _ ≤ ENNReal.ofReal (Real.exp (∑' v, a v)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∏ v ∈ T.biUnion Finsupp.support, (1 + a v)
            ≤ ∏ v ∈ T.biUnion Finsupp.support, Real.exp (a v) :=
              Finset.prod_le_prod (fun v _ => by linarith [ha0 v])
                fun v _ => by linarith [Real.add_one_le_exp (a v)]
          _ = Real.exp (∑ v ∈ T.biUnion Finsupp.support, a v) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, a v) := Real.exp_le_exp.2 (hA.sum_le_tsum _ (fun v _ => ha0 v))

theorem hasProd_tsum_finsupp (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hN := summable_norm_finsupp_prod f hf0 hsum
  have key : (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) = fun S =>
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) :=
    funext (prod_tsum_eq_tsum_indicator f hf0 (summable_norm_local f hsum))
  show Tendsto (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) atTop _
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun l : I →₀ X => ‖l.prod f‖) hN
    (fun l => ?_) (Eventually.of_forall fun S l => norm_indicator_le_norm_self _ _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop l.support] with S hS
  exact (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ S} from hS)
    (fun l : I →₀ X => l.prod f)).symm

theorem euler_product_intVec {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℂ)
    (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : Fin n → ℤ // x ≠ 0} => ‖f p.1 p.2‖) :
    (Summable fun l : I →₀ (Fin n → ℤ) => ‖l.prod f‖) ∧
      HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨summable_norm_finsupp_prod f hf0 hsum, hasProd_tsum_finsupp f hf0 hsum,
    (hasProd_tsum_finsupp f hf0 hsum).tprod_eq.symm⟩

theorem euler_product_intVec_ennreal {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℝ≥0∞)
    (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨hasProd_tsum_finsupp_ennreal f hf0, tsum_finsupp_eq_tprod_ennreal f hf0⟩

end GlobalTheory.EulerSum
