import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailExtra
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreNum

section Values

variable {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra F Ω]

def vals (F : Type) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Submodule F Ω :=
  (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) d).map (aeval y).toLinearMap

theorem one_le_weight {a : (Σ k, ι k) →₀ ℕ} {v : Σ k, ι k} (hv : a v ≠ 0) :
    1 ≤ Finsupp.weight (NumbersDVR.blockWeight ι) a v.1 := by
  have h := Finsupp.le_weight_of_ne_zero (w := NumbersDVR.blockWeight ι) (fun _ _ => Nat.zero_le _) hv v.1
  simpa [NumbersDVR.blockWeight] using h

theorem eq_zero_of_weight {a : (Σ k, ι k) →₀ ℕ} (h : Finsupp.weight (NumbersDVR.blockWeight ι) a = 0) :
    a = 0 := by
  ext v
  by_contra hv
  have h1 := one_le_weight hv
  rw [h] at h1
  simp at h1

theorem exists_ne_zero_of_weight {a : (Σ k, ι k) →₀ ℕ} {k : K}
    (h : Finsupp.weight (NumbersDVR.blockWeight ι) a k ≠ 0) : ∃ i, a ⟨k, i⟩ ≠ 0 := by
  by_contra hne
  push Not at hne
  apply h
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  obtain ⟨k', i⟩ := v
  by_cases hk : k' = k
  · subst hk
    simp [hne i]
  · simp [NumbersDVR.blockWeight, Ne.symm hk]

theorem peel {a : (Σ k, ι k) →₀ ℕ} {d : K → ℕ} {k : K}
    (h : Finsupp.weight (NumbersDVR.blockWeight ι) a = d + Pi.single k 1) :
    ∃ i, ∃ a' : (Σ k, ι k) →₀ ℕ, a = a' + Finsupp.single ⟨k, i⟩ 1 ∧
      Finsupp.weight (NumbersDVR.blockWeight ι) a' = d := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_weight (a := a) (k := k) (by rw [h]; simp)
  have e : a = (a - Finsupp.single ⟨k, i⟩ 1) + Finsupp.single ⟨k, i⟩ 1 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))).symm
  refine ⟨i, a - Finsupp.single ⟨k, i⟩ 1, e, ?_⟩
  have h2 := h
  rw [e, map_add, Finsupp.weight_single, one_smul] at h2
  exact add_right_cancel h2

theorem vals_eq_span (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    vals F y d = Submodule.span F {z | ∃ a : (Σ k, ι k) →₀ ℕ,
      Finsupp.weight (NumbersDVR.blockWeight ι) a = d ∧ aeval y (monomial a (1 : F)) = z} := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule] at hg
    rw [AlgHom.toLinearMap_apply, g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have hw := hg (mem_support_iff.mp ha)
    have hm : monomial a (coeff a g) = coeff a g • monomial a (1 : F) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hw, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨monomial a 1, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (isWeightedHomogeneous_monomial _ _ _ ha), rfl⟩

theorem mem_vals_of (y : (Σ k, ι k) → Ω) {d : K → ℕ} {a : (Σ k, ι k) →₀ ℕ}
    (ha : Finsupp.weight (NumbersDVR.blockWeight ι) a = d) : aeval y (monomial a (1 : F)) ∈ vals F y d := by
  rw [vals_eq_span]
  exact Submodule.subset_span ⟨a, ha, rfl⟩

theorem vals_mul_le (y : (Σ k, ι k) → Ω) (d e : K → ℕ) : vals F y d * vals F y e ≤ vals F y (d + e) := by
  rw [vals_eq_span y d, vals_eq_span y e, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  show aeval y (monomial a (1 : F)) * aeval y (monomial b (1 : F)) ∈ vals F y (d + e)
  rw [← map_mul, monomial_mul, one_mul]
  exact mem_vals_of y (by rw [map_add, ha, hb])

theorem vals_single_le (y : (Σ k, ι k) → Ω) (d : K → ℕ) (k : K) :
    vals F y (d + Pi.single k 1) ≤ vals F y d * vals F y (Pi.single k 1) := by
  rw [vals_eq_span y (d + _), Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨i, a', rfl, ha'⟩ := peel ha
  rw [← one_mul (1 : F), ← monomial_mul, map_mul]
  exact Submodule.mul_mem_mul (mem_vals_of y ha')
    (mem_vals_of y (by rw [Finsupp.weight_single, one_smul]; rfl))

theorem vals_zero (y : (Σ k, ι k) → Ω) : vals F y (0 : K → ℕ) = 1 := by
  rw [vals_eq_span, Submodule.one_eq_span]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [eq_zero_of_weight ha]
    simp
  · rintro rfl
    exact ⟨0, map_zero _, by simp⟩

theorem vals_single (y : (Σ k, ι k) → Ω) (k : K) :
    vals F y (Pi.single k 1) = Submodule.span F (Set.range fun i => y ⟨k, i⟩) := by
  rw [vals_eq_span]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, a', rfl, ha'⟩ := peel (d := 0) (by rw [ha, zero_add])
    rw [eq_zero_of_weight ha', zero_add]
    exact ⟨i, (aeval_X y _).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Finsupp.single ⟨k, i⟩ 1, by rw [Finsupp.weight_single, one_smul]; rfl, aeval_X y _⟩

theorem vals_eq_prod [Fintype K] (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    vals F y d = ∏ k, vals F y (Pi.single k 1) ^ d k := by
  induction hn : ∑ k, d k generalizing d with
  | zero =>
    have hd : d = 0 := funext fun k => by
      simpa using (Finset.sum_eq_zero_iff.mp hn) k (Finset.mem_univ _)
    subst hd
    simp [vals_zero]
  | succ n ih =>
    obtain ⟨k, hk⟩ : ∃ k, d k ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hn
    set d' : K → ℕ := d - Pi.single k 1 with hd'
    have hd : d = d' + Pi.single k 1 := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [hd']
        omega
      · simp [hd', hj]
    have hs : ∑ j, d' j = n := by
      rw [hd] at hn
      simp only [Pi.add_apply, Finset.sum_add_distrib] at hn
      simpa using hn
    rw [hd, le_antisymm (vals_single_le y _ k) (vals_mul_le y _ _), ih _ hs]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp

omit [DecidableEq K] in

theorem prod_span_blocks [Fintype K] (y : (Σ k, ι k) → Ω) :
    ∏ k, Submodule.span F (Set.range fun i => y ⟨k, i⟩) =
      Submodule.span F (Set.range fun c : (∀ k, ι k) => ∏ k, y ⟨k, c k⟩) := by
  rw [Submodule.prod_span]
  congr 1
  ext z
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose c hc using hg
    exact ⟨c, Finset.prod_congr rfl fun k _ => hc k⟩
  · rintro ⟨c, rfl⟩
    exact ⟨fun k => y ⟨k, c k⟩, fun k => ⟨c k, rfl⟩, rfl⟩

theorem mapDomain_fst (a : (Σ k, ι k) →₀ ℕ) :
    ⇑(Finsupp.mapDomain Sigma.fst a) = Finsupp.weight (NumbersDVR.blockWeight ι) a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, Finsupp.coe_add, hf, hg]
  | single v n =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.single_eq_pi_single]
    ext k'
    simp [NumbersDVR.blockWeight, Pi.single_apply]

omit [DecidableEq K] in

theorem cone_monomial (y : (Σ k, ι k) → Ω) (a : (Σ k, ι k) →₀ ℕ) (c : F) :
    mConeMapOver F y (monomial a c) = monomial (a.mapDomain Sigma.fst) (aeval y (monomial a c)) := by
  have key : (monomial (a.mapDomain Sigma.fst) (1 : Ω) : MvPolynomial K Ω) =
      a.prod fun p n => (X p.1 : MvPolynomial K Ω) ^ n := by
    rw [← rename_monomial, monomial_eq, map_mul, rename_C, C_1, one_mul, map_finsuppProd]
    simp [rename_X]
  rw [mConeMapOver, aeval_monomial, aeval_monomial]
  rw [show (monomial (a.mapDomain Sigma.fst)) (algebraMap F Ω c * a.prod fun p n => y p ^ n) =
      C (algebraMap F Ω c * a.prod fun p n => y p ^ n) * monomial (a.mapDomain Sigma.fst) (1 : Ω) by
    rw [C_mul_monomial, mul_one], key]
  simp only [mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_mul, map_finsuppProd, map_pow]
  ring

theorem cone_of_homog [Fintype K] (y : (Σ k, ι k) → Ω) {g : MvPolynomial (Σ k, ι k) F} {d : K → ℕ}
    (hg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g d) :
    mConeMapOver F y g = monomial (Finsupp.equivFunOnFinite.symm d) (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hA : a.mapDomain Sigma.fst = Finsupp.equivFunOnFinite.symm d := by
    ext k
    rw [show (a.mapDomain Sigma.fst) k = _ from congrFun (mapDomain_fst a) k, hg (mem_support_iff.mp ha)]
    simp
  rw [cone_monomial, hA]

theorem mem_mIdealOver_iff [Fintype K] (y : (Σ k, ι k) → Ω) {g : MvPolynomial (Σ k, ι k) F} {d : K → ℕ}
    (hg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g d) :
    g ∈ mIdealOver F y ↔ aeval y g = 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mIdealOver, RingHom.mem_ker, cone_of_homog y hg, monomial_eq_zero]

theorem finrank_gradedPiece [Fintype K] (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    Module.finrank F (NumbersDVR.gradedPiece (mIdealOver F y) d) = Module.finrank F (vals F y d) := by
  set V := weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) d
  let P := mIdealOver F y
  let f₁ : V →ₗ[F] MvPolynomial (Σ k, ι k) F ⧸ P := (Ideal.Quotient.mkₐ F P).toLinearMap ∘ₗ V.subtype
  let f₂ : V →ₗ[F] Ω := (aeval y).toLinearMap ∘ₗ V.subtype
  have hr₁ : LinearMap.range f₁ = NumbersDVR.gradedPiece P d := by
    rw [NumbersDVR.gradedPiece, LinearMap.range_comp, Submodule.range_subtype]
  have hr₂ : LinearMap.range f₂ = vals F y d := by
    rw [vals, LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_mIdealOver_iff y ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hv)
  have e₁ := ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
    f₂.quotKerEquivRange).finrank_eq
  rw [hr₁, hr₂] at e₁
  exact e₁

theorem hilbFn_eq [Fintype K] (y : (Σ k, ι k) → Ω) (m : K → ℤ) (hm : ∀ k, 0 ≤ m k) :
    NumbersDVR.hilbFn (mIdealOver F y) m = (Module.finrank F (vals F y fun k => (m k).toNat) : ℤ) := by
  rw [NumbersDVR.hilbFn, if_pos hm, finrank_gradedPiece]

end Values

section Eventual

theorem eventuallyEq_mixedDiff {K' : Type} {n : ℕ} (bs : Fin n → K' → ℤ) {h₁ h₂ : (K' → ℤ) → ℤ}
    (h : h₁ =ᶠ[atTop] h₂) : NumbersDVR.mixedDiff bs h₁ =ᶠ[atTop] NumbersDVR.mixedDiff bs h₂ := by
  unfold NumbersDVR.mixedDiff
  generalize List.ofFn bs = l
  induction l with
  | nil => exact h
  | cons b l ih =>
    simp only [List.foldr_cons]
    have ht : Tendsto (fun m : K' → ℤ => m - b) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro c
      exact ⟨c + b, fun a ha => by simpa using sub_le_sub_right ha b⟩
    filter_upwards [ih, ht.eventually ih] with m h1 h2
    simp only [NumbersDVR.diffStep, h1, h2]

variable {K : Type}

def shiftDeg (D : Unit ⊕ K → ℤ) : K → ℤ := fun k => D (Sum.inr k) + D (Sum.inl ())

theorem mixedDiff_shift {n : ℕ} (μs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    NumbersDVR.mixedDiff (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (μs j)) (fun D => h (shiftDeg D)) =
      fun D => NumbersDVR.mixedDiff μs h (shiftDeg D) := by
  unfold NumbersDVR.mixedDiff
  have hl : List.ofFn (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (μs j)) =
      (List.ofFn μs).map (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit)) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn μs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih]
    funext D
    simp only [NumbersDVR.diffStep]
    have hs : shiftDeg (D - IndefiniteRowSideFullHecke.Kleiman2.pullDeg b) = shiftDeg D - b := by
      funext k
      simp only [shiftDeg, Pi.sub_apply, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
      ring
    rw [hs]

theorem eventually_shift_iff (f : (K → ℤ) → ℤ) (c : ℤ) :
    (∀ᶠ D in atTop, f (shiftDeg D) = c) ↔ ∀ᶠ m in atTop, f m = c := by
  constructor
  · intro h
    obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp h
    refine eventually_atTop.mpr ⟨shiftDeg D₀, fun m hm => ?_⟩
    let D : Unit ⊕ K → ℤ := Sum.elim (fun _ => D₀ (Sum.inl ())) (fun k => m k - D₀ (Sum.inl ()))
    have hD : D₀ ≤ D := by
      intro j
      rcases j with u | k
      · cases u
        exact le_rfl
      · have := hm k
        simp only [shiftDeg] at this
        show D₀ (Sum.inr k) ≤ m k - D₀ (Sum.inl ())
        omega
    have hψ : shiftDeg D = m := by
      funext k
      simp [shiftDeg, D]
    rw [← hψ]
    exact hD₀ D hD
  · intro h
    have ht : Tendsto (shiftDeg (K := K)) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨Sum.elim 0 b, fun a ha k => ?_⟩
      have h1 := ha (Sum.inl ())
      have h2 := ha (Sum.inr k)
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] at h1 h2
      simp only [shiftDeg]
      omega
    exact ht.eventually h

end Eventual

section Segre

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra F Ω]

theorem vals_segreJoin (y : (Σ k, ι k) → Ω) (m₀ : ℕ) (m : K → ℕ) :
    vals F (segreJoin y) (Sum.elim (fun _ => m₀) m) = vals F y (fun k => m k + m₀) := by
  have hS : ∀ u : Unit, vals F (segreJoin y) (Pi.single (Sum.inl u) 1) = ∏ k, vals F y (Pi.single k 1) := by
    intro u
    rw [vals_single]
    simp_rw [vals_single]
    rw [prod_span_blocks]
    rfl
  have hL : ∀ k, vals F (segreJoin y) (Pi.single (Sum.inr k) 1) = vals F y (Pi.single k 1) := by
    intro k
    rw [vals_single, vals_single]
    rfl
  rw [vals_eq_prod, vals_eq_prod, Fintype.prod_sum_type, Fintype.prod_unique]
  simp only [Sum.elim_inl, Sum.elim_inr, hS, hL, pow_add, Finset.prod_mul_distrib, Finset.prod_pow]
  ring

theorem hilbFn_segreJoin (y : (Σ k, ι k) → Ω) (D : Unit ⊕ K → ℤ) (hD : ∀ j, 0 ≤ D j) :
    NumbersDVR.hilbFn (mIdealOver F (segreJoin y)) D = NumbersDVR.hilbFn (mIdealOver F y) (shiftDeg D) := by
  rw [hilbFn_eq _ _ hD, hilbFn_eq y (shiftDeg D) (fun k => add_nonneg (hD _) (hD _))]
  have h1 : (fun j => (D j).toNat) =
      Sum.elim (fun _ => (D (Sum.inl ())).toNat) (fun k => (D (Sum.inr k)).toNat) := by
    funext j
    rcases j with u | k
    · cases u
      rfl
    · rfl
  have h2 : (fun k => (shiftDeg D k).toNat) = fun k => (D (Sum.inr k)).toNat + (D (Sum.inl ())).toNat := by
    funext k
    exact Int.toNat_add (hD _) (hD _)
  rw [h1, h2, vals_segreJoin]

end Segre

end SegreNum

open SegreNum in

theorem SegreNum.proof : SegreNum.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y _ n μs
  unfold NumbersDVR.intNum
  have hE : NumbersDVR.hilbFn (mIdealOver F (segreJoin y)) =ᶠ[atTop]
      fun D => NumbersDVR.hilbFn (mIdealOver F y) (shiftDeg D) := by
    filter_upwards [eventually_ge_atTop 0] with D hD
    exact hilbFn_segreJoin y D fun j => hD j
  have hM := eventuallyEq_mixedDiff (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (μs j)) hE
  rw [mixedDiff_shift] at hM
  refine FieldNumbers.Relabel.eventualValue_congr fun c => ?_
  rw [← eventually_shift_iff (NumbersDVR.mixedDiff μs (NumbersDVR.hilbFn (mIdealOver F y))) c]
  constructor
  · intro h
    filter_upwards [h, hM] with D h1 h2
    rw [← h2, h1]
  · intro h
    filter_upwards [h, hM] with D h1 h2
    rw [h2, h1]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
