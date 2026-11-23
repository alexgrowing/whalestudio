import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.CompactAbelianCharacters

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.CompactAbelianFourier
open scoped NumberField.AdeleRing ComplexConjugate Pointwise

namespace GlobalTheory.CompanionTheory.AdelicFourier

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

theorem isClosed_vecLattice : IsClosed (vecLattice K ι : Set (ι → 𝔸[K])) := by
  have h : (vecLattice K ι : Set (ι → 𝔸[K])) =
      Set.univ.pi (fun _ => (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K])) := by
    ext x
    simp only [SetLike.mem_coe, mem_vecLattice, Set.mem_pi, Set.mem_univ, true_implies,
      AdeleRing.principalSubgroup, Subring.coe_toAddSubgroup, RingHom.coe_range, Set.mem_range]
    constructor
    · rintro ⟨ξ, rfl⟩ i
      exact ⟨ξ i, rfl⟩
    · intro hx
      choose ξ hξ using hx
      exact ⟨ξ, funext hξ⟩
  rw [h]
  exact isClosed_set_pi fun _ _ => isClosed_principalSubgroup K

instance : IsClosed (vecLattice K ι : Set (ι → 𝔸[K])) := isClosed_vecLattice

abbrev VecQuot (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι] : Type _ :=
  Multiplicative ((ι → 𝔸[K]) ⧸ vecLattice K ι)

def toQuot (x : ι → 𝔸[K]) : VecQuot K ι := Multiplicative.ofAdd (QuotientAddGroup.mk x)

theorem continuous_toQuot : Continuous (toQuot : (ι → 𝔸[K]) → VecQuot K ι) := by
  exact continuous_ofAdd.comp continuous_quot_mk

instance : CompactSpace ((ι → 𝔸[K]) ⧸ vecLattice K ι) := by
  refine ⟨?_⟩
  have hs : (Set.univ : Set ((ι → 𝔸[K]) ⧸ vecLattice K ι)) =
      (QuotientAddGroup.mk : (ι → 𝔸[K]) → _) '' closure (vecDomain K ι) := by
    symm
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨g, hg, -⟩ := existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) x
    refine ⟨g +ᵥ x, subset_closure hg, ?_⟩
    rw [QuotientAddGroup.eq]
    change -((g : ι → 𝔸[K]) + x) + x ∈ vecLattice K ι
    simpa using neg_mem g.2
  rw [hs]
  exact isCompact_closure_vecDomain.image continuous_quot_mk

instance : T2Space (VecQuot K ι) :=
  (inferInstance : T2Space ((ι → 𝔸[K]) ⧸ vecLattice K ι))

theorem toQuot_add (x y : ι → 𝔸[K]) : toQuot (x + y) = toQuot x * toQuot y := rfl

theorem toQuot_zero : toQuot (0 : ι → 𝔸[K]) = 1 := rfl

theorem toQuot_of_mem {x : ι → 𝔸[K]} (hx : x ∈ vecLattice K ι) : toQuot x = 1 := by
  unfold toQuot
  rw [(QuotientAddGroup.eq_zero_iff x).2 hx, ofAdd_zero]

theorem addChar_sum {A σ : Type*} [AddCommMonoid A] (φ : AddChar A Circle) (s : Finset σ)
    (v : σ → A) : φ (∑ i ∈ s, v i) = ∏ i ∈ s, φ (v i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem exists_pair_of_char (χ : VecQuot K ι →ₜ* Circle) :
    ∃ ξ : ι → K, ∀ x, χ (toQuot x) = adelicChar K (pair ξ x) := by
  classical
  let Φ : AddChar (ι → 𝔸[K]) Circle :=
    { toFun := fun x => χ (toQuot x)
      map_zero_eq_one' := by rw [toQuot_zero, map_one]
      map_add_eq_mul' := fun x y => by rw [toQuot_add, map_mul] }
  have hΦ : Continuous Φ := χ.continuous.comp continuous_toQuot
  have hi : ∀ i, ∃ ξ : K, ∀ a : 𝔸[K], Φ (Pi.single i a) = adelicChar K (algebraMap K 𝔸[K] ξ * a) := by
    intro i
    let χi : AddChar 𝔸[K] Circle :=
      { toFun := fun a => Φ (Pi.single i a)
        map_zero_eq_one' := by rw [Pi.single_zero, AddChar.map_zero_eq_one]
        map_add_eq_mul' := fun x y => by rw [Pi.single_add, AddChar.map_add_eq_mul] }
    have hχi : Continuous χi := hΦ.comp (continuous_pi fun j => by
      by_cases h : j = i
      · subst h; simp only [Pi.single_eq_same]; exact continuous_id
      · simpa [Pi.single_eq_of_ne h] using continuous_const)
    have hK : ∀ k : K, χi (algebraMap K 𝔸[K] k) = 1 := fun k => by
      have hm : (Pi.single i (algebraMap K 𝔸[K] k) : ι → 𝔸[K]) ∈ vecLattice K ι := by
        refine ⟨Pi.single i k, ?_⟩
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      show χ (toQuot _) = 1
      rw [toQuot_of_mem hm, map_one]
    obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul χi hχi hK
    exact ⟨ξ, hξ⟩
  choose ξ hξ using hi
  refine ⟨ξ, fun x => ?_⟩
  have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  show Φ x = _
  conv_lhs => rw [hx]
  rw [addChar_sum, pair, addChar_sum]
  exact Finset.prod_congr rfl fun i _ => hξ i (x i)

theorem continuous_descend {f : (ι → 𝔸[K]) → ℂ} (hc : Continuous f)
    (hper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) :
    ∃ φ : C(VecQuot K ι, ℂ), ∀ x, φ (toQuot x) = conj (f x) := by
  have hs : ∀ a b : ι → 𝔸[K], (QuotientAddGroup.leftRel (vecLattice K ι)) a b → f a = f b := by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have e := hper _ hab a
    have e2 : -a + b + a = b := by abel
    rw [e2] at e
    exact e.symm
  refine ⟨⟨fun q => conj (Quotient.liftOn' (Multiplicative.toAdd q) f hs), ?_⟩, fun x => rfl⟩
  exact Complex.continuous_conj.comp ((hc.quotient_liftOn' hs).comp continuous_toAdd)

theorem eq_zero_of_vecCoeff_eq_zero {f : (ι → 𝔸[K]) → ℂ} (hc : Continuous f)
    (hper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) (h0 : ∀ ξ, vecCoeff f ξ = 0) : f = 0 := by
  classical
  obtain ⟨C0, hC0⟩ := (isCompact_closure_vecDomain (K := K) (ι := ι)).exists_bound_of_continuousOn
    hc.continuousOn
  have hDfin : vecMeasure K ι (vecDomain K ι) < ⊤ := by
    rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top
  have hint : ∀ ψ : C(VecQuot K ι, ℂ),
      IntegrableOn (fun x => f x * ψ (toQuot x)) (vecDomain K ι) (vecMeasure K ι) := by
    intro ψ
    have hcψ : Continuous fun x => f x * ψ (toQuot x) := hc.mul (ψ.continuous.comp continuous_toQuot)
    obtain ⟨C, hC⟩ := (isCompact_closure_vecDomain (K := K) (ι := ι)).exists_bound_of_continuousOn
      hcψ.continuousOn
    exact Measure.integrableOn_of_bounded (M := C) hDfin.ne hcψ.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_vecDomain).2
        (Filter.Eventually.of_forall fun x hx => hC x (subset_closure hx)))
  set Λ : C(VecQuot K ι, ℂ) → ℂ := fun ψ => ∫ x in vecDomain K ι, f x * ψ (toQuot x) ∂vecMeasure K ι
    with hΛ
  have hΛchar : ∀ χ : VecQuot K ι →ₜ* Circle, Λ (charCM χ) = 0 := by
    intro χ
    obtain ⟨ξ, hξ⟩ := exists_pair_of_char χ
    have h1 := h0 (-ξ)
    have hp : ∀ x, -pair (-ξ) x = pair ξ x := by
      intro x
      simp [pair, Finset.sum_neg_distrib]
    simp only [vecCoeff, hp] at h1
    simp only [hΛ, charCM_apply, hξ]
    exact h1
  have hΛadd : ∀ ψ ψ' : C(VecQuot K ι, ℂ), Λ (ψ + ψ') = Λ ψ + Λ ψ' := by
    intro ψ ψ'
    simp only [hΛ, ContinuousMap.add_apply, mul_add]
    exact integral_add (hint ψ) (hint ψ')
  have hΛsmul : ∀ (c : ℂ) (ψ : C(VecQuot K ι, ℂ)), Λ (c • ψ) = c • Λ ψ := by
    intro c ψ
    simp only [hΛ, ContinuousMap.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hspan : ∀ ψ ∈ Submodule.span ℂ
      (Set.range (charCM : (VecQuot K ι →ₜ* Circle) → C(VecQuot K ι, ℂ))), Λ ψ = 0 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, rfl⟩ := hx
      exact hΛchar χ
    | zero => simp [hΛ]
    | add x y _ _ hx hy => rw [hΛadd, hx, hy, add_zero]
    | smul c x _ hx => rw [hΛsmul, hx, smul_zero]
  set C : ℝ := |C0| + 1 with hCdef
  have hCpos : 0 < C := by positivity
  have hbound : ∀ ψ : C(VecQuot K ι, ℂ), ‖Λ ψ‖ ≤ C * ‖ψ‖ := by
    intro ψ
    have h := norm_setIntegral_le_of_norm_le_const hDfin (C := C * ‖ψ‖)
      (f := fun x => f x * ψ (toQuot x)) (fun x hx => by
        rw [norm_mul]
        exact mul_le_mul ((hC0 x (subset_closure hx)).trans (by linarith [le_abs_self C0]))
          (ψ.norm_coe_le_norm _) (norm_nonneg _) hCpos.le)
    simpa [Measure.real, vecMeasure_vecDomain] using h
  obtain ⟨φ, hφ⟩ := continuous_descend hc hper
  have hΛφ : Λ φ = 0 := by
    have hmem : φ ∈ closure ((Submodule.span ℂ
        (Set.range (charCM : (VecQuot K ι →ₜ* Circle) → C(VecQuot K ι, ℂ))) : Set C(VecQuot K ι, ℂ))) := by
      rw [← Submodule.topologicalClosure_coe, span_charCM_dense]
      trivial
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
    obtain ⟨ψ, hψ, hd⟩ := Metric.mem_closure_iff.1 hmem (δ / C) (div_pos hδ hCpos)
    have e : Λ φ = Λ (φ - ψ) + Λ ψ := by rw [← hΛadd, sub_add_cancel]
    rw [e, hspan ψ hψ, add_zero, zero_add]
    calc ‖Λ (φ - ψ)‖ ≤ C * ‖φ - ψ‖ := hbound _
      _ ≤ C * (δ / C) := by
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hd.le hCpos.le
      _ = δ := by field_simp
  have hsq : ∫ x in vecDomain K ι, (Complex.normSq (f x) : ℂ) ∂vecMeasure K ι = 0 := by
    rw [← hΛφ]
    simp only [hΛ, hφ]
    congr 1
    funext x
    rw [Complex.mul_conj]
  have hsqR : ∫ x in vecDomain K ι, Complex.normSq (f x) ∂vecMeasure K ι = 0 := by
    have h3 : ((∫ x in vecDomain K ι, Complex.normSq (f x) ∂vecMeasure K ι : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      exact hsq
    exact_mod_cast h3
  have hint2 : IntegrableOn (fun x => Complex.normSq (f x)) (vecDomain K ι) (vecMeasure K ι) := by
    refine IntegrableOn.congr_fun (f := fun x => ‖f x * φ (toQuot x)‖) (hint φ).norm
      (fun x _ => ?_) measurableSet_vecDomain
    dsimp only
    rw [hφ, Complex.mul_conj, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  have hae : (fun x => Complex.normSq (f x)) =ᵐ[(vecMeasure K ι).restrict (vecDomain K ι)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _) hint2).1 hsqR
  set U : Set (ι → 𝔸[K]) := {x | f x ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUD : vecMeasure K ι (U ∩ vecDomain K ι) = 0 := by
    have h2 := ae_iff.1 hae
    rw [Measure.restrict_apply' measurableSet_vecDomain] at h2
    convert h2 using 2
    ext x
    simp [hU, Complex.normSq_eq_zero]
  have hinv : ∀ g : vecLattice K ι, g +ᵥ U = U := by
    intro g
    ext x
    rw [Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show f ((g : ι → 𝔸[K]) + y) ≠ 0
      rw [hper _ g.2]
      exact hy
    · intro hx
      refine ⟨-(g : ι → 𝔸[K]) + x, ?_, ?_⟩
      · show f (-(g : ι → 𝔸[K]) + x) ≠ 0
        rw [hper _ (neg_mem g.2)]
        exact hx
      · show (g : ι → 𝔸[K]) + (-(g : ι → 𝔸[K]) + x) = x
        abel
  have hU0 : vecMeasure K ι U = 0 :=
    isAddFundamentalDomain_vecDomain.measure_zero_of_invariant U hinv hUD
  have hUe : U = ∅ := (hUo.measure_eq_zero_iff (vecMeasure K ι)).1 hU0
  funext x
  by_contra hx
  have hxU : x ∈ U := hx
  rw [hUe] at hxU
  exact hxU

end GlobalTheory.CompanionTheory.AdelicFourier
