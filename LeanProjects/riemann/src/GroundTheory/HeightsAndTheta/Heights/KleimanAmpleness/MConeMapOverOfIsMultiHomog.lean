import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTail
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (isMultiHomog_mul isMultiHomog_add isMultiHomog_X isMultiHomog_one)

namespace ResidueMap

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_sub {f g : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  exacts [hf m h k, hg m h k]

omit [Fintype K] in

theorem isMultiHomog_C (r : F) : IsMultiHomog (C r : MRingOver F ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  subst hm0
  simp

omit [Fintype K] in

theorem isMultiHomog_rename [DecidableEq K] (k : K) {f : MvPolynomial (ι k) F} {m : ℕ} (hf : f.IsHomogeneous m) :
    IsMultiHomog (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) f) (Pi.single k m) := by
  classical
  intro e he k'
  rw [support_rename_of_injective sigma_mk_injective] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  have hdeg : ∑ i, d i = m := by
    have h1 := hf (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simpa using h1
  by_cases hk : k' = k
  · subst hk
    rw [Pi.single_eq_same, ← hdeg]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply sigma_mk_injective d i
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact Finsupp.mapDomain_of_notMem_range _ _
      (by rintro ⟨j, hj⟩; exact hk (congrArg Sigma.fst hj).symm)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_rename_block {A : Type} [CommRing A] [Algebra F A] (z : (Σ k, ι k) → A) (k : K)
    (p : MvPolynomial (ι k) F) :
    aeval z (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) p) = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k) p := by
  rw [aeval_rename]; rfl

variable {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mConeMapOver_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : MRingOver F ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    mConeMapOver F y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p = ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_mIdealOver_iff (y : (Σ k, ι k) → Ω) {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mIdealOver F y ↔ aeval y g = 0 := by
  rw [mIdealOver, RingHom.mem_ker, mConeMapOver_of_isMultiHomog y hg]
  have hP : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  rw [mul_eq_zero, or_iff_left hP, MvPolynomial.C_eq_zero]

variable {K' : Type} [Field K'] [Algebra F K']

theorem vanish {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) (h : aeval y g = 0) : aeval y' g = 0 :=
  (mem_mIdealOver_iff y' hg).mp (hle ((mem_mIdealOver_iff y hg).mpr h))

theorem ne_zero_of {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hg' : aeval y' g ≠ 0) : aeval y g ≠ 0 :=
  fun h => hg' (vanish hle hg h)

theorem wd {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {f g f₂ g₂ : MRingOver F ι} {n n₂ : K → ℕ} (hf : IsMultiHomog f n) (hg : IsMultiHomog g n)
    (hf₂ : IsMultiHomog f₂ n₂) (hg₂ : IsMultiHomog g₂ n₂) (hg' : aeval y' g ≠ 0) (hg₂' : aeval y' g₂ ≠ 0)
    (h : aeval y f / aeval y g = aeval y f₂ / aeval y g₂) :
    aeval y' f / aeval y' g = aeval y' f₂ / aeval y' g₂ := by
  rw [div_eq_div_iff (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂')] at h
  rw [div_eq_div_iff hg' hg₂']
  have h2 : IsMultiHomog (f₂ * g) (n + n₂) := by
    rw [add_comm]; exact isMultiHomog_mul hf₂ hg
  have hp := isMultiHomog_sub (isMultiHomog_mul hf hg₂) h2
  have h0 := vanish hle hp (by rw [map_sub, map_mul, map_mul, h, sub_self])
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
  exact h0

variable (F) in

def fracSet (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → K') : Set Ω :=
  {x | ∃ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n ∧ IsMultiHomog g n ∧ aeval y' g ≠ 0 ∧
    x = aeval y f / aeval y g}

def locR {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y') :
    Subalgebra F Ω where
  carrier := fracSet F y y'
  mul_mem' := by
    rintro _ _ ⟨f, g, n, hf, hg, hg', rfl⟩ ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', rfl⟩
    exact ⟨f * f₂, g * g₂, n + n₂, isMultiHomog_mul hf hf₂, isMultiHomog_mul hg hg₂,
      by rw [map_mul]; exact mul_ne_zero hg' hg₂', by rw [map_mul, map_mul, div_mul_div_comm]⟩
  add_mem' := by
    rintro _ _ ⟨f, g, n, hf, hg, hg', rfl⟩ ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', rfl⟩
    have h2 : IsMultiHomog (f₂ * g) (n + n₂) := by
      rw [add_comm]; exact isMultiHomog_mul hf₂ hg
    refine ⟨f * g₂ + f₂ * g, g * g₂, n + n₂, isMultiHomog_add (isMultiHomog_mul hf hg₂) h2,
      isMultiHomog_mul hg hg₂, by rw [map_mul]; exact mul_ne_zero hg' hg₂', ?_⟩
    rw [div_add_div _ _ (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂'), map_add, map_mul, map_mul, map_mul]
    ring
  algebraMap_mem' r := ⟨C r, 1, 0, isMultiHomog_C r, isMultiHomog_one, by simp, by simp⟩

theorem exists_of_mem {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} {hle : mIdealOver F y ≤ mIdealOver F y'}
    {x : Ω} (hx : x ∈ locR hle) :
    ∃ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n ∧ IsMultiHomog g n ∧ aeval y' g ≠ 0 ∧
      x = aeval y f / aeval y g := hx

def sigmaFun {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) : K' :=
  aeval y' (exists_of_mem x.2).choose / aeval y' (exists_of_mem x.2).choose_spec.choose

theorem sigmaFun_eq {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) {f g : MRingOver F ι} {n : K → ℕ} (hf : IsMultiHomog f n) (hg : IsMultiHomog g n)
    (hg' : aeval y' g ≠ 0) (hx : (x : Ω) = aeval y f / aeval y g) :
    sigmaFun hle x = aeval y' f / aeval y' g := by
  obtain ⟨hf0, hg0, hg0', hx0⟩ := (exists_of_mem x.2).choose_spec.choose_spec.choose_spec
  exact wd hle hf0 hg0 hf hg hg0' hg' (hx0.symm.trans hx)

def sigma {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y') :
    locR hle →ₐ[F] K' where
  toFun := sigmaFun hle
  map_one' := by
    rw [sigmaFun_eq hle 1 isMultiHomog_one isMultiHomog_one (by simp) (by simp)]; simp
  map_zero' := by
    rw [sigmaFun_eq hle 0 (isMultiHomog_C (0 : F)) isMultiHomog_one (by simp) (by simp)]; simp
  map_mul' x x' := by
    obtain ⟨f, g, n, hf, hg, hg', hx⟩ := exists_of_mem x.2
    obtain ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', hx₂⟩ := exists_of_mem x'.2
    rw [sigmaFun_eq hle x hf hg hg' hx, sigmaFun_eq hle x' hf₂ hg₂ hg₂' hx₂,
      sigmaFun_eq hle (x * x') (isMultiHomog_mul hf hf₂) (isMultiHomog_mul hg hg₂)
        (by rw [map_mul]; exact mul_ne_zero hg' hg₂')
        (by rw [Subalgebra.coe_mul, hx, hx₂, map_mul, map_mul, div_mul_div_comm]),
      map_mul, map_mul, div_mul_div_comm]
  map_add' x x' := by
    obtain ⟨f, g, n, hf, hg, hg', hx⟩ := exists_of_mem x.2
    obtain ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', hx₂⟩ := exists_of_mem x'.2
    have h2 : IsMultiHomog (f₂ * g) (n + n₂) := by
      rw [add_comm]; exact isMultiHomog_mul hf₂ hg
    rw [sigmaFun_eq hle x hf hg hg' hx, sigmaFun_eq hle x' hf₂ hg₂ hg₂' hx₂,
      sigmaFun_eq hle (x + x') (isMultiHomog_add (isMultiHomog_mul hf hg₂) h2) (isMultiHomog_mul hg hg₂)
        (by rw [map_mul]; exact mul_ne_zero hg' hg₂')
        (by rw [Subalgebra.coe_add, hx, hx₂, div_add_div _ _ (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂'),
              map_add, map_mul, map_mul, map_mul]; ring),
      div_add_div _ _ hg' hg₂', map_add, map_mul, map_mul, map_mul]
    ring
  commutes' r := by
    show sigmaFun hle (algebraMap F (locR hle) r) = _
    rw [sigmaFun_eq hle _ (isMultiHomog_C r) isMultiHomog_one (by simp) (by simp)]; simp

theorem sigma_apply {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) : sigma hle x = sigmaFun hle x := rfl

theorem frac_spec {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {f g : MRingOver F ι} {n : K → ℕ} (hf : IsMultiHomog f n) (hg : IsMultiHomog g n)
    (hg' : aeval y' g ≠ 0) (x : Ω) (hx : x = aeval y f / aeval y g) :
    ∃ h : x ∈ locR hle, sigma hle ⟨x, h⟩ = aeval y' f / aeval y' g :=
  ⟨⟨f, g, n, hf, hg, hg', hx⟩, (sigma_apply hle _).trans (sigmaFun_eq hle _ hf hg hg' hx)⟩

end ResidueMap

open ResidueMap in

theorem ResidueMap.proof : ResidueMap.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' hle
  classical
  refine ⟨locR hle, sigma hle, ?_, ?_, ?_⟩
  · intro f g n hf hg hg'
    exact frac_spec hle hf hg hg' _ rfl
  · intro k f g m hf hg hg'
    have hg'' : aeval y' (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) g) ≠ 0 := by
      rwa [aeval_rename_block]
    obtain ⟨h, hσ⟩ := frac_spec hle (isMultiHomog_rename k hf) (isMultiHomog_rename k hg) hg''
      (aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g)
      (by rw [aeval_rename_block, aeval_rename_block])
    refine ⟨h, ?_⟩
    rw [hσ, aeval_rename_block, aeval_rename_block]
  · intro d hd z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨k, i⟩, rfl⟩ := hx
      obtain ⟨h, hσ⟩ := frac_spec hle (isMultiHomog_X (F := F) k i) (isMultiHomog_X (F := F) k (d k))
        (by rw [aeval_X]; exact hd k) _ (by rw [aeval_X, aeval_X])
      refine ⟨h, ?_⟩
      rw [hσ, aeval_X, aeval_X]
      exact Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    | algebraMap r =>
      refine ⟨Subalgebra.algebraMap_mem _ r, ?_⟩
      show sigma hle (algebraMap F (locR hle) r) ∈ _
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x x' _ _ ih ih' =>
      obtain ⟨h, hσ⟩ := ih
      obtain ⟨h', hσ'⟩ := ih'
      refine ⟨add_mem h h', ?_⟩
      rw [show (⟨x + x', add_mem h h'⟩ : locR hle) = ⟨x, h⟩ + ⟨x', h'⟩ from rfl, map_add]
      exact add_mem hσ hσ'
    | mul x x' _ _ ih ih' =>
      obtain ⟨h, hσ⟩ := ih
      obtain ⟨h', hσ'⟩ := ih'
      refine ⟨mul_mem h h', ?_⟩
      rw [show (⟨x * x', mul_mem h h'⟩ : locR hle) = ⟨x, h⟩ * ⟨x', h'⟩ from rfl, map_mul]
      exact mul_mem hσ hσ'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
