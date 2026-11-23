import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFormsExist
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_vertdiv_commensurable

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

def Pair (x : (Σ k, ι k) → Ω) (c : K → ℤ) (u : Ω) (f g : MRing ι O) : Prop :=
  (∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ (fun k => (bf k : ℤ) - bg k) = c) ∧
    aeval x f = u * aeval x g

theorem cross {x : (Σ k, ι k) → Ω} {c : K → ℤ} {u : Ω} {f g f' g' : MRing ι O}
    (h : Pair x c u f g) (h' : Pair x c u f' g') : f * g' - f' * g ∈ pointIdeal O x := by
  obtain ⟨⟨bf, bg, hf, hg, hd⟩, hv⟩ := h
  obtain ⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩ := h'
  have he : bf + bg' = bf' + bg := by
    funext k
    have h1 := congrFun hd k
    have h2 := congrFun hd' k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg') := IsWeightedHomogeneous.mul hf hg'
  have h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg') := by
    rw [he]; exact IsWeightedHomogeneous.mul hf' hg
  refine GenericProjClosureDivisor.mem_of_homog (b := bf + bg') ?_ ?_
  · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  · rw [map_sub, map_mul, map_mul, hv, hv']
    ring

omit [∀ k, Fintype (ι k)] in
theorem mono_homog (s : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, X ⟨k, s k⟩ ^ e k : MRing ι O) e := by
  have he : e = ∑ k, e k • blockWeight ι ⟨k, s k⟩ := by
    ext j
    simp [blockWeight, Pi.single_apply]
  unfold IsMultiHomog
  conv => enter [3]; rw [he]
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X O _ _).pow _

theorem product_powers_not_mem_prime {A : Type} [CommRing A] {W : Ideal A} (hW : W.IsPrime) {c : A} (hc : c ∉ W) (y : K → A)
    (hy : ∀ k, y k ∉ W) (n : ℕ) (e : K → ℕ) : c ^ n * ∏ k, y k ^ e k ∉ W := by
  intro hf
  rcases hW.mem_or_mem hf with h3 | h3
  · exact hc (hW.mem_of_pow_mem n h3)
  · obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 h3
    exact hy k (hW.mem_of_pow_mem (e k) hk)

theorem zpow_aux (y : K → Ω) (hy : ∀ k, y k ≠ 0) (b b' : K → ℤ) (p q : K → ℕ)
    (h : ∀ k, b k + q k = b' k + p k) :
    (∏ k, y k ^ b k) * ∏ k, y k ^ q k = (∏ k, y k ^ b' k) * ∏ k, y k ^ p k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k), h k]

theorem mul_eq_one_of_covolume_identity {m m' t D P Q r u : Ω} (hm : m' ≠ 0) (h : t * m = r * (u * m')) (hb : m * Q = m' * P) :
    t * (D * P) = u * (r * D * Q) := by
  apply mul_left_cancel₀ hm
  linear_combination D * Q * h - D * t * hb

omit [∀ k, Fintype (ι k)] in
theorem pair_num {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} {s : ∀ k, ι k} (hs : mseg x s ≠ 0)
    {W : Ideal (MRing ι O)} (hW : W.IsPrime) (hϖ : (C ϖ : MRing ι O) ∉ W)
    (hX : ∀ k, (X ⟨k, s k⟩ : MRing ι O) ∉ W) {n : ℕ} {r : Ω} (hr : r ∈ chartRing O (mseg x) s)
    (h : algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W := by
  obtain ⟨d, F, hF, eF⟩ := A_forms_exist.chartRing_le_fracs x s hs hr
  have hx : ∀ k, x ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  have hm : chartMon x s b' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  obtain ⟨p, hp⟩ : ∃ p : K → ℕ, ∀ k, p k = (b k - b' k).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : K → ℕ, ∀ k, q k = (b' k - b k).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ k, b k + q k = b' k + p k := fun k => by
    have e1 := hp k
    have e2 := hq k
    omega
  have hb : chartMon x s b * ∏ k, x ⟨k, s k⟩ ^ q k = chartMon x s b' * ∏ k, x ⟨k, s k⟩ ^ p k :=
    zpow_aux (fun k => x ⟨k, s k⟩) hx b b' p q hpq
  have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
    rw [← map_pow]
    exact isWeightedHomogeneous_C _ _
  have h1 : IsMultiHomog (C ϖ ^ n * ∏ k, X ⟨k, s k⟩ ^ (d + p) k : MRing ι O) (0 + (d + p)) :=
    IsWeightedHomogeneous.mul h0 (mono_homog s (d + p))
  have h2 : IsMultiHomog (F * ∏ k, X ⟨k, s k⟩ ^ q k : MRing ι O) (d + q) :=
    IsWeightedHomogeneous.mul hF (mono_homog s q)
  refine ⟨_, _, ⟨⟨_, _, h1, h2, ?_⟩, ?_⟩, product_powers_not_mem_prime hW hϖ (fun k => X ⟨k, s k⟩) hX n (d + p)⟩
  · funext k
    have e1 := hpq k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C, eF, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    exact mul_eq_one_of_covolume_identity hm h hb

theorem pair_at {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} (hu : u ≠ 0)
    (H : ∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b)
    (W : Ideal (MRing ι O)) (hW : W.IsPrime) (hPW : pointIdeal O x ≤ W) (hrel : IsRelevant W)
    (hϖ : (C ϖ : MRing ι O) ∉ W) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W ∧ g ∉ W := by
  choose s hX using hrel
  have hs : mseg x s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h0 => hX k (hPW ?_)
    exact GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0])
  obtain ⟨⟨n, r, hr, h⟩, n', r', hr', h'⟩ := H s hs
  obtain ⟨f, g, hp, hf⟩ := pair_num hs hW hϖ hX hr h
  have h'' : algebraMap O Ω ϖ ^ n' * chartMon x s b' = r' * (u⁻¹ * chartMon x s b) := by
    apply mul_left_cancel₀ hu
    rw [mul_left_comm r', ← mul_assoc u u⁻¹, mul_inv_cancel₀ hu, one_mul, ← h']
    ring
  obtain ⟨g', f', ⟨⟨bg, bf, hg1, hf1, hd⟩, hv⟩, hg'⟩ := pair_num hs hW hϖ hX hr' h''
  have hp' : Pair x (b - b') u f' g' := by
    refine ⟨⟨bf, bg, hf1, hg1, ?_⟩, ?_⟩
    · funext k
      have h1 := congrFun hd k
      simp only [Pi.sub_apply] at h1 ⊢
      omega
    · rw [hv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  refine ⟨f, g, hp, hf, fun hg => ?_⟩
  have h1 := W.add_mem (hPW (cross hp hp')) (W.mul_mem_left f' hg)
  rw [sub_add_cancel] at h1
  exact (hW.mem_or_mem h1).elim hf hg'

end PositivityTheory.Xgn.A_vertdiv_commensurable

theorem PositivityTheory.Xgn.t_vertdiv_commensurable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM b b' u hu H
  have hϖP : (C ϖ : MRing ι O) ∉ pointIdeal O x := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := hm
    rw [hM.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  obtain ⟨f, g, hp, hf, hg⟩ := A_vertdiv_commensurable.pair_at hu H _ hM.multiProj.isPrime le_rfl
    hM.multiProj.relevant hϖP
  refine ⟨f, g, IsVerticalDivisor.of_unit_off_special hp.1 hf hg fun W hW hPW hrel hϖW => ?_, hp.2⟩
  obtain ⟨f', g', hp', hf', hg'⟩ := A_vertdiv_commensurable.pair_at hu H W hW hPW hrel hϖW
  refine ⟨g', f', hg', hf', ?_⟩
  rw [mul_comm g' f]
  exact A_vertdiv_commensurable.cross hp hp'
