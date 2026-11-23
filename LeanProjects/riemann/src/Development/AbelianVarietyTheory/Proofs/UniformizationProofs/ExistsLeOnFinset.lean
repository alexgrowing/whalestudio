import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.AdicValSum

theorem nullV_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) : NullV v x := by
  classical
  intro q
  obtain ⟨S, hS⟩ := h q
  refine S.finite_toSet.subset fun i hi => ?_
  by_contra hiS
  have h1 := hS S subset_rfl
  have h2 := hS (insert i S) (Finset.subset_insert i S)
  have hx : x i = (s - ∑ j ∈ S, x j) - (s - ∑ j ∈ insert i S, x j) := by
    rw [Finset.sum_insert hiS]
    ring
  have h3 : (q : WithTop ℚ) ≤ v (x i) := by
    rw [hx]
    exact le_trans (le_min h1 h2) (AddValuation.map_sub v _ _)
  exact absurd hi (not_lt.mpr h3)

theorem exists_le_on_finset {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (t : Finset F) :
    ∃ c : ℚ, ∀ y ∈ t, (c : WithTop ℚ) ≤ v y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d : ℚ, (d : WithTop ℚ) ≤ v a := by
      by_cases htop : v a = ⊤
      · exact ⟨0, htop ▸ le_top⟩
      · exact ⟨(v a).untop htop, by rw [WithTop.coe_untop]⟩
    refine ⟨min c d, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_right c d)) hd
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_left c d)) (hc y hy)

theorem sumV_of_sumI {V : Type} [CommRing V] (I : Ideal V) {F : Type} [Field F] [Module V F] (φ : V → F)
    (hφ : ∀ (a : V) (y : F), a • y = φ a * y) (v : AddValuation F (WithTop ℚ))
    (hv : ∀ (n : ℕ) (a : V), a ∈ I ^ n → ((n : ℚ) : WithTop ℚ) ≤ v (φ a))
    {Ix : Type} {x : Ix → F} {s : F} (h : SumI I x s) : SumV v x s := by
  obtain ⟨N, hNfg, -, -, hconv⟩ := h
  obtain ⟨G, rfl⟩ := hNfg
  obtain ⟨c, hc⟩ := exists_le_on_finset v G
  have h0 : ∀ a : V, (0 : WithTop ℚ) ≤ v (φ a) := by
    intro a
    have := hv 0 a (by simp)
    simpa using this
  have hN : ∀ y ∈ Submodule.span V (G : Set F), (c : WithTop ℚ) ≤ v y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simp
    | add y z _ _ hy hz => exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
    | smul a y _ hy =>
      rw [hφ, AddValuation.map_mul]
      simpa using add_le_add (h0 a) hy
  have hIN : ∀ n : ℕ, ∀ z ∈ I ^ n • Submodule.span V (G : Set F), (((n : ℚ) + c : ℚ) : WithTop ℚ) ≤ v z := by
    intro n z hz
    refine Submodule.smul_induction_on hz (fun r hr y hy => ?_) (fun y z hy hz => ?_)
    · rw [hφ, AddValuation.map_mul, WithTop.coe_add]
      exact add_le_add (hv n r hr) (hN y hy)
    · exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
  intro q
  obtain ⟨S, hS⟩ := hconv ⌈q - c⌉₊
  refine ⟨S, fun T hT => le_trans ?_ (hIN _ _ (hS T hT))⟩
  have : q ≤ (⌈q - c⌉₊ : ℚ) + c := by linarith [Nat.le_ceil (q - c)]
  exact WithTop.coe_le_coe.mpr this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (x : Ix → F) (s : F), SumF (maximalIdeal V) F x s → SumV v x s ∧ NullV v x := by
  intro V _ _ _ ϖ hϖ F _ _ v hval Ix x s hsum
  letI : Module V F := Module.compHom F (algebraMap V (FractionRing V))
  have hI : SumI (maximalIdeal V) x s := hsum
  have hV : SumV v x s := by
    refine sumV_of_sumI (maximalIdeal V) (fun a => algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))
      (fun a y => Algebra.smul_def _ _) v ?_ hI
    intro n a ha
    by_cases ha0 : a = 0
    · subst ha0
      simp
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : ϖ ^ n ∣ ϖ ^ k := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      exact (Units.dvd_mul_left).mp ha
    have hnk : n ≤ k := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
    have hhv : HasVal ϖ (algebraMap V (FractionRing V) (↑u * ϖ ^ k)) (k : ℤ) :=
      ⟨u, by rw [map_mul, map_pow, zpow_natCast, mul_comm]⟩
    rw [hval _ _ hhv, WithTop.coe_le_coe]
    exact_mod_cast hnk
  exact ⟨hV, nullV_of_sumV hV⟩

end GlobalTheory.UT.AdicValSum
