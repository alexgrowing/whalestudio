import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem exists_adic_sum_of_finsets {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {Ix : Type} (c : Ix → R) (S : ℕ → Finset Ix) (hmono : Monotone S)
    (hS : ∀ n i, i ∉ S n → c i ∈ I ^ n) :
    ∃ a : R, ∀ n, ∀ T : Finset Ix, S n ⊆ T → a - ∑ i ∈ T, c i ∈ I ^ n := by
  classical
  have key : ∀ n, ∀ T : Finset Ix, S n ⊆ T → ∑ i ∈ T, c i - ∑ i ∈ S n, c i ∈ I ^ n := by
    intro n T hT
    rw [← Finset.sum_sdiff hT, add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => hS n i (Finset.mem_sdiff.mp hi).2
  have hsm : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    simp
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance
    (f := fun n => ∑ i ∈ S n, c i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact key m _ (hmono hmn))
  refine ⟨a, fun n T hT => ?_⟩
  have h1 := ha n
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := key n T hT
  have h3 := Ideal.add_mem _ h1 h2
  rw [← neg_mem_iff]
  convert h3 using 1
  ring

theorem exists_sumI_of_coeff {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {E : Type} [AddCommGroup E] [Module R E] {Jx : Type} [Fintype Jx] (g : Jx → E)
    {Ix : Type} (c : Ix → Jx → R) (h : ∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ I ^ n}.Finite) :
    ∃ s : E, GlobalTheory.UT.SumI I (fun i => ∑ k, c i k • g k) s := by
  classical
  have hmono : Monotone (fun n => (h n).toFinset) := by
    intro m n hmn i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hk => hi fun k => Ideal.pow_le_pow_right hmn (hk k)
  have hS : ∀ k n i, i ∉ (h n).toFinset → c i k ∈ I ^ n := by
    intro k n i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    exact hi k
  choose a ha using fun k =>
    exists_adic_sum_of_finsets I (fun i => c i k) (fun n => (h n).toFinset) hmono (hS k)
  have hg : ∀ k, g k ∈ Submodule.span R (Set.range g) := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  refine ⟨∑ k, a k • g k, Submodule.span R (Set.range g),
    Submodule.fg_span (Set.finite_range g),
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun i => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun n => ⟨(h n).toFinset, fun T hT => ?_⟩⟩
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← Finset.sum_smul, ← sub_smul]
  exact Submodule.smul_mem_smul (ha k n T hT) (hg k)

theorem exists_sumF_of_coeff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  intro R _ _ _ _ hc F _ _ Jx _ g Ix c h
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨s, hs⟩ := exists_sumI_of_coeff (maximalIdeal R) g c h
  refine ⟨s, ?_⟩
  have e : (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k)
      = fun i => ∑ k, c i k • g k := by
    funext i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def]
    rfl
  rw [e]
  exact hs

end GlobalTheory.Mum
