import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_coherent_gens

theorem mem_spanOver {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, one_mem R, e, he, (one_smul Ω e).symm⟩

theorem spanOver_le {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hS : ∀ e ∈ S, e ∈ L) : spanOver R S ≤ L := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hL a ha e (hS e he)

theorem spanOver_mono {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S T : Set E} (h : S ⊆ T) : spanOver R S ≤ spanOver R T := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem transition {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) {c t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) (a : K → ℤ) (m : ℕ) (hm : ∀ k, (m : ℤ) ≤ a k) :
    ∃ r ∈ chartRing o (mseg x) t,
      (chartMon x t a)⁻¹ * chartMon x c a = r * (mseg x c / mseg x t) ^ m := by
  refine ⟨∏ k, (x ⟨k, c k⟩ / x ⟨k, t k⟩) ^ (a k - m).toNat,
    prod_mem fun k _ => pow_mem (TwistedDualGensExist.ratio_mem (O := o) x ht k (c k)) _, ?_⟩
  simp only [chartMon, mseg]
  rw [← Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h : a k = (((a k - m).toNat + m : ℕ) : ℤ) := by
    have := hm k
    push_cast
    omega
  rw [← pow_add, ← zpow_natCast, ← h, div_zpow, div_eq_inv_mul]

end PositivityTheory.Xgn.A_coherent_gens

theorem PositivityTheory.Xgn.t_coherent_gens : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (V : Type) [AddCommGroup V] [Module Ω V] (Γ : (∀ k, ι k) → AddSubgroup V), IsLatFamily O x Γ → (∀ c, mseg x c ≠ 0 → ∃ S : Finset V, Γ c = spanOver (chartRing O (mseg x) c) (S : Set V)) → ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a → ∃ (M : ℕ) (v : Fin M → V), ∀ c, mseg x c ≠ 0 → Γ c = spanOver (chartRing O (mseg x) c) (Set.range fun j => (chartMon x c a)⁻¹ • v j) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x V _ _ Γ ⟨hst, hov⟩ hfg
  choose! S hS using hfg
  let I := Σ c : {c : ∀ k, ι k // mseg x c ≠ 0}, S c.1
  have hmem : ∀ i : I, (i.2 : V) ∈ Γ i.1.1 := fun i => by
    rw [hS _ i.1.2]
    exact A_coherent_gens.mem_spanOver _ i.2.2
  have hex : ∀ p : I × {c : ∀ k, ι k // mseg x c ≠ 0}, ∃ m : ℕ,
      (mseg x p.1.1.1 / mseg x p.2.1) ^ m • (p.1.2 : V) ∈ Γ p.2.1 :=
    fun p => hov _ _ p.1.1.2 p.2.2 _ (hmem p.1)
  choose m hm using hex
  refine ⟨fun _ => ((∑ p, m p : ℕ) : ℤ), fun a ha => ?_⟩
  let e := Fintype.equivFin I
  refine ⟨_, fun j => chartMon x (e.symm j).1.1 a • ((e.symm j).2 : V), fun t ht => ?_⟩
  apply le_antisymm
  · rw [hS t ht]
    refine A_coherent_gens.spanOver_mono _ fun w hw => ⟨e ⟨⟨t, ht⟩, ⟨w, hw⟩⟩, ?_⟩
    have hne : chartMon x t a ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ ((Finset.prod_ne_zero_iff.1 ht) k (Finset.mem_univ _))
    dsimp only
    rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · refine A_coherent_gens.spanOver_le _ (hst t ht) ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr, heq⟩ := A_coherent_gens.transition (o := O) x (c := (e.symm j).1.1) ht a
      (m (e.symm j, ⟨t, ht⟩)) fun k => le_trans (by
        exact Nat.cast_le.2
          (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))) (ha k)
    dsimp only
    rw [smul_smul, heq, mul_smul]
    exact hst t ht r hr _ (hm (e.symm j, ⟨t, ht⟩))
