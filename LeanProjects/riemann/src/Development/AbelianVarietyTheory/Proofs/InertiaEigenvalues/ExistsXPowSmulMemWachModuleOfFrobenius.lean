import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapConstantCoeffEqOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000

namespace GlobalTheory.NL.DenomStep

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem mem_N_of_jD (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (h1 : p1et W E T)
    (h6 : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (x : W.DD T) (hx : E.jD T x ∈ NAinf W E T) : x ∈ W.N T := by
  obtain ⟨⟨r, b, hbN, hbA, hbW⟩, -⟩ := h1

  have hNA : ∀ z ∈ NAinf W E T, ∃ β : Fin r → RA, z = ∑ j, inclR (β j) • E.jD T (b j) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hxN, rfl⟩ := hz
      obtain ⟨α, hα, -⟩ := hbA x hxN
      refine ⟨fun j => a * E.io (α j), ?_⟩
      rw [hα, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [GlobalTheory.NL.FrobDenom.jD_smulA, smul_smul, map_mul]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨β, rfl⟩ := hz
      obtain ⟨γ, rfl⟩ := hw
      refine ⟨β + γ, ?_⟩
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, map_add, add_smul]
    | smul c z _ hz =>
      obtain ⟨β, rfl⟩ := hz
      refine ⟨c • β, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, smul_assoc]

  have hDE : ∀ y : W.DD T, ∃ μ : Fin r → W.EE, y = ∑ j, μ j • b j := by
    intro y
    refine (W.N_base T hT).inductionOn y _ ⟨0, by simp⟩ ?_ ?_ ?_
    · intro z
      obtain ⟨α, hα, -⟩ := hbA z z.2
      refine ⟨fun j => algebraMap _ W.EE (α j), ?_⟩
      simp only [Submodule.subtype_apply, algebraMap_smul]
      exact hα
    · rintro e y ⟨μ, rfl⟩
      exact ⟨e • μ, by simp [Finset.smul_sum, smul_smul]⟩
    · rintro y y' ⟨μ, rfl⟩ ⟨μ', rfl⟩
      exact ⟨μ + μ', by simp [add_smul, Finset.sum_add_distrib]⟩
  obtain ⟨β, hβ⟩ := hNA _ hx
  obtain ⟨μ, rfl⟩ := hDE x
  have hj : E.jD T (∑ j, μ j • b j) = ∑ j, E.ioE (μ j) • E.jD T (b j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => E.jD_smul T _ _
  obtain ⟨c, -, hc⟩ := hbW (E.jD T (∑ j, μ j • b j))
  have e1 := hc (fun j => E.ioE (μ j)) hj
  have e2 := hc (fun j => inclR (β j)) hβ
  have hμ : ∀ j, ∃ a : LetA O n, algebraMap _ W.EE a = μ j := fun j =>
    h6 (μ j) ⟨β j, (congrFun e2 j).trans (congrFun e1 j).symm⟩
  choose a ha using hμ
  have : ∑ j, μ j • b j = ∑ j, a j • b j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, algebraMap_smul]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbN j)

end Generic

end GlobalTheory.NL.DenomStep

namespace GlobalTheory.NL.DenomStep

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem of_tie (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (hF : ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T →
      ∀ b : TW RW T, TWmap φR T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ,
        TensorProduct.map (LinearMap.mulLeft O
          (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
          TAinf inclR T)
    (hP1 : p1et W E T ∧ wachInfiniteLevel W E T)
    (h6 : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (M : ℕ) (m : W.DD T) (hm : W.φD T m - m ∈ invN W T (W.Q ^ M)) :
    ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  have hy : ((Multiset.replicate M 0).map fun j => (W.φA ^ j) W.Q).prod • (W.φD T m - m) ∈
      W.N T := by
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hm
  have hb : TWmap φR T (E.jD T m) - E.jD T m = E.jD T (W.φD T m - m) := by
    rw [map_sub, E.jD_φ]
  obtain ⟨a, ha⟩ := hF _ _ hy _ hb 0 (fun j hj => (Multiset.eq_of_mem_replicate hj).le)
  rw [Finset.prod_range_one, pow_zero, GlobalTheory.NL.SandArb.map_mulLeft] at ha
  obtain ⟨h1, k, hk, -⟩ := hP1
  have hz := hk _ ha
  refine ⟨k + a, mem_N_of_jD E T hT h1 h6 _ ?_⟩
  rw [GlobalTheory.NL.FrobDenom.jD_smulA, map_pow, map_pow, pow_add, mul_smul]
  exact hz

end Generic

set_option synthInstance.maxHeartbeats 200000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  intro D HW F l _ K s LL h W T hT M m hm
  exact of_tie ((F l).E K s LL h).tie T hT (GlobalTheory.NL.FrobDenom.main D HW F l K s LL h T hT)
    (GlobalTheory.NL.NygaardExtension.main D HW F l K s LL h T hT) (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.1 M m hm

end GlobalTheory.NL.DenomStep
