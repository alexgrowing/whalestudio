import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOfFamily
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullLine
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_exists
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)
open PositivityTheory.Xgn.A_pull_line (comb mseg_join map_mem)
open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC (smul_mem_spanOver mem_spanOver_of_mem locFree_baseChange)

theorem pow_mul_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
    {ι : K → Type} (x : (Σ k, ι k) → Ω) (s t : ∀ k, ι k) (hs : mseg x s ≠ 0) (a : Ω)
    (ha : a ∈ chartRing O (mseg x) s) :
    ∃ n : ℕ, (mseg x s / mseg x t) ^ n * a ∈ chartRing O (mseg x) t := by
  have hq := div_mem_chartRing (o := O) (mseg x) t s
  unfold chartRing at ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have h : (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t := by
      rw [pow_one, mul_comm, div_mul_div_cancel₀ hs]
    have h2 := div_mem_chartRing (o := O) (mseg x) t u
    rw [← h] at h2
    exact h2
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : (mseg x s / mseg x t) ^ (m + n) * (a + b) =
        (mseg x s / mseg x t) ^ n * ((mseg x s / mseg x t) ^ m * a) +
        (mseg x s / mseg x t) ^ m * ((mseg x s / mseg x t) ^ n * b) := by ring
    rw [h]
    exact add_mem (mul_mem (pow_mem hq n) hm) (mul_mem (pow_mem hq m) hn)
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : (mseg x s / mseg x t) ^ (m + n) * (a * b) =
        ((mseg x s / mseg x t) ^ m * a) * ((mseg x s / mseg x t) ^ n * b) := by ring
    rw [h]
    exact mul_mem hm hn

theorem closure_eq {O Ω₁ V V₁ : Type} [CommRing O] [Field Ω₁] [Algebra O Ω₁] [AddCommGroup V₁]
    [Module Ω₁ V₁] (R : Subalgebra O Ω₁) (f : V → V₁) (L : Set V) :
    spanOver R (f '' L) = AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • f e} := by
  unfold spanOver
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

theorem main (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type)
    [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V)
    (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type)
    [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁)
    (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, ∀ s, mseg (bcCoord x z) s ≠ 0 →
      EB.lat s = AddSubgroup.closure
        {v | ∃ a ∈ chartRing O (mseg (bcCoord x z)) s, ∃ e ∈ E.lat (restrictChart s), v = a • bc e} := by
  let φ : Ω →ₐ[O] Ω₁ := IsScalarTower.toAlgHom O Ω Ω₁
  obtain ⟨hfam, hloc⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).2 E
  have hj : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) :=
    fun s => mseg_join φ x z s
  have hne : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (bcCoord x z) s ≠ 0 →
      mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    rw [hj, h, map_zero, zero_mul] at hs
    exact hs rfl
  suffices hov : IsLatFamily O (bcCoord x z) (fun s =>
      spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))) by
    obtain ⟨EB, hEB⟩ :=
      (PositivityTheory.Xgn.t_bundle_of_family O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1 _ hov
        (fun s hs => locFree_baseChange _ _ (fun a ha => map_mem φ x z s hs a ha) bc hbc N _
          (hloc _ (hne s hs)))
    exact ⟨EB, fun s hs => (hEB s hs).trans (closure_eq _ _ _)⟩
  refine ⟨fun s _ a ha v hv => smul_mem_spanOver _ _ ha hv, ?_⟩
  intro s t hs ht v hv
  beta_reduce at hv ⊢
  have hq := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t s
  set q := mseg (bcCoord x z) s / mseg (bcCoord x z) t with hqdef
  rw [spanOver] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
    obtain ⟨n, hn⟩ := pow_mul_mem (bcCoord x z) s t hs a ha
    obtain ⟨m, hm⟩ := hfam.2 _ _ (hne s hs) (hne t ht) e he
    have hw := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (comb (restrictChart t) s)
    set w := mseg (bcCoord x z) (comb (restrictChart t) s) / mseg (bcCoord x z) t with hwdef
    have ht' : algebraMap Ω Ω₁ (mseg x (restrictChart t)) ≠ 0 := (map_ne_zero _).mpr (hne t ht)
    have hqw : q = w * algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) := by
      have h1 : mseg (bcCoord x z) (comb (restrictChart t) s) =
          algebraMap Ω Ω₁ (mseg x (restrictChart t)) * mseg z (fun k => s (.inr k)) := hj _
      rw [hqdef, hwdef, h1, hj s, map_div₀]
      field_simp
    refine ⟨n + m, ?_⟩
    have h : q ^ (n + m) • a • bc e = (q ^ n * a * w ^ m) •
        bc ((mseg x (restrictChart s) / mseg x (restrictChart t)) ^ m • e) := by
      rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m : Ω), smul_smul, smul_smul, map_pow, pow_add,
        mul_assoc (q ^ n * a), ← mul_pow, ← hqw]
      congr 1
      ring
    rw [h]
    exact smul_mem_spanOver _ _ (mul_mem hn (pow_mem hw m)) (mem_spanOver_of_mem _ ⟨_, hm, rfl⟩)
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : q ^ (m + n) • (a + b) = q ^ n • q ^ m • a + q ^ m • q ^ n • b := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [h]
    exact add_mem (smul_mem_spanOver _ _ (pow_mem hq n) hm) (smul_mem_spanOver _ _ (pow_mem hq m) hn)
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

end PositivityTheory.Xgn.A_pull_exists

theorem PositivityTheory.Xgn.t_pull_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_, fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc =>
    PositivityTheory.Xgn.A_pull_exists.main O Ω K ι x N V E Ω₁ K' ι' z V₁ bc hbc⟩
  exact PositivityTheory.Xgn.A_pull_exists.main O Ω K ι x N V E Ω K' ι' z V (LinearEquiv.refl Ω V).toLinearMap
    (IsBaseChange.ofEquiv _)
