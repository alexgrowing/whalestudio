import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg restrictChart)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullExists

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => c k
  | .inr k => s (.inr k)

def secondChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k := fun k => s (.inr k)

theorem restrictChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    restrictChart (mixChart c s) = c := rfl

theorem secondChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    secondChart (mixChart c s) = secondChart s := rfl

theorem mseg_joinCoord {F : Type*} [CommMonoid F] (x : (Σ k, ι k) → F) (z : (Σ k, ι' k) → F)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (secondChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

end Charts

section Pull

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω₁}

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (secondChart s) := by
  rw [bcCoord, mseg_joinCoord]
  simp [mseg, map_prod]

theorem first_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg x (restrictChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem second_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg z (secondChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem ratio_first {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    (c : ∀ k, ι k) :
    algebraMap Ω Ω₁ (mseg x c / mseg x (restrictChart s)) ∈
      chartRing O (mseg (bcCoord x z)) s := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) s (mixChart c s)
  rw [mseg_bcCoord x z (mixChart c s), mseg_bcCoord x z s, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_right _ _ (second_ne_zero hs), ← map_div₀] at h
  exact h

theorem ratio_second {s t : ∀ k : K ⊕ K', Sum.elim ι ι' k} (ht : mseg (bcCoord x z) t ≠ 0) :
    mseg z (secondChart s) / mseg z (secondChart t) ∈ chartRing O (mseg (bcCoord x z)) t := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (mixChart (restrictChart t) s)
  rw [mseg_bcCoord x z (mixChart (restrictChart t) s), mseg_bcCoord x z t, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_left _ _
      ((map_ne_zero (algebraMap Ω Ω₁)).2 (first_ne_zero ht))] at h
  exact h

theorem map_mem_chartRing {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    {a : Ω} (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (bcCoord x z)) s).comap (IsScalarTower.toAlgHom O Ω Ω₁) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact ratio_first hs c
  exact hle ha

variable {N : ℕ} {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω₁ V₁]
  [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

def pullFam (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup V₁ := fun s =>
  spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))

theorem isLatFamily_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁) :
    IsLatFamily O (bcCoord x z) (pullFam x z E bc) := by
  refine ⟨fun s _ a ha v hv => LocFreeBC.smul_mem_spanOver _ _ ha hv,
    fun s t hs ht v hv => ?_⟩
  have hf : mseg (bcCoord x z) s / mseg (bcCoord x z) t ∈ chartRing O (mseg (bcCoord x z)) t :=
    div_mem_chartRing _ t s
  have hst : ∀ a ∈ chartRing O (mseg (bcCoord x z)) t, ∀ e ∈ pullFam x z E bc t,
      a • e ∈ pullFam x z E bc t := fun a ha e he => LocFreeBC.smul_mem_spanOver _ _ ha he
  have hfac : mseg (bcCoord x z) s / mseg (bcCoord x z) t =
      algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) *
        (mseg z (secondChart s) / mseg z (secondChart t)) := by
    rw [mseg_bcCoord x z s, mseg_bcCoord x z t, map_div₀, mul_div_mul_comm]
  change v ∈ AddSubgroup.closure _ at hv
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hv
    obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (mseg (bcCoord x z)) s t hs ha
    obtain ⟨m₂, hm₂⟩ := E.overlap _ _ (first_ne_zero hs) (first_ne_zero ht) e he
    refine ⟨m₁ + m₂, AddSubgroup.subset_closure ⟨_, mul_mem hm₁ (pow_mem
      (ratio_second (s := s) ht) m₂), _, ⟨_, hm₂, rfl⟩, ?_⟩⟩
    rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m₂) (bc e), smul_smul, smul_smul]
    congr 1
    rw [pow_add, map_pow]
    nth_rw 2 [hfac]
    rw [mul_pow]
    ring
  | zero => exact ⟨0, by simp⟩
  | add v w _ _ hv hw => exact LocFreeBC.loc_add _ _ hst hf hv hw
  | neg v _ hv =>
    obtain ⟨n, hn⟩ := hv
    exact ⟨n, by simpa using neg_mem hn⟩

theorem locFree_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁)
    (hbc : IsBaseChange Ω₁ bc) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (bcCoord x z) s ≠ 0) :
    LocFree (chartRing O (mseg (bcCoord x z)) s) N (pullFam x z E bc s) := by
  classical
  exact LocFreeBC.locFree_baseChange _ _ (fun _ ha => map_mem_chartRing hs ha) bc hbc N _
    (((BundleOfFamily.main O Ω K ι x N V).2 E).2 _ (first_ne_zero hs))

theorem exists_pullBC [IsDomain O] [IsDiscreteValuationRing O] (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  classical
  obtain ⟨EB, hEB⟩ := (BundleOfFamily.main O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1
    (pullFam x z E bc) (isLatFamily_pullFam E bc) (locFree_pullFam E bc hbc)
  refine ⟨EB, fun s hs => ?_⟩
  rw [hEB s hs]
  refine congrArg AddSubgroup.closure (Set.ext fun v => ?_)
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

end Pull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_,
    fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc => exists_pullBC E bc hbc⟩
  exact exists_pullBC (Ω₁ := Ω) (V₁ := V) (z := z) E LinearMap.id
    (IsBaseChange.ofEquiv (LinearEquiv.refl Ω V))

end GlobalTheory.CompanionTheory.Ar.Num.PullExists
