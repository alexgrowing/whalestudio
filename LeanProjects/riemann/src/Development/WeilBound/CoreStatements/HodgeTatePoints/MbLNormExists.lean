import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
import Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpanStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLMorph
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormChart
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaledStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMaxStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalizationStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentreUnique
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFracExt
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFiniteExt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompatStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section
namespace PositivityTheory.HtPt.Mb.LNormExists.NormEx

instance isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) :=
  (LocalSubring.range (genMap ξ p)).isLocalRing

theorem int_trans {o K : Type} [CommRing o] [Field K] [Algebra o K] (A B : Subalgebra o K)
    (hAB : ∀ a ∈ A, a ∈ B) (hB : ∀ b ∈ B, IsIntegral A b) (a : K) (ha : IsIntegral B a) : IsIntegral A a := by
  letI : Algebra A B := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  haveI : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    have := hB b b.2
    exact (isIntegral_algebraMap_iff (A := B) (B := K) (x := b) Subtype.val_injective).1 this⟩
  exact isIntegral_trans a ha

theorem mem_of_isIntegral_loc {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (D : Subring K)
    (hA : ∀ a, IsIntegral A a → a ∈ A) (hAD : ∀ a ∈ A, a ∈ D)
    (hD : ∀ a ∈ D, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) (a : K) (ha : IsIntegral D a) : a ∈ D := by
  obtain ⟨v, -, hv0, hvi, hi⟩ := GlobalTheory.T.integral_over_localization_scaled A D hAD hD a ha
  have e : a = (v * a) * v⁻¹ := by field_simp
  rw [e]
  exact mul_mem (hAD _ (hA _ hi)) hvi

theorem ideal_ext {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K)
    (hAR : ∀ a ∈ A, a ∈ R) (hR : ∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v)
    (P₁ P₂ : Ideal (integralClosure R K).toSubring)
    (hag : ∀ t : (integralClosure R K).toSubring, IsIntegral A (t : K) → (t ∈ P₁ ↔ t ∈ P₂)) : P₁ = P₂ := by
  have hRT : ∀ r ∈ R, r ∈ (integralClosure R K).toSubring := fun r hr =>
    isIntegral_algebraMap (x := (⟨r, hr⟩ : R))
  have key : ∀ Q₁ Q₂ : Ideal (integralClosure R K).toSubring,
      (∀ t : (integralClosure R K).toSubring, IsIntegral A (t : K) → t ∈ Q₁ → t ∈ Q₂) → Q₁ ≤ Q₂ := by
    intro Q₁ Q₂ h t ht
    obtain ⟨v, hv, hv0, hvi, hi⟩ := GlobalTheory.T.integral_over_localization_scaled A R hAR hR t t.2
    have h1 := h (⟨v, hRT v (hAR v hv)⟩ * t) hi (Q₁.mul_mem_left _ ht)
    have h2 := Q₂.mul_mem_left ⟨v⁻¹, hRT _ hvi⟩ h1
    have e : (⟨v⁻¹, hRT _ hvi⟩ : (integralClosure R K).toSubring) * (⟨v, hRT v (hAR v hv)⟩ * t) = t := by
      apply Subtype.ext
      change v⁻¹ * (v * (t : K)) = t
      field_simp
    rwa [e] at h2
  exact le_antisymm (key _ _ fun t ht => (hag t ht).1) (key _ _ fun t ht => (hag t ht).2)

theorem exists_ne {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (M : PModel o x) : ∃ c, x c ≠ 0 := by
  obtain ⟨c, hc⟩ := M.tie.cover ⟨genPt M.ξ, specializes_rfl⟩
  exact ⟨c, hc.1⟩

theorem join_chart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω) (d n : ℕ)
    (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d)
    (hi : ∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔
      a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d))
    (c : κ) (hc : x c ≠ 0) (a : Ω) (ha : IsIntegral (chRing o x c) a) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := by
  have hcd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have h1 : ∀ k, z k / x c ^ d ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := fun k => by
    have e : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = z k / x c ^ d := by
      simp only [joinCo, RingHom.id_apply, hz]
      rw [mul_div_mul_left _ _ hc]
    rw [← e]
    exact Algebra.subset_adjoin ⟨(c, k), rfl⟩
  have h2 : ∀ j, x j / x c ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := fun j => by
    have e : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x j / x c := by
      simp only [joinCo, RingHom.id_apply, hz]
      rw [mul_div_mul_right _ _ hcd]
    rw [← e]
    exact Algebra.subset_adjoin ⟨(j, Sum.inl c), rfl⟩
  have h3 : chRing o x c ≤ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
    Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact h2 j)
  have key : ∀ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d),
      a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) := by
    intro a h
    induction h using Submodule.span_induction with
    | mem a h => obtain ⟨k, rfl⟩ := h; exact h1 k
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul r a _ h => exact mul_mem (h3 r.2) h
  exact key a ((hi c hc a).1 ha)

theorem map_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) (a : Ω)
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem exists_of_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) (a : Ω')
    (ha : a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c) : ∃ b ∈ chRing o x c, algebraMap Ω Ω' b = a := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    exact ⟨x j / x c, Algebra.subset_adjoin ⟨j, rfl⟩, map_div₀ _ _ _⟩
  | algebraMap r =>
    exact ⟨algebraMap o Ω r, Subalgebra.algebraMap_mem _ r, (IsScalarTower.algebraMap_apply o Ω Ω' r).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨a', h1, rfl⟩ := ha
    obtain ⟨b', h2, rfl⟩ := hb
    exact ⟨a' + b', add_mem h1 h2, map_add _ _ _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', h1, rfl⟩ := ha
    obtain ⟨b', h2, rfl⟩ := hb
    exact ⟨a' * b', mul_mem h1 h2, map_mul _ _ _⟩

theorem normal_of_charts {o : Type} [CommRing o] {Ω' : Type} [Field Ω'] [Algebra o Ω'] {κ' : Type} [Finite κ']
    {y : κ' → Ω'} (M' : PModel o y) (S : Set κ') (hS : ∀ p' : Cpt M'.ξ, ∃ c ∈ S, InChart M'.ξ y c p')
    (hI : ∀ c ∈ S, ∀ a : Ω', IsIntegral (chRing o y c) a → a ∈ chRing o y c) : Flat.NormalCpt M'.ξ := by
  intro p' a ha
  obtain ⟨c, hcS, hp⟩ := hS p'
  have h := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' c p' hp
  refine mem_of_isIntegral_loc (chRing o y c) (regAt M'.ξ p') (hI c hcS) h.1 (fun a ha => ?_) a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (h.2 a).1 ha
  exact ⟨u, hu, v, hv, hvu.1, hvu.2.2, rfl⟩

theorem unitAt_map {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (i : Ω →+* Ω') {p : Cpt ξ} {p' : Cpt ξ'}
    (h : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' p') {u : Ω} (hu : unitAt ξ p u) : unitAt ξ' p' (i u) :=
  ⟨(map_ne_zero i).2 hu.1, h _ hu.2.1, by rw [← map_inv₀]; exact h _ hu.2.2⟩

section Sit

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
  {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ')

variable {M Ω' M' f} in

theorem dom_of_eq (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω')) {p : Cpt M.ξ} {p' : Cpt M'.ξ} (h : f p'.1 = p.1) :
    (∀ a ∈ regAt M.ξ p, algebraMap Ω Ω' a ∈ regAt M'.ξ p') ∧
      ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p' (algebraMap Ω Ω' a) → unitAt M.ξ p a := by
  obtain ⟨h', hl⟩ := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
  have e : (⟨f p'.1, h'⟩ : Cpt M.ξ) = p := Subtype.ext h
  rwa [e] at hl

theorem fibre_iff (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a → a ∈ chRing o y (e c))
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (c : κ) (p : Cpt M.ξ) (hp : InChart M.ξ x c p) (p' : Cpt M'.ξ) :
    f p'.1 = p.1 ↔ InChart M'.ξ y (e c) p' ∧
      ∀ u ∈ chRing o x c, (unitAt M.ξ p u ↔ unitAt M'.ξ p' (algebraMap Ω Ω' u)) := by
  have hr := PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp
  constructor
  · intro h
    have hl := dom_of_eq hD h
    refine ⟨hC c hp.1 p' fun j => ?_, fun u hu => ⟨unitAt_map _ hl.1, hl.2 u (hr.1 u hu)⟩⟩
    rw [← map_div₀]
    exact hl.1 _ (hp.2 j)
  · rintro ⟨hp', hu⟩
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hp'
    have hA : ∀ u ∈ chRing o x c, algebraMap Ω Ω' u ∈ regAt M'.ξ p' := fun u hu' =>
      hr'.1 _ (hB c hp.1 _ (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu'⟩ :
        chRing o (fun k => algebraMap Ω Ω' (x k)) c))))
    have hl : (∀ a ∈ regAt M.ξ p, algebraMap Ω Ω' a ∈ regAt M'.ξ p') ∧
        ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p' (algebraMap Ω Ω' a) → unitAt M.ξ p a := by
      refine ⟨fun a ha => ?_, fun a ha h => ?_⟩
      · obtain ⟨u, h1, v, h2, hv, rfl⟩ := (hr.2 a).1 ha
        have := ((hu v h2).1 hv).2.2
        rw [map_div₀, div_eq_mul_inv]
        exact mul_mem (hA u h1) this
      · obtain ⟨u, h1, v, h2, hv, rfl⟩ := (hr.2 a).1 ha
        have h3 : unitAt M'.ξ p' (algebraMap Ω Ω' u) := by
          have h4 := Flat.ZUnit.mul h ((hu v h2).1 hv)
          have h5 : algebraMap Ω Ω' (u / v) * algebraMap Ω Ω' v = algebraMap Ω Ω' u := by
            rw [← map_mul, div_mul_cancel₀ _ hv.1]
          rwa [h5] at h4
        have h4 := Flat.ZUnit.mul ((hu u h1).2 h3) (Flat.ZUnit.inv hv)
        rwa [← div_eq_mul_inv] at h4
    obtain ⟨h', hl'⟩ := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
    exact congrArg Subtype.val (PositivityTheory.HtPt.Mb.centre_unique M M'.ξ (algebraMap Ω Ω') p' ⟨f p'.1, h'⟩ p hl' hl)

theorem chart_over (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a → a ∈ chRing o y (e c))
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (c : κ) (hc : x c ≠ 0) (p' : Cpt M'.ξ) :
    InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p := by
  constructor
  · intro hp'
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hp'
    have hA : ∀ u ∈ chRing o x c, algebraMap Ω Ω' u ∈ regAt M'.ξ p' := fun u hu' =>
      hr'.1 _ (hB c hc _ (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu'⟩ :
        chRing o (fun k => algebraMap Ω Ω' (x k)) c))))
    obtain ⟨p₀, hl, -, hch⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M M'.X Ω' M'.ξ (algebraMap Ω Ω') p' ⟨c, hc, hA⟩
    obtain ⟨h', hl'⟩ := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω' M'.ξ (algebraMap Ω Ω') f hD p'
    exact ⟨p₀, congrArg Subtype.val (PositivityTheory.HtPt.Mb.centre_unique M M'.ξ (algebraMap Ω Ω') p' p₀ ⟨f p'.1, h'⟩ hl hl'),
      hch c hc fun j => hA _ (Algebra.subset_adjoin ⟨j, rfl⟩)⟩
  · rintro ⟨p, hpf, hp⟩
    have hl := dom_of_eq hD hpf.symm
    refine hC c hc p' fun j => ?_
    rw [← map_div₀]
    exact hl.1 _ (hp.2 j)

end Sit

theorem isIntegral_mono {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K)
    (h : ∀ a ∈ A, a ∈ R) (b : K) (hb : IsIntegral A b) : IsIntegral R b :=
  IsIntegral.map_of_comp_eq (A.val.toRingHom.codRestrict R fun a => h a a.2) (RingHom.id K) (by ext; rfl) hb

theorem isIntegral_mono' {K : Type} [Field K] {R D : Subring K} (h : R ≤ D) (b : K) (hb : IsIntegral R b) :
    IsIntegral D b :=
  IsIntegral.map_of_comp_eq (Subring.inclusion h) (RingHom.id K) (by ext; rfl) hb

section Sit

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
  {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ')

local notation "i₀" => algebraMap Ω Ω'
local notation "A₀" => chRing o (fun k => algebraMap Ω Ω' (x k))

theorem normAt_of_charts (hD : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    (hy : ∀ c, x c ≠ 0 → y (e c) ≠ 0)
    (hB : ∀ c, x c ≠ 0 → ∀ a : Ω', a ∈ chRing o y (e c) ↔ IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) a)
    (hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, algebraMap Ω Ω' (x j) / algebraMap Ω Ω' (x c) ∈ regAt M'.ξ p') →
      InChart M'.ξ y (e c) p')
    (hN : Flat.NormalCpt M'.ξ) (p : Cpt M.ξ) : NormAt M'.ξ f (algebraMap Ω Ω') p := by
  obtain ⟨c, hp⟩ := M.tie.cover p
  have hc := hp.1
  have hr := PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp
  have hB1 : ∀ c, x c ≠ 0 → ∀ a : Ω', IsIntegral (A₀ c) a → a ∈ chRing o y (e c) := fun c hc a => (hB c hc a).2
  have hAR : ∀ a ∈ A₀ c, a ∈ (regAt M.ξ p).map i₀ := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_chRing x Ω' c a ha
    exact ⟨b, hr.1 b hb, rfl⟩
  have hR : ∀ r ∈ (regAt M.ξ p).map i₀, ∃ u ∈ A₀ c, ∃ v ∈ A₀ c, v ≠ 0 ∧ v⁻¹ ∈ (regAt M.ξ p).map i₀ ∧ r = u / v := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (hr.2 a).1 ha
    exact ⟨i₀ u, map_chRing x Ω' c u hu, i₀ v, map_chRing x Ω' c v hv, (map_ne_zero _).2 hvu.1,
      ⟨v⁻¹, hvu.2.2, map_inv₀ _ _⟩, map_div₀ _ _ _⟩
  have first : ∀ p' : Cpt M'.ξ, f p'.1 = p.1 →
      ∃ (P : Ideal (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring) (_ : P.IsMaximal),
        regAt M'.ξ p' = (LocalSubring.ofPrime _ P).toSubring ∧
        ∀ t : (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring,
          t ∈ P ↔ ¬ ((t : Ω') ≠ 0 ∧ (t : Ω')⁻¹ ∈ regAt M'.ξ p') := by
    intro p' hf
    have hl := dom_of_eq hD hf
    have hch := ((fibre_iff M Ω' M' f e hD hB1 hC c p hp p').1 hf).1
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hch
    have hRD : (regAt M.ξ p).map i₀ ≤ regAt M'.ξ p' := by
      rintro _ ⟨a, ha, rfl⟩
      exact hl.1 a ha
    refine GlobalTheory.T.local_subring_integral_closure_max ((regAt M.ξ p).map i₀) (regAt M'.ξ p') (chRing o y (e c)).toSubring hRD ?_ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ h0 hinv
      have hu : unitAt M'.ξ p' (i₀ a) := ⟨h0, hl.1 a ha, hinv⟩
      exact ⟨a⁻¹, (hl.2 a ha hu).2.2, map_inv₀ _ _⟩
    · intro t ht
      exact hN p' t (isIntegral_mono' hRD t ht)
    · intro b hb
      exact isIntegral_mono _ _ hAR b ((hB c hc b).1 hb)
    · intro a ha
      obtain ⟨u, hu, v, hv, hvu, rfl⟩ := (hr'.2 a).1 ha
      exact ⟨u, hu, v, hv, hvu.1, hvu.2.2, rfl⟩
  refine ⟨fun p' hf => ?_, fun P hPm => ?_, hD⟩
  · obtain ⟨P, hPm, hD', -⟩ := first p' hf
    exact ⟨P, hPm, hD'⟩
  · have hBT : ∀ b : chRing o y (e c), (b : Ω') ∈ (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring := fun b =>
      isIntegral_mono _ _ hAR _ ((hB c hc b).1 b.2)
    let ι : chRing o y (e c) →+* (integralClosure ((regAt M.ξ p).map i₀) Ω').toSubring :=
      { toFun := fun b => ⟨b, hBT b⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    obtain ⟨p', ⟨hch, hmem⟩, huniq⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω' κ' y M' (e c) (hy c hc) (P.comap ι) inferInstance
    have hr' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p' hch
    have hf : f p'.1 = p.1 := by
      refine (fibre_iff M Ω' M' f e hD hB1 hC c p hp p').2 ⟨hch, fun u hu => ?_⟩
      have hub : i₀ u ∈ chRing o y (e c) := (hB c hc _).2
        (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c u hu⟩ : A₀ c)))
      have h1 : ι ⟨i₀ u, hub⟩ ∈ P ↔ ¬ unitAt M'.ξ p' (i₀ u) := hmem ⟨i₀ u, hub⟩
      have h2 := GlobalTheory.T.maximal_ideal_membership_of_local ((regAt M.ξ p).map i₀) P hPm (ι ⟨i₀ u, hub⟩) ⟨u, hr.1 u hu, rfl⟩
      have h3 : unitAt M.ξ p u ↔ (i₀ u ≠ 0 ∧ (i₀ u)⁻¹ ∈ (regAt M.ξ p).map i₀) := by
        refine ⟨fun h => ⟨(map_ne_zero _).2 h.1, ⟨u⁻¹, h.2.2, map_inv₀ _ _⟩⟩, ?_⟩
        rintro ⟨h0, a, ha, e'⟩
        have hu0 : u ≠ 0 := fun h => h0 (by rw [h, map_zero])
        have : a = u⁻¹ := (algebraMap Ω Ω').injective (by rw [map_inv₀]; exact e')
        exact ⟨hu0, hr.1 u hu, this ▸ ha⟩
      rw [h3]
      exact not_iff_not.1 (h2.symm.trans h1)
    obtain ⟨P', hPm', hD', hP'⟩ := first p' hf
    have e' : P = P' := by
      refine ideal_ext (A₀ c) ((regAt M.ξ p).map i₀) hAR hR P P' fun t ht => ?_
      have hb : (t : Ω') ∈ chRing o y (e c) := (hB c hc _).2 ht
      have h1 : t ∈ P ↔ ¬ unitAt M'.ξ p' (t : Ω') := hmem ⟨t, hb⟩
      rw [h1, hP' t]
      exact not_congr ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hr'.1 _ hb, h.2⟩⟩
    subst e'
    refine ⟨p', ⟨hf, hD'⟩, ?_⟩
    rintro p'' ⟨hf'', hD''⟩
    have hch'' := ((fibre_iff M Ω' M' f e hD hB1 hC c p hp p'').1 hf'').1
    have hr'' := PositivityTheory.HtPt.Ma.regat_loc o Ω' κ' y M' (e c) p'' hch''
    refine huniq p'' ⟨hch'', fun u => ?_⟩
    have h := GlobalTheory.T.prime_mem_iff_not_unit_localization _ P inferInstance (ι u)
    rw [← hD''] at h
    refine h.trans (not_congr ⟨fun h => ⟨h.1, hr''.1 _ u.2, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩)

end Sit

theorem exists_normalisation : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p := by
  intro o _ _ Ω _ _ κ _ x M Ω' _ _ _ _ _
  have hinj : ∀ c, x c ≠ 0 → algebraMap Ω Ω' (x c) ≠ 0 := fun c hc => by
    simpa using hc
  have hinj' : ∀ c, algebraMap Ω Ω' (x c) ≠ 0 → x c ≠ 0 := fun c hc h => hc (by simp [h])
  obtain ⟨d, n, z, hz1, hz2⟩ := GlobalTheory.T.integral_closure_chart_span o Ω' κ (fun k => algebraMap Ω Ω' (x k))
    (fun c hc => PositivityTheory.HtPt.Mb.finite_ext M Ω' c (hinj' c hc))
  set x' : κ → Ω' := fun k => algebraMap Ω Ω' (x k) with hx'
  set y := joinCo (RingHom.id Ω') x' z with hy
  obtain ⟨c₀, hc₀⟩ := exists_ne M
  have hyne : ∀ c, x c ≠ 0 → y (c, Sum.inl c) ≠ 0 := fun c hc => by
    simp only [hy, joinCo, RingHom.id_apply, hz1]
    exact mul_ne_zero (hinj c hc) (pow_ne_zero _ (hinj c hc))
  have hJ := fun c (hc : x c ≠ 0) a (ha : IsIntegral (chRing o x' c) a) =>
    join_chart (o := o) x' d n z hz1 hz2 c (hinj c hc) a ha
  obtain ⟨M'⟩ : Nonempty (PModel o y) := GlobalTheory.T.projective_model_nonempty o Ω' (κ × (κ ⊕ Fin n)) y
    ⟨(c₀, Sum.inl c₀), hyne c₀ hc₀, fun a => by
      obtain ⟨b, v, hb, hv, hv0, rfl⟩ := PositivityTheory.HtPt.Mb.frac_ext M Ω' c₀ hc₀ a
      exact ⟨b, hJ c₀ hc₀ b hb, v, hJ c₀ hc₀ v (isIntegral_algebraMap (x := (⟨v, hv⟩ : chRing o x' c₀))), rfl⟩⟩
  have hT := PositivityTheory.HtPt.Mb.norm_chart o Ω' κ x' d n z M' hz1 hz2
  have hB : ∀ c, x c ≠ 0 → ∀ a : Ω', a ∈ chRing o y (c, Sum.inl c) ↔ IsIntegral (chRing o x' c) a :=
    fun c hc => (hT c (hinj c hc)).1
  have hC : ∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, (∀ j, x' j / x' c ∈ regAt M'.ξ p') → InChart M'.ξ y (c, Sum.inl c) p' :=
    fun c hc => (hT c (hinj c hc)).2
  have hcov : ∀ p' : Cpt M'.ξ, ∃ c, x c ≠ 0 ∧ InChart M'.ξ y (c, Sum.inl c) p' := by
    intro p'
    obtain ⟨⟨c, k⟩, h0, h1⟩ := M'.tie.cover p'
    have hc' : x' c ≠ 0 := left_ne_zero_of_mul h0
    have hk : z k ≠ 0 := right_ne_zero_of_mul h0
    refine ⟨c, hinj' c hc', hC c (hinj' c hc') p' fun j => ?_⟩
    have := h1 (j, k)
    simp only [hy, joinCo, RingHom.id_apply] at this
    rwa [mul_div_mul_right _ _ hk] at this
  have hreg : ∀ (c : κ) (p' : Cpt M'.ξ), InChart M'.ξ y (c, Sum.inl c) p' → ∀ a ∈ chRing o x c, algebraMap Ω Ω' a ∈ regAt M'.ξ p' := by
    intro c p' hp a ha
    have hc : x c ≠ 0 := hinj' c (left_ne_zero_of_mul hp.1)
    exact (PositivityTheory.HtPt.Ma.regat_loc o Ω' _ y M' _ p' hp).1 _ ((hB c hc _).2
      (isIntegral_algebraMap (x := (⟨_, map_chRing x Ω' c a ha⟩ : chRing o x' c))))
  obtain ⟨f, hf, -⟩ := PositivityTheory.HtPt.Mb.morph o Ω κ x M o Ω' _ y M' (algebraMap Ω Ω') fun p' => by
    obtain ⟨c, hc, hp⟩ := hcov p'
    exact ⟨c, hc, hreg c p' hp⟩
  have hN : Flat.NormalCpt M'.ξ := by
    refine normal_of_charts M' {q | ∃ c, x c ≠ 0 ∧ q = (c, Sum.inl c)} (fun p' => ?_) ?_
    · obtain ⟨c, hc, hp⟩ := hcov p'
      exact ⟨_, ⟨c, hc, rfl⟩, hp⟩
    · rintro _ ⟨c, hc, rfl⟩ a ha
      rw [hB c hc]
      refine int_trans (chRing o x' c) (chRing o y (c, Sum.inl c)) (fun b hb => (hB c hc b).2
        (isIntegral_algebraMap (x := (⟨b, hb⟩ : chRing o x' c)))) (fun b hb => (hB c hc b).1 hb) a ha
  refine ⟨_, inferInstance, y, M', f, hf, hN, ?_, fun p => ?_⟩
  · refine GlobalTheory.T.dominating_model_chart_compat M Ω' M' f (fun c => (c, Sum.inl c)) hf hyne
      (fun c hc p' => chart_over M Ω' M' f _ hf (fun c hc a ha => (hB c hc a).2 ha) hC c hc p') fun c hc => ?_
    refine ⟨(Set.finite_range fun k => z k / x' c ^ d).toFinset, fun a => ?_⟩
    rw [Set.Finite.coe_toFinset]
    exact (hB c hc a).trans (hz2 c (hinj c hc) a)
  · exact normAt_of_charts M Ω' M' f (fun c => (c, Sum.inl c)) hf hyne hB hC hN p

end PositivityTheory.HtPt.Mb.LNormExists.NormEx

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.norm_exists : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p :=
  @PositivityTheory.HtPt.Mb.LNormExists.NormEx.exists_normalisation
