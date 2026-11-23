import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CosetFin

variable {H : Type} [Group H]

theorem finite_mk_mul (A K : Subgroup H) (x : H) (h : (K.map (MulAut.conj x).toMonoidHom).relIndex A ≠ 0) :
    {q : H ⧸ K | ∃ a ∈ A, q = (QuotientGroup.mk (a * x) : H ⧸ K)}.Finite := by
  set S := (K.map (MulAut.conj x).toMonoidHom).subgroupOf A
  haveI : S.FiniteIndex := ⟨h⟩
  haveI : Finite (A ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_range (fun t : A ⧸ S => (QuotientGroup.mk ((t.out : H) * x) : H ⧸ K))).subset ?_
  rintro q ⟨a, ha, rfl⟩
  refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ S), ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul S (⟨a, ha⟩ : A)
  simp only
  rw [hu]
  have hu2 : ((u : A) : H) ∈ K.map (MulAut.conj x).toMonoidHom := u.2
  obtain ⟨k, hk, hke⟩ := hu2
  rw [QuotientGroup.eq]
  have : ((u : A) : H) = x * k * x⁻¹ := by rw [← hke]; rfl
  simp only [Subgroup.coe_mul, this]
  have e : (a * (x * k * x⁻¹) * x)⁻¹ * (a * x) = k⁻¹ := by group
  rw [e]; exact K.inv_mem hk

theorem finite_mk_dcoset (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (s : H) :
    {q : H ⧸ K | ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, q = (QuotientGroup.mk (k₁ * s * k₂) : H ⧸ K)}.Finite := by
  set T := K.subgroupOf K₀
  haveI : T.FiniteIndex := ⟨hc⟩
  haveI : Finite (K₀ ⧸ T) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_iUnion (fun t : K₀ ⧸ T => finite_mk_mul K₀ K (s * (t.out : H)) (hconj _))).subset ?_
  rintro q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨k₂, hk₂⟩ : K₀) : K₀ ⧸ T), k₁, hk₁, ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul T (⟨k₂, hk₂⟩ : K₀)
  rw [hu, QuotientGroup.eq]
  have hu2 : ((u : K₀) : H) ∈ K := u.2
  simp only [Subgroup.coe_mul]
  have e : (k₁ * s * k₂)⁻¹ * (k₁ * (s * (k₂ * ((u : K₀) : H)))) = ((u : K₀) : H) := by group
  rw [e]; exact hu2

theorem finite_mk_support (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (φ : H → ℂ) (S : Finset H)
    (hS : ∀ g, φ g ≠ 0 → ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂) :
    {q : H ⧸ K | ∃ g, φ g ≠ 0 ∧ q = (QuotientGroup.mk g : H ⧸ K)}.Finite := by
  refine (S.finite_toSet.biUnion fun s _ => finite_mk_dcoset K₀ K hc hconj s).subset ?_
  rintro q ⟨g, hg, rfl⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem relIndex_ne_zero_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (y : G) :
    IsOpen ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  have e : ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) = (fun g => y⁻¹ * g * y) ⁻¹' (U : Set G) := by
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : y⁻¹ * ((MulAut.conj y).toMonoidHom k) * y = k := by
        show y⁻¹ * (y * k * y⁻¹) * y = k; group
      rw [this]; exact hk
    · intro h
      refine ⟨_, h, ?_⟩
      show y * (y⁻¹ * g * y) * y⁻¹ = g; group
  rw [e]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.CosetFin

namespace GlobalTheory.CosetFin

theorem commensurable_map_conj {G : Type} [Group G] {A B : Subgroup G} (h : A.Commensurable B) (y : G) :
    (A.map (MulAut.conj y).toMonoidHom).Commensurable (B.map (MulAut.conj y).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  exact ⟨by rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]; exact h.1,
    by rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]; exact h.2⟩

end GlobalTheory.CosetFin

open GlobalTheory.CosetFin in

theorem GlobalTheory.testProd_support_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  intro p _ G L f hf _ K' f' hf' _
  obtain ⟨-, -, -, S, hS⟩ := hf
  obtain ⟨hc', -, -, S', hS'⟩ := hf'

  have hA : {a : G.GAf ⧸ L.K.toSubgroup | ∃ g, f g ≠ 0 ∧ a = (QuotientGroup.mk g : G.GAf ⧸ L.K.toSubgroup)}.Finite := by
    refine finite_mk_support L.K.toSubgroup L.K.toSubgroup ?_ ?_ f S hS
    · rw [Subgroup.relIndex_self]; exact one_ne_zero
    · intro y
      exact relIndex_ne_zero_open_compact _ _ (isOpen_map_conj _ L.K.isOpen y) L.compact

  have hB : {b : Gr G 1 ⧸ K' | ∃ g, f' g ≠ 0 ∧ b = (QuotientGroup.mk g : Gr G 1 ⧸ K')}.Finite := by
    refine finite_mk_support (KHT p G.m G.n 1 G.Fw) K' hc'.1 ?_ f' S' hS'
    intro y
    have h1 := (GlobalTheory.heckeOperator_integral p G 1 Nat.one_pos).1 y
    exact ((commensurable_map_conj hc' y).trans h1).1
  let ψ : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) →
      (G.GAf ⧸ L.K.toSubgroup) × (Gr G 1 ⧸ K') :=
    fun q => ((QuotientGroup.mk q.out.1 : G.GAf ⧸ L.K.toSubgroup), (QuotientGroup.mk q.out.2 : Gr G 1 ⧸ K'))
  have hψ : Function.Injective ψ := by
    intro q r hqr
    simp only [ψ, Prod.mk.injEq, QuotientGroup.eq] at hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
    apply QuotientGroup.eq.2
    exact Subgroup.mem_prod.2 ⟨by simpa using hqr.1, by simpa using hqr.2⟩
  refine ((hA.prod hB).preimage hψ.injOn).subset ?_
  intro q hq
  have h1 : f q.out.1 ≠ 0 := left_ne_zero_of_mul hq
  have h2 : f' q.out.2 ≠ 0 := right_ne_zero_of_mul hq
  exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
