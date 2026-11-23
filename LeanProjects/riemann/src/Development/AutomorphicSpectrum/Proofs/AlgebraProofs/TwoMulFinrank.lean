import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace PtBasic

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem ht_surjective : Function.Surjective P.ht := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← P.om_lat.span_eq_top, Submodule.span_le]
  intro y hy
  obtain ⟨x, -, hx⟩ := P.κ_mem y hy
  show y ∈ LinearMap.range P.ht
  rw [LinearMap.mem_range]
  refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
  rw [map_smul, hx, ← algebraMap_smul C κ y, smul_smul, inv_mul_cancel₀ P.κ_ne, one_smul]

theorem T_lattice : P.T.IsLattice C := by
  obtain ⟨-, hsp, hT⟩ := P.free
  refine ⟨?_, hsp⟩
  rw [hT]
  exact Submodule.fg_span (Set.finite_range _)

theorem rho_t_mem (a : 𝓞 E) (i : Fin N) : P.ρ a (P.t i) ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hmem : ∀ k, P.ρ (RingOfIntegers.basis E k) (P.t i) ∈ P.T := fun k => by
    rw [hT]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => zsmul_mem (hmem k) _

theorem T_stable (a : 𝓞 E) : ∀ x ∈ P.T, P.ρ a x ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hle : P.T ≤ P.T.comap ((P.ρ a).restrictScalars O) := by
    nth_rewrite 1 [hT]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ P.T
    rw [show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) =
        (P.ρ a * P.ρ (RingOfIntegers.basis E q.2)) (P.t q.1) from rfl, ← map_mul]
    exact rho_t_mem P _ _
  exact fun x hx => hle hx

theorem ht_eigProj (σ : E →+* C) (x : V) :
    P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x) := by
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, P.ht_lin]

theorem om'_lattice : P.om'.IsLattice C := by
  have hT := T_lattice P
  refine ⟨?_, ?_⟩
  · rw [HTPoint.om']
    exact hT.fg.map _
  · rw [HTPoint.om', Submodule.map_coe, LinearMap.coe_restrictScalars, ← Submodule.map_span,
      hT.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact ht_surjective P

theorem omHT_eq (σ : E →+* C) :
    P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O) := by
  have hcomm : ((eigProj P.ρΩ σ).restrictScalars O) ∘ₗ (P.ht.restrictScalars O) =
      (P.ht.restrictScalars O) ∘ₗ ((eigProj P.ρ σ).restrictScalars O) :=
    LinearMap.ext fun x => (ht_eigProj P σ x).symm
  show (P.T.map (P.ht.restrictScalars O)).map ((eigProj P.ρΩ σ).restrictScalars O) =
    (P.T.map ((eigProj P.ρ σ).restrictScalars O)).map (P.ht.restrictScalars O)
  rw [← Submodule.map_comp, ← Submodule.map_comp, hcomm]

theorem e_skew (x y : V) : P.e x y = - P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem dualLat_flip : dualLat P.e.flip P.T = P.T := by
  conv_rhs => rw [← P.perfect]
  ext y
  simp only [LatBasic.mem_dualLat, LinearMap.flip_apply]
  refine forall₂_congr fun x _ => ?_
  rw [e_skew P y x, neg_mem_iff]
include P in
theorem finite_V : Module.Finite C V := by
  obtain ⟨s, hs⟩ := (T_lattice P).fg
  refine ⟨⟨s, ?_⟩⟩
  rw [← Submodule.span_span_of_tower O, hs, (T_lattice P).span_eq_top]
include P in
theorem two_mul_finrank : 2 * finrank C Ω = finrank C V := by
  haveI := finite_V P
  have hrefl : LinearMap.BilinForm.IsRefl P.e := fun x y h => by rw [e_skew P y x, h, neg_zero]
  have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.isOrtho_def,
      LinearMap.mem_ker]
    rw [P.lagr x]
    refine forall₂_congr fun y _ => ?_
    rw [e_skew P y x, neg_eq_zero]
  have htop : LinearMap.BilinForm.orthogonal P.e ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact (Submodule.mem_bot C).mpr (P.nondeg x fun y => hx y Submodule.mem_top)
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl (LinearMap.ker P.ht)
  rw [horth, htop, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker P.ht
  rw [LinearMap.range_eq_top.mpr (ht_surjective P), finrank_top] at h2
  omega

end PtBasic

theorem htPoint_basic : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω), Function.Surjective P.ht ∧ P.T.IsLattice C ∧ (∀ (a : 𝓞 E), ∀ x ∈ P.T, P.ρ a x ∈ P.T) ∧ (∀ (σ : E →+* C) x, P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x)) ∧ P.om'.IsLattice C ∧ (∀ σ : E →+* C, P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O)) ∧ dualLat P.e.flip P.T = P.T ∧ 2 * Module.finrank C Ω = Module.finrank C V := by
  intro C _ v O _ _ _ _ _ E _ _ c _ κ N V _ _ _ _ Ω _ _ _ _ P
  exact ⟨PtBasic.ht_surjective P, PtBasic.T_lattice P, PtBasic.T_stable P, PtBasic.ht_eigProj P,
    PtBasic.om'_lattice P, PtBasic.omHT_eq P, PtBasic.dualLat_flip P, PtBasic.two_mul_finrank P⟩

end GlobalTheory.CompanionTheory.Ar.HT
