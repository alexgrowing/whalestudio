import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaAverage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Set

section Count

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem avgOver_eq_zero_of_forall {K : Subgroup G} {f : G → W} {x : G}
    (h0 : ∀ k ∈ K, f (x * k) = 0) : avgOver K f x = 0 := by
  unfold avgOver avgSub
  rw [finsum_eq_zero_of_forall_eq_zero (fun q => h0 _ (Quotient.out q).2), smul_zero]

theorem avgOver_eq_of_forall_mul_eq {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) {x : G}
    {c : W} (hc : ∀ k ∈ K, f (x * k) = c) : avgOver K f x = c := by
  classical
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  rw [avgOver_eq_sum]
  have hterm : ∀ q : K ⧸ (rightStab f).subgroupOf K, f (x * ((Quotient.out q : K) : G)) = c :=
    fun q => hc _ (Quotient.out q).2
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard : (Fintype.card (K ⧸ (rightStab f).subgroupOf K) : ℂ) =
      (rightStab f).relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcard, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hf), one_smul]

theorem relIndex_ne_zero_trans {H K K' : Subgroup G} (hKK' : K ≤ K') (hH : H.relIndex K ≠ 0)
    (hK : K.relIndex K' ≠ 0) : H.relIndex K' ≠ 0 := by
  have h1 : (H ⊓ K).relIndex K' = (H ⊓ K).relIndex K * K.relIndex K' :=
    (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right hKK').symm
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 : (H ⊓ K).relIndex K' ≠ 0 := by
    rw [h1]
    exact mul_ne_zero hH hK
  intro h0
  apply h2
  have := Subgroup.relIndex_dvd_of_le_left K' (inf_le_left : H ⊓ K ≤ H)
  rw [h0] at this
  exact Nat.eq_zero_of_zero_dvd this

variable {A : Subgroup G}

section Incl

variable (A) {K K' : Subgroup G}

def cosetIncl : (K' ⊓ A : Subgroup G) ⧸ (K ⊓ A).subgroupOf (K' ⊓ A) → K' ⧸ K.subgroupOf K' :=
  fun r => (QuotientGroup.mk (Subgroup.inclusion (inf_le_left : K' ⊓ A ≤ K') (Quotient.out r)) :
    K' ⧸ K.subgroupOf K')

variable {A}

theorem cosetIncl_injective : Function.Injective (cosetIncl A (K := K) (K' := K')) := by
  intro r r' hrr'
  unfold cosetIncl at hrr'
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hrr'
  rw [← QuotientGroup.out_eq' r, ← QuotientGroup.out_eq' r', QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · simpa using hrr'
  · have ha := (Subgroup.mem_inf.1 (Quotient.out r).2).2
    have hb := (Subgroup.mem_inf.1 (Quotient.out r').2).2
    simpa using A.mul_mem (A.inv_mem ha) hb

theorem relIndex_inf_ne_zero (hK : K.relIndex K' ≠ 0) :
    (K ⊓ A).relIndex (K' ⊓ A) ≠ 0 := by
  have : (K.subgroupOf K').FiniteIndex := ⟨hK⟩
  have : Finite ((K' ⊓ A : Subgroup G) ⧸ (K ⊓ A).subgroupOf (K' ⊓ A)) :=
    Finite.of_injective _ (cosetIncl_injective (A := A) (K := K) (K' := K'))
  exact Subgroup.index_ne_zero_of_finite

end Incl

theorem avgOver_eq_smul_avgOver_inf {K K' : Subgroup G} {h : G → W} (hKK' : K ≤ K')
    (hf : AvgFinite K h) (hK : K.relIndex K' ≠ 0)
    (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k) :
    avgOver K' h 1 = (((K.relIndex K' : ℂ)⁻¹ * ((K ⊓ A).relIndex (K' ⊓ A) : ℂ))) •
      avgOver (K' ⊓ A) (avgOver K h) 1 := by
  classical
  set g := avgOver K h with hg
  have hgK : K ≤ rightStab g := le_rightStab_avgOver hf
  have hf' : AvgFinite K' h := relIndex_ne_zero_trans hKK' hf hK
  rw [← avgOver_avgOver hKK' hf']

  set S := K.subgroupOf K'
  set T := (K ⊓ A).subgroupOf (K' ⊓ A)
  have hT : T.index ≠ 0 := relIndex_inf_ne_zero hK
  have : S.FiniteIndex := ⟨hK⟩
  have : T.FiniteIndex := ⟨hT⟩
  let _ := Fintype.ofFinite (K' ⧸ S)
  let _ := Fintype.ofFinite ((K' ⊓ A : Subgroup G) ⧸ T)
  have hSle : S ≤ (rightStab g).subgroupOf K' := fun k hk => hgK hk
  have hTle : T ≤ (rightStab g).subgroupOf (K' ⊓ A) := fun k hk =>
    hgK (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
  rw [avgOver_eq_avgSub hSle hK, avgOver_eq_avgSub hTle hT, avgSub_eq_sum, avgSub_eq_sum,
    smul_smul]

  have hzero : ∀ q : K' ⧸ S, q ∉ Set.range (cosetIncl A (K := K) (K' := K')) →
      g (1 * ((Quotient.out q : K') : G)) = 0 := by
    intro q hq
    rw [one_mul]
    apply avgOver_eq_zero_of_forall
    intro k hk
    by_contra hne
    obtain ⟨a, ha, k₀, hk₀, hy⟩ := hsupp _ (K'.mul_mem (Quotient.out q).2 (hKK' hk)) hne
    apply hq
    have haK' : a ∈ K' := by
      have : a = (Quotient.out q : K') * k * k₀⁻¹ := by rw [hy]; group
      rw [this]
      exact K'.mul_mem (K'.mul_mem (Quotient.out q).2 (hKK' hk)) (K'.inv_mem (hKK' hk₀))
    refine ⟨QuotientGroup.mk ⟨a, Subgroup.mem_inf.2 ⟨haK', ha⟩⟩, ?_⟩
    unfold cosetIncl
    rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul T ⟨a, Subgroup.mem_inf.2 ⟨haK', ha⟩⟩
    have hsK : ((s : (K' ⊓ A : Subgroup G)) : G) ∈ K :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 s.2)).1
    rw [hs]
    show ((a * ((s : (K' ⊓ A : Subgroup G)) : G))⁻¹ * (Quotient.out q : K') : G) ∈ K
    have : ((a * ((s : (K' ⊓ A : Subgroup G)) : G))⁻¹ * (Quotient.out q : K') : G) =
        ((s : (K' ⊓ A : Subgroup G)) : G)⁻¹ * (k * k₀⁻¹)⁻¹ := by
      rw [show ((Quotient.out q : K') : G) = a * k₀ * k⁻¹ by rw [← hy]; group]
      group
    rw [this]
    exact K.mul_mem (K.inv_mem hsK) (K.inv_mem (K.mul_mem hk (K.inv_mem hk₀)))

  have hval : ∀ r : (K' ⊓ A : Subgroup G) ⧸ T,
      g (1 * ((Quotient.out (cosetIncl A (K := K) (K' := K') r) : K') : G)) =
        g (1 * ((Quotient.out r : (K' ⊓ A : Subgroup G)) : G)) := by
    intro r
    unfold cosetIncl
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S
      (Subgroup.inclusion (inf_le_left : K' ⊓ A ≤ K') (Quotient.out r))
    rw [hs]
    simp only [one_mul, Subgroup.coe_mul, Subgroup.coe_inclusion]
    exact hgK (Subgroup.mem_subgroupOf.1 s.2) _
  have hsum : ∑ q : K' ⧸ S, g (1 * ((Quotient.out q : K') : G)) =
      ∑ r : (K' ⊓ A : Subgroup G) ⧸ T, g (1 * ((Quotient.out r : (K' ⊓ A : Subgroup G)) : G)) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (cosetIncl A (K := K) (K' := K'))))
      (fun q _ hq => hzero q (by
        rintro ⟨r, rfl⟩
        exact hq (Finset.mem_image_of_mem _ (Finset.mem_univ r)))),
      Finset.sum_image (fun r _ r' _ h => cosetIncl_injective h)]
    exact Finset.sum_congr rfl fun r _ => hval r
  rw [hsum]
  congr 1
  show (S.index : ℂ)⁻¹ = ((K.relIndex K' : ℂ)⁻¹ * ((K ⊓ A).relIndex (K' ⊓ A) : ℂ)) * (T.index : ℂ)⁻¹
  have hT' : (T.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT
  rw [mul_assoc, show ((K ⊓ A).relIndex (K' ⊓ A) : ℂ) = T.index from rfl, mul_inv_cancel₀ hT',
    mul_one]
  rfl

variable (θ : A → W →ₗ[ℂ] W)

theorem avgOver_mul_left_eq {K : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hf : AvgFinite K h) (a : A) (y : G) :
    avgOver K h ((a : G) * y) = θ a (avgOver K h y) := by
  rw [← avgOver_comp_mul_left, ← avgOver_comp_linearMap hf (θ a)]
  congr 1
  funext z
  exact hh a z

theorem relIndex_smul_avgOver_eq {E : Type*} [AddCommGroup E] [Module ℂ E] (π : W →ₗ[ℂ] E)
    (hπ : ∀ a : A, π ∘ₗ θ a = π) {K K' : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hKK' : K ≤ K') (hf : AvgFinite K h)
    (hK : K.relIndex K' ≠ 0) (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k) :
    (K.relIndex K' : ℂ) • π (avgOver K' h 1) =
      ((K ⊓ A).relIndex (K' ⊓ A) : ℂ) • π (avgOver K h 1) := by
  rw [avgOver_eq_smul_avgOver_inf hKK' hf hK hsupp, map_smul, smul_smul, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK), one_mul]
  congr 1
  have hgf : AvgFinite (K' ⊓ A) (avgOver K h) := by
    have h1 : ((rightStab (avgOver K h)).subgroupOf (K' ⊓ A)) ≥
        (K ⊓ A).subgroupOf (K' ⊓ A) := fun k hk =>
      le_rightStab_avgOver hf (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
    have hT := relIndex_inf_ne_zero (A := A) hK
    intro h0
    apply hT
    have := Subgroup.index_dvd_of_le h1
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ this)
  rw [← avgOver_comp_linearMap hgf π]
  apply avgOver_eq_of_forall_mul_eq
  · have h1 : (rightStab (avgOver K h)) ≤ rightStab (fun y => π (avgOver K h y)) := fun k hk y => by
      show π (avgOver K h (y * k)) = π (avgOver K h y)
      rw [hk y]
    intro h0
    apply hgf
    have := Subgroup.relIndex_dvd_of_le_left (K' ⊓ A) h1
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ this)
  · intro k hk
    rw [one_mul]
    have := avgOver_mul_left_eq θ hh hf ⟨k, (Subgroup.mem_inf.1 hk).2⟩ 1
    rw [mul_one] at this
    rw [this, ← LinearMap.comp_apply, hπ]

theorem avgOver_eq_zero_of_le {K K' : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hKK' : K ≤ K') (hf : AvgFinite K h)
    (hK : K.relIndex K' ≠ 0) (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k)
    (h0 : avgOver K h 1 = 0) : avgOver K' h 1 = 0 := by
  rw [avgOver_eq_smul_avgOver_inf hKK' hf hK hsupp]
  rw [avgOver_eq_zero_of_forall, smul_zero]
  intro k hk
  rw [one_mul]
  have := avgOver_mul_left_eq θ hh hf ⟨k, (Subgroup.mem_inf.1 hk).2⟩ 1
  rw [mul_one] at this
  rw [this, h0, map_zero]

end Count

section Conj

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem avgOver_map_mulEquiv (φ : G ≃* G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f)
    (x : G) :
    avgOver (K.map φ.toMonoidHom) (fun y => f (φ.symm y)) x = avgOver K f (φ.symm x) := by
  classical
  set K' := K.map φ.toMonoidHom
  set ψ : K ≃* K' := φ.subgroupMap K
  set S := (rightStab f).subgroupOf K
  set S' : Subgroup K' := S.map ψ.toMonoidHom
  have hψ : ∀ k : K, ((ψ k : K') : G) = φ k := fun k => rfl
  have hS' : S' ≤ (rightStab fun y => f (φ.symm y)).subgroupOf K' := by
    rintro _ ⟨s, hs, rfl⟩ y
    show f (φ.symm (y * ((ψ s : K') : G))) = f (φ.symm y)
    rw [hψ, map_mul, MulEquiv.symm_apply_apply]
    exact hs _
  let e : K ⧸ S ≃ K' ⧸ S' := Quotient.congr ψ.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      refine ⟨a⁻¹ * b, h, ?_⟩
      simp
    · rintro ⟨c, hc, hc'⟩
      have : c = a⁻¹ * b := by
        apply ψ.injective
        rw [show ψ.toMonoidHom c = ψ c from rfl] at hc'
        rw [hc']
        simp
      rw [← this]
      exact hc)
  have hidx : S'.index = S.index := by
    rw [Subgroup.index, Subgroup.index]
    exact (Nat.card_congr e).symm
  have hS'i : S'.index ≠ 0 := by rw [hidx]; exact hf
  rw [avgOver_eq_avgSub hS' hS'i]
  unfold avgOver avgSub
  rw [hidx, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun q => ?_
  have he : e q = QuotientGroup.mk (ψ (Quotient.out q)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S' (ψ (Quotient.out q))
  rw [hs]
  have hs2 : ((s : K') : G) ∈ rightStab fun y => f (φ.symm y) := hS' s.2
  have hs3 : f (φ.symm (x * ((ψ (Quotient.out q) : K') : G) * ((s : K') : G))) =
      f (φ.symm (x * ((ψ (Quotient.out q) : K') : G))) := hs2 _
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, hs3, hψ, map_mul, MulEquiv.symm_apply_apply]

theorem avgOver_map_conj (b : G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) (x : G) :
    avgOver (K.map (MulAut.conj b).toMonoidHom) (fun y => f (b⁻¹ * y * b)) x =
      avgOver K f (b⁻¹ * x * b) := by
  have := avgOver_map_mulEquiv (MulAut.conj b) hf x
  simp only [MulAut.conj_symm_apply] at this
  exact this

omit [AddCommGroup W] [Module ℂ W] in

theorem avgFinite_map_mulEquiv (φ : G ≃* G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) :
    AvgFinite (K.map φ.toMonoidHom) (fun y => f (φ.symm y)) := by
  have hst : rightStab (fun y => f (φ.symm y)) = (rightStab f).map φ.toMonoidHom := by
    ext g
    rw [Subgroup.mem_map_equiv, mem_rightStab, mem_rightStab]
    constructor
    · intro H y
      have := H (φ y)
      rwa [map_mul, MulEquiv.symm_apply_apply] at this
    · intro H y
      rw [map_mul]
      exact H _
  show (rightStab fun y => f (φ.symm y)).relIndex (K.map φ.toMonoidHom) ≠ 0
  rw [hst, Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
  exact hf

end Conj

end Parabolic

end GroundTheory.Automorphic
