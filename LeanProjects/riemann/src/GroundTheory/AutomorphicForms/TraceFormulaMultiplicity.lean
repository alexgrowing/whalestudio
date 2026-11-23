import Mathlib
import GroundTheory.AutomorphicForms.TraceFormulaSpectral
import GroundTheory.AutomorphicForms.UnitaryRepresentations.ExistsEqAlgebraMapOfIsSelfAdjoint

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))

theorem orthogonalProjection_mem_intertwiners (j : J) :
    ((V j).orthogonalProjectionOnto : H →L[ℂ] V j) ∈ π.intertwiners (π.restrict (V j) (hinv j)) := by
  rw [mem_intertwiners]
  intro g v
  apply Subtype.ext
  have h := ((isInvariant_iff_commute_starProjection (V j)).1 (hinv j) g).eq
  have h2 : (π g) ((V j).starProjection v) = (V j).starProjection (π g v) :=
    congrArg (fun T : H →L[ℂ] H => T v) h
  rw [coe_restrict_apply, ← Submodule.starProjection_apply, ← Submodule.starProjection_apply]
  exact h2.symm

variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)

include hsum in

theorem orthogonalProjection_coe_eq_zero {i j : J} (hij : i ≠ j) (v : V j) :
    (V i).orthogonalProjectionOnto (v : H) = 0 := by
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  exact hsum.OrthogonalFamily hij ⟨u, hu⟩ v

include hsum in

theorem eq_zero_of_forall_orthogonalProjection {x : H}
    (hx : ∀ j, (V j).orthogonalProjectionOnto x = 0) : x = 0 := by
  have hle : (⨆ j, V j) ≤ (ℂ ∙ x)ᗮ := by
    refine iSup_le fun j u hu => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := (Submodule.orthogonalProjectionOnto_eq_zero_iff).1 (hx j)
    rw [Submodule.mem_orthogonal] at this
    rw [← inner_conj_symm, this u hu, map_zero]
  have hcl : (⨆ j, V j).topologicalClosure ≤ (ℂ ∙ x)ᗮ :=
    Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
  have hmem : x ∈ (ℂ ∙ x)ᗮ := hcl (top_le_topologicalClosure_iSup hsum Submodule.mem_top)
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact inner_self_eq_zero.1 hmem

variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)

section Class

variable {σ : UnitaryRep G K}

abbrev EquivSummands (σ : UnitaryRep G K) : Type _ :=
  {j : J // (π.restrict (V j) (hinv j)).IsEquivalent σ}

def summandEquivL (w : EquivSummands hinv σ) : K →L[ℂ] V w.1 :=
  ((w.2.some.symm.toLinearIsometryEquiv : K ≃ₗᵢ[ℂ] V w.1) : K →L[ℂ] V w.1)

theorem summandEquivL_mem (w : EquivSummands hinv σ) :
    summandEquivL hinv w ∈ σ.intertwiners (π.restrict (V w.1) (hinv w.1)) :=
  Equiv.mem_intertwiners _

theorem summandEquivL_ne_zero (hσ : σ.IsIrreducible) (w : EquivSummands hinv σ) :
    summandEquivL hinv w ≠ 0 := by
  have := hσ.1
  obtain ⟨k, hk⟩ := exists_ne (0 : K)
  intro h
  have h1 := congrArg (fun T : K →L[ℂ] V w.1 => T k) h
  simp only [zero_apply] at h1
  apply hk
  have h2 : ‖summandEquivL hinv w k‖ = ‖k‖ := LinearIsometryEquiv.norm_map _ k
  rw [h1, norm_zero] at h2
  exact norm_eq_zero.1 h2.symm

def sumEquivL [Fintype (EquivSummands hinv σ)] (c : EquivSummands hinv σ → ℂ) : K →L[ℂ] H :=
  ∑ w, c w • ((V w.1).subtypeL ∘L summandEquivL hinv w)

theorem sumEquivL_mem [Fintype (EquivSummands hinv σ)] (c : EquivSummands hinv σ → ℂ) :
    sumEquivL hinv c ∈ σ.intertwiners π :=
  Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _
    (comp_mem_intertwiners (subtypeL_mem_intertwiners π (V w.1) (hinv w.1))
      (summandEquivL_mem hinv w))

open Classical in
include hsum in
theorem orthogonalProjection_comp_sumEquivL [Fintype (EquivSummands hinv σ)]
    (c : EquivSummands hinv σ → ℂ) (j : J) (k : K) :
    (V j).orthogonalProjectionOnto (sumEquivL hinv c k) =
      if h : (π.restrict (V j) (hinv j)).IsEquivalent σ then
        c ⟨j, h⟩ • summandEquivL hinv ⟨j, h⟩ k else 0 := by
  classical
  simp only [sumEquivL, sum_apply, smul_apply, comp_apply, map_sum, map_smul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp [Submodule.subtypeL_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    · intro w _ hw
      have hwj : j ≠ w.1 := fun e => hw (Subtype.ext e.symm)
      rw [Submodule.subtypeL_apply, orthogonalProjection_coe_eq_zero hsum hwj, smul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun w _ => ?_
    have hwj : j ≠ w.1 := fun e => h (e ▸ w.2)
    rw [Submodule.subtypeL_apply, orthogonalProjection_coe_eq_zero hsum hwj, smul_zero]

include hsum hirr in

theorem finrank_intertwiners_eq_card (hσ : σ.IsIrreducible)
    (hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      Module.finrank ℂ (σ.intertwiners π) = Nat.card (EquivSummands hinv σ) := by
  classical
  have : Finite (EquivSummands hinv σ) := hW.to_subtype
  let _ : Fintype (EquivSummands hinv σ) := Fintype.ofFinite _
  let Ψ : (EquivSummands hinv σ → ℂ) →ₗ[ℂ] σ.intertwiners π :=
    { toFun := fun c => ⟨sumEquivL hinv c, sumEquivL_mem hinv c⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp [sumEquivL, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a b => by
        apply Subtype.ext
        simp [sumEquivL, smul_smul, Finset.smul_sum] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext w
    have h1 : ∀ k, (V w.1).orthogonalProjectionOnto (sumEquivL hinv c k) = 0 := by
      intro k
      have := congrArg (fun T : σ.intertwiners π => (T : K →L[ℂ] H) k) hc
      change sumEquivL hinv c k = 0 at this
      rw [this, map_zero]
    have h2 : c w • summandEquivL hinv w = 0 := by
      ext1 k
      have := h1 k
      rw [orthogonalProjection_comp_sumEquivL hinv hsum, dif_pos w.2] at this
      simpa using this
    have := hσ.1
    obtain ⟨k, hk⟩ := exists_ne (0 : K)
    have h3 := congrArg (fun S : K →L[ℂ] V w.1 => S k) h2
    simp only [smul_apply, zero_apply] at h3
    rcases smul_eq_zero.1 h3 with h | h
    · exact h
    · exfalso
      have h4 : ‖summandEquivL hinv w k‖ = ‖k‖ := LinearIsometryEquiv.norm_map _ k
      rw [h, norm_zero] at h4
      exact hk (norm_eq_zero.1 h4.symm)
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨T, hT⟩
    have hPT : ∀ w : EquivSummands hinv σ, ∃ c : ℂ,
        (V w.1).orthogonalProjectionOnto ∘L T = c • summandEquivL hinv w := fun w =>
      hσ.exists_eq_smul_of_mem_intertwiners (hirr w.1) (summandEquivL_mem hinv w)
        (comp_mem_intertwiners (orthogonalProjection_mem_intertwiners hinv w.1) hT)
        (summandEquivL_ne_zero hinv hσ w)
    choose c hc using hPT
    refine ⟨c, Subtype.ext ?_⟩
    change sumEquivL hinv c = T
    ext1 k
    refine (sub_eq_zero.1 (eq_zero_of_forall_orthogonalProjection hsum fun j => ?_)).symm
    rw [map_sub, orthogonalProjection_comp_sumEquivL hinv hsum]
    split_ifs with h
    · have := congrArg (fun S : K →L[ℂ] V j => S k) (hc ⟨j, h⟩)
      simp only [comp_apply, smul_apply] at this
      rw [this, sub_self]
    · have h0 : (V j).orthogonalProjectionOnto ∘L T = 0 :=
        hσ.eq_zero_of_not_isEquivalent (hirr j) (fun e => h e.symm)
          (comp_mem_intertwiners (orthogonalProjection_mem_intertwiners hinv j) hT)
      have := congrArg (fun S : K →L[ℂ] V j => S k) h0
      simp only [comp_apply, zero_apply] at this
      rw [this, sub_zero]
  let e := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.finiteDimensional e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Class

include hsum hirr in

theorem multiplicity_eq_finrank
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite)
    (c : Quotient (restrictSetoid π hinv)) {σ : UnitaryRep G K}
    (hσ : (π.restrict (V c.out) (hinv c.out)).IsEquivalent σ) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      multiplicity π hinv c = Module.finrank ℂ (σ.intertwiners π) := by
  have hσirr : σ.IsIrreducible := hσ.isIrreducible_iff.1 (hirr c.out)
  have hiff : ∀ j, (π.restrict (V j) (hinv j)).IsEquivalent σ ↔
      Quotient.mk (restrictSetoid π hinv) j = c := by
    intro j
    rw [← Quotient.out_eq c, Quotient.eq]
    exact ⟨fun h => h.trans hσ.symm, fun h => h.trans hσ⟩
  have hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite :=
    (hfin c.out).subset fun j hj => hj.trans hσ.symm
  obtain ⟨hfd, hrank⟩ := finrank_intertwiners_eq_card hinv hsum hirr hσirr hW
  refine ⟨hfd, ?_⟩
  rw [hrank, multiplicity]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun j => (hiff j).symm)

end UnitaryRep

end

end GroundTheory.Automorphic
