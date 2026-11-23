import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenCoind
import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenLevel
import GroundTheory.ProfiniteCohomology.PoitouTate.RealTraceMap
import GroundTheory.ProfiniteCohomology.RealPlaces.Vanishing
import GroundTheory.ProfiniteCohomology.RealPlaces.Devissage
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseMain
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

theorem isTotallyComplex_of_sq_eq_neg_one {F : Type*} [Field F] (x : F) (hx : x ^ 2 = -1) :
    IsTotallyComplex F := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => ?_⟩
  have h1 := congrArg (fun f : F →+* ℂ => f x)
    (ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw))
  have h2 : (starRingEnd ℂ) (w.embedding x) = w.embedding x := h1
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : (w.embedding x) ^ 2 = -1 := by rw [← map_pow, hx, map_neg, map_one]
  rw [hr] at h3
  have h4 : r ^ 2 = -1 := by exact_mod_cast h3
  nlinarith [sq_nonneg r]

section GenericTrace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G) [Fintype κ]
  {n : ℕ} [NeZero n] (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D]

theorem surjective_of_ptTLocalToCompact_two (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n)
    (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
    (invr : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom D) 2 →+ QZ)
    (ht : ∀ ξ : ptTLocal φ ψ D 2, zmodToQZ n (t ((ptTLocalToCompact φ ψ D 2).hom ξ)) =
      ∑ v, inv v (ξ.1 v) + ∑ w, invr w (ξ.2 w))
    (v : ι) (η : cohomology (Rep.res (φ v).toMonoidHom D) 2) (hη : inv v η = zmodToQZ n 1) :
    Function.Surjective t := by
  classical
  have h1 : t ((ptTLocalToCompact φ ψ D 2).hom ((Pi.single v η, 0) : ptTLocal φ ψ D 2)) = 1 :=
    zmodToQZ_injective ((ht _).trans ((congrArg₂ (· + ·) (sum_apply_pi_single inv v η)
      (Finset.sum_eq_zero fun w _ => map_zero (invr w))).trans ((add_zero _).trans hη)))
  intro a
  refine ⟨a.val • (ptTLocalToCompact φ ψ D 2).hom ((Pi.single v η, 0) : ptTLocal φ ψ D 2), ?_⟩
  rw [map_nsmul, h1, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

end GenericTrace

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Places

variable {N : ℕ} (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)
include hS hev

theorem mem_of_natCast_two_mem_of_even :
    ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  apply hS v
  obtain ⟨m, hm⟩ := hev
  rw [hm, ← two_mul, Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

theorem mem_of_natCast_two_mul_mem_of_even :
    ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 * N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  rw [Nat.cast_mul] at hv
  rcases v.isPrime.mem_or_mem hv with h2 | hN
  · exact mem_of_natCast_two_mem_of_even S hS hev v h2
  · exact hS v hN

end Places

theorem exists_sq_eq_neg_one_of_even {N : ℕ} (hev : Even N) : ∃ z : ℚ̄, z ^ 2 = -1 ∧ z ^ (2 * N) = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄) (show 0 < 2 by norm_num)
  refine ⟨z, hz, ?_⟩
  obtain ⟨m, hm⟩ := hev
  rw [hm, show 2 * (m + m) = 2 * 2 * m by ring, pow_mul, pow_mul, hz]
  norm_num

theorem gsRealFamily_realConj_ne (w : {v : InfinitePlace K.1 // v.IsReal}) (η : maxUnramifiedOutside K.1 ℚ̄ S)
    (hη : η ^ 2 = -1) : gsRealFamily S ιr w (realConj w.1 w.2) η ≠ η := by
  intro hfix
  have key := gsRealFamily_apply S ιr w (realConj w.1 w.2) η
  rw [hfix] at key
  have hη' : ((η : ℚ̄)) ^ 2 = -1 := by
    have e := congrArg (fun y : maxUnramifiedOutside K.1 ℚ̄ S => (y : ℚ̄)) hη
    push_cast at e
    exact e
  have ha2 : (ιr w (η : ℚ̄)) ^ 2 = -1 := by rw [← map_pow, hη', map_neg, map_one]
  have ha0 : ιr w (η : ℚ̄) ≠ 0 := fun h0 => by
    rw [h0] at ha2
    norm_num at ha2
  have hu : Units.mk0 _ ha0 ^ 4 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2]
    norm_num)
  have hc := realConj_apply_of_pow_eq_one w.1 w.2 (Units.mk0 _ ha0) (by norm_num) hu
  have h3 : ιr w (η : ℚ̄) * ιr w (η : ℚ̄) = 1 :=
    calc ιr w (η : ℚ̄) * ιr w (η : ℚ̄) = ιr w (η : ℚ̄) * realConj w.1 w.2 (ιr w (η : ℚ̄)) :=
          congrArg (fun z => ιr w (η : ℚ̄) * z) key
      _ = ((Units.mk0 _ ha0 : (AlgebraicClosure w.1.Completion)ˣ) : AlgebraicClosure w.1.Completion) *
          (((Units.mk0 _ ha0)⁻¹ : (AlgebraicClosure w.1.Completion)ˣ) : AlgebraicClosure w.1.Completion) :=
          congrArg (fun z => ιr w (η : ℚ̄) * z) hc
      _ = 1 := Units.mul_inv _
  have h4 : (-1 : AlgebraicClosure w.1.Completion) = 1 := by rw [← ha2, sq, h3]
  norm_num at h4

theorem freeOnCosets_gsRealFamily_of_fixes (ζ : maxUnramifiedOutside K.1 ℚ̄ S) (hζ : ζ ^ 2 = -1)
    (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hW : ∀ σ ∈ W, σ ζ = ζ) :
    FreeOnCosets (gsRealFamily S ιr) W := by
  intro w x h hmem
  rcases eq_one_or_eq_realConj w.1 w.2 h with h1 | h1
  · exact h1
  exfalso
  subst h1
  have hfix : (x * gsRealFamily S ιr w (realConj w.1 w.2) * x⁻¹) ζ = ζ := hW _ hmem
  have h2 : gsRealFamily S ιr w (realConj w.1 w.2) (x⁻¹ ζ) = x⁻¹ ζ :=
    calc gsRealFamily S ιr w (realConj w.1 w.2) (x⁻¹ ζ)
        = x⁻¹ ((x * gsRealFamily S ιr w (realConj w.1 w.2) * x⁻¹) ζ) := (x.symm_apply_apply _).symm
      _ = x⁻¹ ζ := congrArg (fun y => (x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) y) hfix
  have hη : (x⁻¹ ζ) ^ 2 = -1 := by rw [← map_pow, hζ, map_neg, map_one]
  exact gsRealFamily_realConj_ne S ιr w (x⁻¹ ζ) hη h2

section Hypotheses

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

set_option maxHeartbeats 1000000 in
include hS in

theorem surjective_of_localToCompact_two [hne : Nonempty S]
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : ∀ ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2,
      zmodToQZ N (t ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ)) =
        ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w)) :
    Function.Surjective t := by
  obtain ⟨v⟩ := hne
  obtain ⟨η, hη⟩ := (bijective_gsLocalInvRoots_of_places S ιs N (fun v hv h => hv (hS v h)) v).2 1
  exact surjective_of_ptTLocalToCompact_two (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) t
    (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) ht v η
    ((zmodToQZ_gsLocalInvRoots S ιs N v η).symm.trans (congrArg (zmodToQZ N) hη))

omit [Fintype S] in
include hS hev in

theorem isTotallyComplex_of_gsOpenSubgroup_le {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) : IsTotallyComplex L.1 := by
  obtain ⟨z, hz2, hzN⟩ := exists_sq_eq_neg_one_of_even hev
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  have hzL : z ∈ L.1 := rootsOfUnity_mem_of_gsOpenSubgroup_le S (2 * N) hL W₀ hW₀ hU hn0
    (fun v hv h => hv (mem_of_natCast_two_mul_mem_of_even S hS hev v h)) z hzN
  refine isTotallyComplex_of_sq_eq_neg_one (⟨z, hzL⟩ : L.1) ?_
  apply Subtype.ext
  push_cast
  exact hz2

omit [Fintype S] in
include hS hev in

theorem freeOnCosets_gsRealFamily_of_le (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) :
    FreeOnCosets (gsRealFamily S ιr) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) := by
  obtain ⟨z, hz2, hzN⟩ := exists_sq_eq_neg_one_of_even hev
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  have hzmem : z ∈ maxUnramifiedOutside K.1 ℚ̄ S := mem_maxUnramifiedOutside_of_pow_eq_one S hn0
    (fun v hv h => hv (mem_of_natCast_two_mul_mem_of_even S hS hev v h)) hzN
  have hζ : (⟨z, hzmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ^ 2 = -1 := by
    apply Subtype.ext
    push_cast
    exact hz2
  have hne : (⟨z, hzmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := fun h0 => by
    rw [h0] at hζ
    norm_num at hζ
  have hpow : Units.mk0 _ hne ^ (2 * N) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    apply Subtype.ext
    push_cast
    exact hzN)
  exact freeOnCosets_gsRealFamily_of_fixes S ιr _ hζ _ fun σ hσ => hW₀ σ (hU hσ) _ hpow

end Hypotheses

end GroundTheory.ProfCoh
