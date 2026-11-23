import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
import GroundTheory.ProfiniteCohomology.MackeyFormula.Cohomology
import GroundTheory.ProfiniteCohomology.PoincareDuality.Induced
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

universe u

section Abstract

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, CompactSpace (F w)] (ψ : ∀ w, F w →ₜ* G)
  (W : OpenSubgroup G) (N : Rep.{u} k (W : Subgroup G)) [IsDiscreteRep N]

def mackeyRealRes (n : ℕ) (c : cohomology N n) :
    ∀ w, ∀ d : MackeyDoubleCoset (W : Subgroup G) (ψ w).toMonoidHom,
      cohomology (mackeyRep (W : Subgroup G) (ψ w).toMonoidHom N d.out) n :=
  fun w d => (cohomologyMapAlong (mackeyConj (W : Subgroup G) (ψ w).toMonoidHom d.out)
    (continuous_toMonoidHom (mackeyConjₜ W (ψ w) d.out)) (𝟙 _) n).hom c

theorem mackeyCohomologyEquiv_globalToLocal_coind (n : ℕ)
    (c : cohomology (Rep.coind (W : Subgroup G).subtype N) n) :
    (fun w => mackeyCohomologyEquiv W (ψ w) N n
      ((globalToLocal ψ (Rep.coind (W : Subgroup G).subtype N)
        (fun w => Rep.res (ψ w).toMonoidHom (Rep.coind (W : Subgroup G).subtype N))
        (fun _ => 𝟙 _) n).hom c w)) =
      mackeyRealRes ψ W N n ((shapiroMap W N n).hom c) :=
  funext fun w => funext fun d => mackeyCohomologyEquiv_cohomologyMapAlong W (ψ w) N n c d

theorem bijective_shapiroMap_hom (n : ℕ) : Function.Bijective (shapiroMap W N n).hom := by
  have := isIso_shapiroMap W n N
  exact ConcreteCategory.bijective_of_isIso _

theorem bijective_pi_mackeyCohomologyEquiv (n : ℕ) :
    Function.Bijective (fun (f : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom
        (Rep.coind (W : Subgroup G).subtype N)) n) w => mackeyCohomologyEquiv W (ψ w) N n (f w)) :=
  ⟨fun _ _ h => funext fun w => (mackeyCohomologyEquiv W (ψ w) N n).injective (congrFun h w),
    fun t => ⟨fun w => (mackeyCohomologyEquiv W (ψ w) N n).symm (t w),
      funext fun _ => LinearEquiv.apply_symm_apply _ _⟩⟩

theorem injective_globalToLocal_coind_iff (n : ℕ) :
    Function.Injective (globalToLocal ψ (Rep.coind (W : Subgroup G).subtype N)
        (fun w => Rep.res (ψ w).toMonoidHom (Rep.coind (W : Subgroup G).subtype N))
        (fun _ => 𝟙 _) n).hom ↔
      Function.Injective (mackeyRealRes ψ W N n) := by
  rw [← Function.Injective.of_comp_iff (bijective_pi_mackeyCohomologyEquiv ψ W N n).1]
  have key : (fun (f : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom
        (Rep.coind (W : Subgroup G).subtype N)) n) w => mackeyCohomologyEquiv W (ψ w) N n (f w)) ∘
      (globalToLocal ψ (Rep.coind (W : Subgroup G).subtype N)
        (fun w => Rep.res (ψ w).toMonoidHom (Rep.coind (W : Subgroup G).subtype N))
        (fun _ => 𝟙 _) n).hom =
      mackeyRealRes ψ W N n ∘ (shapiroMap W N n).hom :=
    funext fun c => mackeyCohomologyEquiv_globalToLocal_coind ψ W N n c
  rw [key]
  exact Function.Injective.of_comp_iff' _ (bijective_shapiroMap_hom W N n)

theorem surjective_globalToLocal_coind_iff (n : ℕ) :
    Function.Surjective (globalToLocal ψ (Rep.coind (W : Subgroup G).subtype N)
        (fun w => Rep.res (ψ w).toMonoidHom (Rep.coind (W : Subgroup G).subtype N))
        (fun _ => 𝟙 _) n).hom ↔
      Function.Surjective (mackeyRealRes ψ W N n) := by
  rw [← Function.Surjective.of_comp_iff' (bijective_pi_mackeyCohomologyEquiv ψ W N n)]
  have key : (fun (f : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom
        (Rep.coind (W : Subgroup G).subtype N)) n) w => mackeyCohomologyEquiv W (ψ w) N n (f w)) ∘
      (globalToLocal ψ (Rep.coind (W : Subgroup G).subtype N)
        (fun w => Rep.res (ψ w).toMonoidHom (Rep.coind (W : Subgroup G).subtype N))
        (fun _ => 𝟙 _) n).hom =
      mackeyRealRes ψ W N n ∘ (shapiroMap W N n).hom :=
    funext fun c => mackeyCohomologyEquiv_globalToLocal_coind ψ W N n c
  rw [key]
  exact Function.Surjective.of_comp_iff _ (bijective_shapiroMap_hom W N n).2

def MackeyTopIndex : Type u :=
  {p : Σ w, MackeyDoubleCoset (W : Subgroup G) (ψ w).toMonoidHom //
    mackeySubgroup (W : Subgroup G) (ψ p.1).toMonoidHom p.2.out = ⊤}

def mackeyTopRes (n : ℕ) (c : cohomology N n) :
    ∀ p : MackeyTopIndex ψ W,
      cohomology (mackeyRep (W : Subgroup G) (ψ p.1.1).toMonoidHom N p.1.2.out) n :=
  fun p => mackeyRealRes ψ W N n c p.1.1 p.1.2

variable {ψ W N} {n : ℕ}
  (h : ∀ w (d : MackeyDoubleCoset (W : Subgroup G) (ψ w).toMonoidHom),
    mackeySubgroup (W : Subgroup G) (ψ w).toMonoidHom d.out ≠ ⊤ →
      Subsingleton (cohomology (mackeyRep (W : Subgroup G) (ψ w).toMonoidHom N d.out) n))
include h

omit [CompactSpace G] [∀ w, CompactSpace (F w)] in

theorem injective_mackeyRealRes_iff :
    Function.Injective (mackeyRealRes ψ W N n) ↔ Function.Injective (mackeyTopRes ψ W N n) := by
  constructor
  · intro hi c c' hcc
    refine hi (funext fun w => funext fun d => ?_)
    by_cases hd : mackeySubgroup (W : Subgroup G) (ψ w).toMonoidHom d.out = ⊤
    · exact congrFun hcc ⟨⟨w, d⟩, hd⟩
    · exact (h w d hd).elim _ _
  · intro hi c c' hcc
    exact hi (funext fun p => congrFun (congrFun hcc p.1.1) p.1.2)

omit [CompactSpace G] [∀ w, CompactSpace (F w)] in

theorem surjective_mackeyRealRes_iff :
    Function.Surjective (mackeyRealRes ψ W N n) ↔ Function.Surjective (mackeyTopRes ψ W N n) := by
  classical
  constructor
  · intro hs t
    obtain ⟨c, hc⟩ := hs fun w d =>
      if hd : mackeySubgroup (W : Subgroup G) (ψ w).toMonoidHom d.out = ⊤ then t ⟨⟨w, d⟩, hd⟩ else 0
    refine ⟨c, funext fun p => ?_⟩
    have := congrFun (congrFun hc p.1.1) p.1.2
    rw [dif_pos p.2] at this
    exact this
  · intro hs t
    obtain ⟨c, hc⟩ := hs fun p => t p.1.1 p.1.2
    refine ⟨c, funext fun w => funext fun d => ?_⟩
    by_cases hd : mackeySubgroup (W : Subgroup G) (ψ w).toMonoidHom d.out = ⊤
    · exact congrFun hc ⟨⟨w, d⟩, hd⟩
    · exact (h w d hd).elim _ _

end Abstract

section Trivial

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

theorem subsingleton_cohomology_of_subsingleton_group [Subsingleton H] (A : Rep.{0} (ULift.{0} ℤ) H)
    [IsDiscreteRep A] {n : ℕ} (hn : 1 ≤ n) : Subsingleton (cohomology A n) := by
  suffices h : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A (by omega) x
  have : Nat.card (H ⧸ (U : Subgroup H)) = 1 := Nat.card_unique
  rwa [this, one_smul] at hU

end Trivial

section GS

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (W : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))

instance isDiscreteRep_res_coind_zmodRep_two {H' : Type} [Group H'] [TopologicalSpace H']
    (ψ : H' →ₜ* galUnramifiedOutside K.1 ℚ̄ S) :
    IsDiscreteRep (Rep.res ψ.toMonoidHom (Rep.coind (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) :=
  isDiscreteRep_res_toMonoidHom ψ _

theorem subsingleton_cohomology_gsFinFamily_coind_zmodRep (v : S) {j : ℕ} (hj : 3 ≤ j) :
    Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
      (Rep.coind (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) j) := by
  refine subsingleton_cohomology_of_cdp_le_two (n := 2) two_ne_zero (fun ℓ hℓ _ => ?_)
    (Rep.res (gsFinFamily S ιs v).toMonoidHom (Rep.coind (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2)))
    (fun m => nsmul_coind_zmodRep_eq_zero W m) hj
  refine cdp_galois_le_two _ _ hℓ ?_
  exact_mod_cast hℓ.ne_zero

theorem eq_bot_of_ne_top_realGal (v : {v : InfinitePlace K.1 // v.IsReal})
    (P : Subgroup Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (hP : P ≠ ⊤) : P = ⊥ := by
  have : Fact (Nat.card Gal(AlgebraicClosure v.1.Completion / v.1.Completion)).Prime :=
    ⟨by rw [Nat.card_eq_fintype_card, card_realGal_eq_two v.1 v.2]; exact Nat.prime_two⟩
  exact P.eq_bot_or_eq_top_of_prime_card.resolve_right hP

theorem subsingleton_cohomology_mackeyRep_realFamily (N : Rep.{0} (ULift.{0} ℤ)
    (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep N] {n : ℕ} (hn : 1 ≤ n)
    (v : {v : InfinitePlace K.1 // v.IsReal})
    (d : MackeyDoubleCoset (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom)
    (hd : mackeySubgroup (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom d.out ≠ ⊤) :
    Subsingleton (cohomology (mackeyRep (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom N d.out) n) := by
  have hb := eq_bot_of_ne_top_realGal v _ hd
  have : Subsingleton (mackeySubgroup (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom d.out) := by
    rw [hb]
    infer_instance
  exact subsingleton_cohomology_of_subsingleton_group _ hn

def GsMackeyTopInjective (j : ℕ) : Prop :=
  Function.Injective (mackeyTopRes (gsRealFamily S ιr) W (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2) j)

def GsMackeyTopSurjective (j : ℕ) : Prop :=
  Function.Surjective (mackeyTopRes (gsRealFamily S ιr) W (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2) j)

theorem gsTateCompactCohomology_coind_zmodRep_eq_zero_of
    (hI : ∀ j, 4 ≤ j → GsMackeyTopInjective S ιr W j)
    (hS : ∀ j, 3 ≤ j → GsMackeyTopSurjective S ιr W j)
    {r : ℕ} (hr : 4 ≤ r)
    (x : gsTateCompactCohomology S ιr ιs (Rep.coind (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2)) r) : x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  have htriv : ∀ j, 1 ≤ j → ∀ v (d : MackeyDoubleCoset (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom),
      mackeySubgroup (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) (gsRealFamily S ιr v).toMonoidHom
        d.out ≠ ⊤ →
      Subsingleton (cohomology (mackeyRep (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom
        (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2) d.out) j) :=
    fun j hj v d hd => subsingleton_cohomology_mackeyRep_realFamily S ιr W _ hj v d hd
  have hs := (surjective_tateGlobalToLocal_iff (gsFinFamily S ιs) (gsRealFamily S ιr) (Rep.coind
      (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (Rep.coind
        (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
          (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (Rep.coind
        (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
          (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) (fun _ => 𝟙 _) (n + 1)
      (fun v => subsingleton_cohomology_gsFinFamily_coind_zmodRep S ιs W v (by omega))).2
    ((surjective_globalToLocal_coind_iff (gsRealFamily S ιr) W
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2) (n + 1)).2
      ((surjective_mackeyRealRes_iff (htriv (n + 1) (by omega))).2 (hS (n + 1) (by omega))))
  have hi := (injective_tateGlobalToLocal_iff (gsFinFamily S ιs) (gsRealFamily S ιr) (Rep.coind
      (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (Rep.coind
        (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
          (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (Rep.coind
        (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
          (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) (fun _ => 𝟙 _) (n + 2)
      (fun v => subsingleton_cohomology_gsFinFamily_coind_zmodRep S ιs W v (by omega))).2
    ((injective_globalToLocal_coind_iff (gsRealFamily S ιr) W
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2) (n + 2)).2
      ((injective_mackeyRealRes_iff (htriv (n + 2) (by omega))).2 (hI (n + 2) (by omega))))
  exact tateCompactCohomology_eq_zero_of_surjective_of_injective (gsFinFamily S ιs) (gsRealFamily S ιr)
    (Rep.coind (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))
    (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (Rep.coind
      (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (Rep.coind
      (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2))) (fun _ => 𝟙 _) n hs hi x

end GS

end GroundTheory.ProfCoh
