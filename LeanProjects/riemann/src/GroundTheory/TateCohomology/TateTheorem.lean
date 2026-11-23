import Mathlib
import GroundTheory.TateCohomology.SplittingCohTrivial
import GroundTheory.TateCohomology.TateDeltaZero
import GroundTheory.TateCohomology.TateSubgroupMaps
set_option maxSynthPendingDepth 1

open CategoryTheory Limits Rep

namespace GroundTheory.GroupCoh

section Basics

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

omit [Fintype G] in

noncomputable def tateOneClass : tateCohomology (Rep.trivial ℤ S ℤ) 0 :=
  ((tateCohomologyZeroIso ℤ S).app (Rep.trivial ℤ S ℤ)).inv.hom
    (Submodule.Quotient.mk ⟨(1 : ℤ), fun _ => rfl⟩)

end Basics

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
  (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup G,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

include h1 h2 h3

noncomputable def tateTheoremIsoTop (n : ℤ) :
    tateCohomology (Rep.trivial ℤ G ℤ) n ≅ tateCohomology M (n + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augTrivSES_shortExact ℤ G) n)
      (isIso_δ_of_tateAcyclic (augTrivSES_shortExact ℤ G) (tateAcyclic_leftRegular (k := ℤ)) n) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ (splittingSES_shortExact M u) (n + 1))
      (isIso_δ_of_tateAcyclic (splittingSES_shortExact M u)
        (cohTrivial_splittingModule M u h1 h2 h3).tateAcyclic (n + 1)) ≪≫
    eqToIso (congrArg (tateCohomology M) (by ring))

variable (S : Subgroup G) [Fintype S]

noncomputable def tateTheoremIso (n : ℤ) :
    tateCohomology (Rep.trivial ℤ S ℤ) n ≅ tateCohomology (res S.subtype M) (n + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) n)
      (isIso_δ_of_tateAcyclic (augTrivSES_res_shortExact ℤ S.subtype)
        (tateAcyclic_res_leftRegular S) n) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (n + 1))
      (isIso_δ_of_tateAcyclic ((shortExact_res S.subtype).2 (splittingSES_shortExact M u))
        (cohTrivial_splittingModule M u h1 h2 h3 S) (n + 1)) ≪≫
    eqToIso (congrArg (tateCohomology (res S.subtype M)) (by ring))

theorem tateTheoremIso_zero_apply :
    (tateIsoH (res S.subtype M) (0 + 2) 2 (by norm_num)).hom.hom
      ((tateTheoremIso M u h1 h2 h3 S 0).hom.hom (tateOneClass S)) =
      groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u := by
  obtain ⟨c, hc⟩ := exists_tateComplex_cycles_zero (Rep.trivial ℤ S ℤ) ⟨(1 : ℤ), fun _ => rfl⟩
  have hcls : tateOneClass S = ((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c :=
    tateCohomologyZeroIso_inv_mk _ c _ hc.symm
  have hx : ((augTrivSES ℤ G).map (resFunctor S.subtype)).f.hom ∘
      (fun s : S => augIdealSubOne (k := ℤ) (s : G)) =
      groupCohomology.d₀₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₂
        (MonoidAlgebra.single (1 : G) (1 : ℤ)) := by
    funext h
    change MonoidAlgebra.single (h : G) (1 : ℤ) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular ℤ G).ρ (h : G) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  have ha := tateIsoH_δ_zero_apply (augTrivSES_res_shortExact ℤ S.subtype)
    (oneInvariant ℤ S.subtype) (MonoidAlgebra.single (1 : G) (1 : ℤ))
    (by exact augmentation_single (k := ℤ) (1 : G) (1 : ℤ)) _ hx c hc
  have hcoc : (⟨fun s : S => augIdealSubOne (k := ℤ) (s : G),
      groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ :
        groupCohomology.cocycles₁ (res S.subtype (augIdeal ℤ G))) = augCocycle ℤ S.subtype := rfl
  have hs : (tateIsoH ((splittingSES M u).map (resFunctor S.subtype)).X₁ ((1 : ℕ) + 1) (1 + 1)
      (Nat.cast_succ 1).symm).hom.hom
      ((tδ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (1 : ℕ) ((1 : ℕ) + 1)
        rfl).hom ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
          (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c))) =
      (groupCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 (1 + 1)
        rfl).hom ((tateIsoH ((splittingSES M u).map (resFunctor S.subtype)).X₃ (1 : ℕ) 1
          rfl).hom.hom ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
            (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c))) :=
    congr(($(tδ_comp_tateIsoH ((shortExact_res S.subtype).2
      (splittingSES_shortExact M u)) 1)).hom
        ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
          (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c)))
  have key := δ_splittingSES_res_δ₀ M u S.subtype
  rw [δ₀_augTrivSES_res] at key
  rw [hcls]
  refine hs.trans ?_
  refine Eq.trans ?_ key
  exact congrArg (groupCohomology.δ ((shortExact_res S.subtype).2
    (splittingSES_shortExact M u)) 1 2 rfl).hom (ha.trans (congrArg _ hcoc))

noncomputable def tateReciprocityIso :
    tateCohomology (Rep.trivial ℤ S ℤ) (-2) ≅ tateCohomology (res S.subtype M) 0 :=
  tateTheoremIso M u h1 h2 h3 S (-2) ≪≫ eqToIso (congrArg (tateCohomology (res S.subtype M)) (by norm_num))

end Tate

end GroundTheory.GroupCoh
