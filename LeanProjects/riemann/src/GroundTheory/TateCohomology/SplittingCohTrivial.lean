import Mathlib
import GroundTheory.TateCohomology.SplittingModule
import GroundTheory.TateCohomology.CohTrivial
import GroundTheory.TateCohomology.ResCores
set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section LES

variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)

theorem eq_zero_of_isZero {A : ModuleCat.{u} k} (h : IsZero A) (x : A) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero h).elim x 0

theorem isZero_of_forall_eq_zero {A : ModuleCat.{u} k} (h : ∀ x : A, x = 0) : IsZero A :=
  ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩

include hX in

theorem δ_map_g_apply (i j : ℕ) (hij : i + 1 = j) (x : groupCohomology X.X₂ i) :
    δ hX i j hij (map (MonoidHom.id H) X.g i x) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).comp_δ i j hij)).hom x)
  exact h

include hX in

theorem map_f_δ_apply (i j : ℕ) (hij : i + 1 = j) (z : groupCohomology X.X₃ i) :
    map (MonoidHom.id H) X.f j (δ hX i j hij z) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).δ_comp i j hij)).hom z)
  exact h

include hX in

theorem exists_map_f_eq (n : ℕ) (x : groupCohomology X.X₂ n)
    (hx : map (MonoidHom.id H) X.g n x = 0) : ∃ w, map (MonoidHom.id H) X.f n w = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (mapShortComplex₂_exact hX n) x hx

include hX in

theorem isZero_X₂_of_injective_δ (n : ℕ) (h₁ : IsZero (groupCohomology X.X₁ n))
    (hδ : Function.Injective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  have h1 : map (MonoidHom.id H) X.g n x = 0 :=
    hδ (by rw [δ_map_g_apply hX n (n + 1) rfl, map_zero])
  obtain ⟨w, hw⟩ := exists_map_f_eq hX n x h1
  rw [← hw, eq_zero_of_isZero h₁ w, map_zero]

include hX in

theorem isZero_X₂_succ_of_surjective_δ (n : ℕ) (h₃ : IsZero (groupCohomology X.X₃ (n + 1)))
    (hδ : Function.Surjective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ (n + 1)) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨w, hw⟩ := exists_map_f_eq hX (n + 1) x (eq_zero_of_isZero h₃ _)
  obtain ⟨z, rfl⟩ := hδ w
  rw [← hw, map_f_δ_apply hX n (n + 1) rfl z]

end LES

section TrivialInt

theorem isZero_H1_trivial_int {H : Type} [Group H] [Finite H] :
    IsZero (groupCohomology (Rep.trivial ℤ H ℤ) 1) := by
  have : Subsingleton (Additive H →+ ℤ) := ⟨fun f g => AddMonoidHom.ext fun x => by
    have key : ∀ φ : Additive H →+ ℤ, φ x = 0 := fun φ => by
      have h : addOrderOf x • φ x = 0 := by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
      exact (smul_eq_zero.1 h).resolve_left (addOrderOf_pos x).ne'
    rw [key f, key g]⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (H1IsoOfIsTrivial _)

end TrivialInt

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]

theorem tateAcyclic_res_leftRegular : TateAcyclic (res S.subtype (Rep.leftRegular ℤ G)) :=
  cohTrivial_leftRegular ℤ G S

theorem isZero_groupCohomology_res_leftRegular (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (res S.subtype (Rep.leftRegular ℤ G)) n) :=
  ((tateAcyclic_res_leftRegular S) n).of_iso (tateIsoH _ n n rfl).symm

noncomputable def augClass : groupCohomology (res S.subtype (augIdeal ℤ G)) 1 :=
  δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl ((H0Iso _).inv (oneInvariant ℤ S.subtype))

theorem exists_eq_zsmul_augClass (y : groupCohomology (res S.subtype (augIdeal ℤ G)) 1) :
    ∃ m : ℤ, y = m • augClass S := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 0
      (isZero_groupCohomology_res_leftRegular S 1)
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep y
  let c : ℤ := show ℤ from ((H0Iso _).hom w).1
  refine ⟨c, ?_⟩
  have hw : w = (H0Iso _).inv (c • oneInvariant ℤ S.subtype) := by
    have : ((H0Iso _).hom w) = c • oneInvariant ℤ S.subtype := by
      apply Subtype.ext
      change _ = c * 1
      rw [mul_one]
    rw [← this]
    exact ((Iso.hom_inv_id_apply (H0Iso _) w)).symm
  conv_lhs => rw [hw]
  rw [map_zsmul]
  exact map_zsmul _ c _

noncomputable def subgroupNormElt : MonoidAlgebra ℤ G :=
  ∑ t : S, MonoidAlgebra.single (t : G) (1 : ℤ)

omit [Fintype G] in

theorem ρ_subgroupNormElt (s : S) :
    (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) = subgroupNormElt S := by
  simp only [subgroupNormElt, map_sum, Representation.ofMulAction_single, smul_eq_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft s) _ _ (fun t => rfl)

omit [Fintype G] in

theorem augmentation_subgroupNormElt :
    augmentation ℤ G (subgroupNormElt S) = (Fintype.card S : ℤ) := by
  rw [subgroupNormElt, map_sum,
    Finset.sum_congr rfl (fun (x : S) _ => augmentation_single (k := ℤ) (x : G) (1 : ℤ))]
  simp

theorem card_smul_augClass : (Fintype.card S : ℤ) • augClass S = 0 := by
  let z : (res S.subtype (Rep.trivial ℤ G ℤ)).ρ.invariants := ⟨(Fintype.card S : ℤ), fun _ => rfl⟩
  have hx : ((augTrivSES ℤ G).map (resFunctor S.subtype)).f.hom ∘
      (0 : S → res S.subtype (augIdeal ℤ G)) =
      d₀₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₂ (subgroupNormElt S) := by
    funext s
    change (augIdealι ℤ G).hom 0 =
      (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) - subgroupNormElt S
    rw [map_zero, ρ_subgroupNormElt, sub_self]
  have hδ := δ₀_apply (augTrivSES_res_shortExact ℤ S.subtype) z (subgroupNormElt S)
    (by exact augmentation_subgroupNormElt S) _ hx
  have hz : z = (Fintype.card S : ℤ) • oneInvariant ℤ S.subtype := by
    apply Subtype.ext
    change _ = (Fintype.card S : ℤ) * 1
    rw [mul_one]
  have h0 : H1π ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₁
      ⟨0, mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ = 0 := by
    have : (⟨0, mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ :
        cocycles₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₁) = 0 := rfl
    rw [this, map_zero]
  have e1 : (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv z =
      (Fintype.card S : ℤ) • (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv
        (oneInvariant ℤ S.subtype) :=
    (congrArg (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv hz).trans
      (map_zsmul _ _ _)
  exact (map_zsmul _ _ _).symm.trans ((congrArg _ e1.symm).trans (hδ.trans h0))

noncomputable abbrev resClass : groupCohomology (res S.subtype M) 2 :=
  map S.subtype (𝟙 (res S.subtype M)) 2 u

noncomputable abbrev splitδ :
    groupCohomology (res S.subtype (augIdeal ℤ G)) 1 ⟶ groupCohomology (res S.subtype M) 2 :=
  δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 2 rfl

omit [Fintype S] in

theorem splitδ_augClass : splitδ M u S (augClass S) = resClass M u S :=
  δ_splittingSES_res_δ₀ M u S.subtype

theorem splitδ_injective (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    Function.Injective (splitδ M u S) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨m, rfl⟩ := exists_eq_zsmul_augClass S y
  rw [map_zsmul, splitδ_augClass] at hy
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 hy
  rw [h2, Nat.card_eq_fintype_card] at hd
  obtain ⟨t, rfl⟩ := hd
  rw [mul_comm, mul_zsmul, card_smul_augClass, zsmul_zero]

omit [Fintype S] in

theorem splitδ_surjective
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    Function.Surjective (splitδ M u S) := by
  intro y
  obtain ⟨m, rfl⟩ := h3 y
  exact ⟨m • augClass S, by rw [map_zsmul, splitδ_augClass]⟩

theorem isZero_groupCohomology_res_augIdeal_two :
    IsZero (groupCohomology (res S.subtype (augIdeal ℤ G)) 2) := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 1 2 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 1
      (isZero_groupCohomology_res_leftRegular S 2)
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep x
  have hz : IsZero (groupCohomology (res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
    isZero_H1_trivial_int (H := S)
  exact (congrArg _ (eq_zero_of_isZero hz z)).trans (map_zero _)

theorem isZero_groupCohomology_res_splittingModule_one
    (h1 : IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 1) :=
  isZero_X₂_of_injective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 h1
    (splitδ_injective M u S h2)

theorem isZero_groupCohomology_res_splittingModule_two
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 2) :=
  isZero_X₂_succ_of_surjective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1
    (isZero_groupCohomology_res_augIdeal_two S) (splitδ_surjective M u S h3)

omit [Fintype S] in

theorem cohTrivial_splittingModule
    (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : ∀ S : Subgroup G, addOrderOf (map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
      ∃ m : ℤ, y = m • map S.subtype (𝟙 (res S.subtype M)) 2 u) :
    CohTrivial (splittingModule M u) := by
  refine cohTrivial_of_forall_subgroup _ 1 fun T _ => ⟨?_, ?_⟩
  · exact (isZero_groupCohomology_res_splittingModule_one M u T (h1 T) (h2 T)).of_iso
      (tateIsoH _ 1 1 rfl)
  · exact (isZero_groupCohomology_res_splittingModule_two M u T (h3 T)).of_iso
      (tateIsoH _ (1 + 1) 2 (by norm_num))

end Tate

end GroundTheory.GroupCoh
