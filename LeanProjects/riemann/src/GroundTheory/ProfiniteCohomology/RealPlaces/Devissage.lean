import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.DevissageNatural
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance 2000] Rep.hV2

section Core

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] {ψ : ∀ w, F w →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace TateCompactDualityHypotheses

variable (H : TateCompactDualityHypotheses φ ψ n D t U₀)

include H in
theorem finite_D : Finite D :=
  finite_of_nonempty_addEquiv H.nonempty_addEquiv

include H in
theorem nsmul_D (d : D) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d

include H in

theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) G) (_ : IsDiscreteRep I) (_ : IsDiscreteRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
        Function.Bijective (tateCompactDualityMap φ ψ D h t I) := by
  obtain ⟨W, hW, J, _, i, hi⟩ := exists_injective_biproduct_coind_le (n := n) U₀ M hM
  have hφ : ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective (tateCompactDualityMap φ ψ D h t
      (⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) :
        Rep.{u} (ULift.{u} ℤ) G)) :=
    fun h hs => bijective_tateCompactDualityMap_biproduct φ ψ D h t _
      fun _ => H.bijective_coind W hW h hs
  have hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype
      (zmodRep.{u} (W : Subgroup G) n) : Rep.{u} (ULift.{u} ℤ) G) : Type u), n • x = 0 := by
    intro x
    rw [biproduct_eq_sum _ x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]
  have hmono : Mono i := (Rep.mono_iff_injective i).2 hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono
      (inferInstance : Epi (cokernel.π i))
  have hQd : IsDiscreteRep (cokernel i) := isDiscreteRep_X₃_of_shortExact hS
  have hsurj : Function.Surjective (cokernel.π i).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) G) : Type u) :=
    Finite.of_surjective _ hsurj
  refine ⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i,
    cokernel.condition i, hS, hnI, fun x => ?_, hφ⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← map_nsmul, hnI, map_zero]

end TateCompactDualityHypotheses

end Core

section Steps

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] {ψ : ∀ w, F w →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace TateCompactDualityHypotheses

variable (H : TateCompactDualityHypotheses φ ψ n D t U₀)

include H in

theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Injective (tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t I ((cohomologyMap i 0).hom x) = 0 := by
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D (rfl : 0 + 3 = 3) t i x y, hx]
    rfl
  have h2 : (cohomologyMap i 0).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI (rfl : 0 + 3 = 3) (by norm_num)).1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

include H in

theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (tateCompactCohomologyResMap φ ψ (dualMap D i) 3).hom := by
    intro y
    have : Subsingleton (tateCompactCohomologyRes φ ψ (dualRep D Q) 4) :=
      H.subsingleton_four (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)
    exact (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₃ φ ψ hT 3) y
      (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := (hI (rfl : 0 + 3 = 3) (by norm_num)).2
    (l.comp (tateCompactCohomologyResMap φ ψ (dualMap D i) 3).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D (rfl : 0 + 3 = 3) t p v y, hv]
    change l ((tateCompactCohomologyResMap φ ψ (dualMap D p) 3 ≫
      tateCompactCohomologyResMap φ ψ (dualMap D i) 3).hom y) = 0
    rw [← tateCompactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      tateCompactCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← tateCompactDualityMap_cohomologyMap φ ψ D (rfl : 0 + 3 = 3) t i m z]
  change tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t I ((cohomologyMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

include H in
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t M) :=
  ⟨H.injective_zero M hM, H.surjective_zero M hM⟩

variable {r s : ℕ} (h₁ : r + 1 + s = 3) (h₀ : r + (s + 1) = 3) (hs : 1 ≤ s)

include H hs in

theorem injective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (tateCompactDualityMap φ ψ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Injective (tateCompactDualityMap φ ψ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : tateCompactDualityMap φ ψ D h₁ t I ((cohomologyMap i (r + 1)).hom x) = 0 := by
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D h₁ t i x y, hx]
    rfl
  have hix : (cohomologyMap i (r + 1)).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI h₁ hs).1 _ h1
  obtain ⟨q, hq⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS r (r + 1) rfl) x hix
  have hker : ((tateCompactCohomologyResMap φ ψ (dualMap D p) (s + 1)).hom.toAddMonoidHom).ker ≤
      (tateCompactDualityMap φ ψ D h₀ t Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₁ φ ψ hT s) z hz
    rw [AddMonoidHom.mem_ker, ← hy]
    have e := tateCompactDualityMap_δ φ ψ D t hS hT h₁ h₀ q y
    change tateCompactDualityMap φ ψ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
    rw [hq, hx, AddMonoidHom.zero_apply] at e
    exact eq_zero_of_neg_neg_one_pow_zsmul s e.symm
  obtain ⟨χ, hχ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_tateCompactCohomologyRes_eq_zero φ ψ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨v, hv⟩ := (ih I hnI).2 χ
  have hpv : (cohomologyMap p r).hom v = q := by
    apply (ih Q hnQ).1
    ext z
    rw [tateCompactDualityMap_cohomologyMap φ ψ D h₀ t p v z, hv, ← hχ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun F => F.hom v) (comp_δ hS r (r + 1) rfl)

include H hs in

theorem surjective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (tateCompactDualityMap φ ψ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (tateCompactDualityMap φ ψ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := (hI h₁ hs).2 (l.comp (tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p (r + 1)).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_succ h₁ h₀ hs ih Q hnQ)
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D h₁ t p v y, hv]
    change l ((tateCompactCohomologyResMap φ ψ (dualMap D p) s ≫
      tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom y) = 0
    rw [← tateCompactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      tateCompactCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (r + 1)) v hpv
  set ν := l - tateCompactDualityMap φ ψ D h₁ t M x' with hν
  have hker : ((tateCompactδRes φ ψ hT s).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₃ φ ψ hT s) y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom z) =
      tateCompactDualityMap φ ψ D h₁ t M x' ((tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom z)
    rw [← tateCompactDualityMap_cohomologyMap φ ψ D h₁ t i x' z]
    change _ = tateCompactDualityMap φ ψ D h₁ t I ((cohomologyMap S.f (r + 1)).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨χ, hχ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_tateCompactCohomologyRes_eq_zero φ ψ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨q, hq⟩ := (ih Q hnQ).2 χ
  refine ⟨x' + (-(-1 : ℤ) ^ s) • (δ hS r (r + 1) rfl).hom q, ?_⟩
  ext y
  have e := tateCompactDualityMap_δ φ ψ D t hS hT h₁ h₀ q y
  change tateCompactDualityMap φ ψ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
  have hχy : χ ((tateCompactδRes φ ψ hT s).hom y) = ν y := congrArg (fun f => f y) hχ
  rw [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, e, hq,
    neg_neg_one_pow_zsmul_zsmul]
  change _ + χ ((tateCompactδRes φ ψ hT s).hom y) = l y
  rw [hχy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

include H hs in
theorem bijective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (tateCompactDualityMap φ ψ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (tateCompactDualityMap φ ψ D h₁ t M) :=
  ⟨H.injective_succ h₁ h₀ hs ih M hM, H.surjective_succ h₁ h₀ hs ih M hM⟩

end TateCompactDualityHypotheses

end Steps

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] {ψ : ∀ w, F w →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace TateCompactDualityHypotheses

variable (H : TateCompactDualityHypotheses φ ψ n D t U₀)

include H in

theorem bijective_tateCompactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t M) := by
  have b0 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_zero M hM
  have b1 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) =>
      H.bijective_succ (r := 0) (s := 2) rfl rfl (by norm_num) b0 M hM
  have b2 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) =>
      H.bijective_succ (r := 1) (s := 1) rfl rfl (by norm_num) b1 M hM
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 3) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) := by omega
  · exact b0 M hM
  · exact b1 M hM
  · exact b2 M hM

end TateCompactDualityHypotheses

end Main

end GroundTheory.ProfCoh
