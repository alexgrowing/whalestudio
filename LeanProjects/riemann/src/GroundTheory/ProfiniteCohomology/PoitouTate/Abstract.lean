import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section ExactTransport

variable {A B X Y C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup C]

omit [AddCommGroup A] in

theorem exact_comp_addEquiv {f : A → B} {g : B →+ X} (hfg : Function.Exact f g) (e : X ≃+ Y) :
    Function.Exact f (e.toAddMonoidHom.comp g) := fun b => by
  rw [← hfg b, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff]

theorem exact_addEquiv_comp_comp_symm {g : B →+ X} {c : X → C} (hgc : Function.Exact g c)
    (e : X ≃+ Y) : Function.Exact (e.toAddMonoidHom.comp g) (c ∘ e.symm) := fun y => by
  rw [Function.comp_apply, hgc]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simp [hb]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by simp⟩

omit [AddCommGroup C] in

theorem exact_comp_symm_addEquiv {c : X → C} {β : C → A} (hcβ : Function.Exact c β) (e : X ≃+ Y) :
    Function.Exact (c ∘ e.symm) β := fun x => by
  rw [hcβ x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e z, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

theorem bijective_compHom_zmodToQZ {n : ℕ} [NeZero n] (β : X →+ Y →+ ZMod n)
    (hY : ∀ y : Y, n • y = 0) (hβ : Function.Bijective β) :
    Function.Bijective ((AddMonoidHom.compHom (zmodToQZ n)).comp β) := by
  refine ⟨fun x₁ x₂ hx => hβ.1 (AddMonoidHom.ext fun y => zmodToQZ_injective ?_), fun χ => ?_⟩
  · exact DFunLike.congr_fun hx y
  · have hχ : ∀ y, n • χ y = 0 := fun y => by rw [← map_nsmul, hY, map_zero]
    obtain ⟨x, hx⟩ := hβ.2 (zmodOfQZ χ hχ)
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    change zmodToQZ n (β x y) = χ y
    rw [hx, zmodToQZ_zmodOfQZ]

theorem bijective_flip_of_bijective_qz [Finite X] [Finite Y] (β : X →+ Y →+ QZ)
    (hβ : Function.Bijective β) : Function.Bijective β.flip := by
  have hinj : Function.Injective β.flip := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    by_contra hne
    obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero hne
    obtain ⟨x, rfl⟩ := hβ.2 χ
    exact hχ (DFunLike.congr_fun hy x)
  refine hinj.bijective_of_nat_card_le ?_
  rw [QZ.card_hom, ← QZ.card_hom (G := Y)]
  exact (Nat.card_congr (Equiv.ofBijective _ hβ)).le

end ExactTransport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
  (t : compactCohomologyRes φ D 3 →+ ZMod n)
  (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)

structure PoitouTateHypotheses : Prop where

  compactDuality : ∃ U₀ : OpenSubgroup G, CompactDualityHypotheses φ n D t U₀

  finite_cohomology : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, Finite (cohomology M r)

  finite_compactCohomology : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, Finite (compactCohomologyRes φ M r)

  subsingleton_three : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)

  localToCompact_two : ∀ ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2,
    zmodToQZ n (t ((localToCompact φ D _ (fun _ => 𝟙 _) 2).hom ξ)) = ∑ v, inv v (ξ v)

  surjective_localPairing : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))

variable (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]

def ptDualToGlobal {r s : ℕ} (h : r + s = 3)
    (hψ : Function.Bijective (ptCompactDualMap φ D M t h)) :
    (cohomology (dualRep D M) s →+ QZ) →+ cohomology M r :=
  (ptCompactToGlobal φ M r).hom.toAddMonoidHom.comp (AddEquiv.ofBijective _ hψ).symm.toAddMonoidHom

namespace PoitouTateHypotheses

variable {φ D t inv} (P : PoitouTateHypotheses φ D t inv)

include P in

theorem bijective_ptCompactDualMap (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (ptCompactDualMap φ D M t h) := by
  obtain ⟨U₀, H⟩ := P.compactDuality
  have hD := H.nonempty_addEquiv
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv hD
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : IsDiscreteRep (dualRep D M) := isDiscreteRep_dualRep D M
  have : IsDiscreteRep (dualRep D (dualRep D M)) := isDiscreteRep_dualRep D (dualRep D M)
  have hMD : ∀ f : dualRep D M, n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hMDD : ∀ f : dualRep D (dualRep D M), n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hφ := H.bijective_compactDualityMap (dualRep D M) hMD (r := s) (s := r) (by omega)
  have := P.finite_compactCohomology (dualRep D (dualRep D M)) hMDD r
  have hflip := bijective_of_bijective_flip (nsmul_compactCohomologyRes_eq_zero φ hMDD r)
    (bilinAddHom (compactCupRes φ (dualEvalPairing D (dualRep D M)) h)) t hφ
  set e := Rep.isoOfBijective (toDualDual D M) (bijective_toDualDual hD hM)
  have hg := bijective_compactCohomologyResMap_of_comp_eq_id φ e.hom e.inv e.hom_inv_id e.inv_hom_id r
  have hμ : (toDualDual D M ⊗ₘ 𝟙 (dualRep D M)) ≫ dualEvalPairing D (dualRep D M) =
      (𝟙 M ⊗ₘ 𝟙 (dualRep D M)) ≫ evalPairing D M := by
    refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a f => rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  let β : compactCohomologyRes φ M r →+ (cohomology (dualRep D M) s →+ ZMod n) :=
    (AddMonoidHom.compHom t).comp (bilinAddHom (compactCupRes φ (evalPairing D M) h))
  have hβ : Function.Bijective β := by
    convert hflip.comp hg using 1
    funext x
    refine AddMonoidHom.ext fun y => ?_
    change t (compactCupRes φ (evalPairing D M) h x y) =
      t (compactCupRes φ (dualEvalPairing D (dualRep D M)) h
        ((compactCohomologyResMap φ (toDualDual D M) r).hom x) y)
    rw [compactCupRes_compactCohomologyResMap φ _ (evalPairing D M) _ (𝟙 _) hμ, cohomologyMap_id]
    rfl
  exact bijective_compHom_zmodToQZ β (nsmul_cohomology_eq_zero _ hMD s) hβ

include P in

theorem subsingleton_compactCohomologyRes_zero (hM : ∀ m : M, n • m = 0) :
    Subsingleton (compactCohomologyRes φ M 0) := by
  obtain ⟨U₀, H⟩ := P.compactDuality
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv H.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have hb := P.bijective_ptCompactDualMap M hM (show 0 + 3 = 3 from rfl)
  have : Subsingleton (cohomology (dualRep D M) 3) :=
    P.subsingleton_three (dualRep D M) (nsmul_dualRep_eq_zero hnD)
  refine ⟨fun a b => hb.1 (AddMonoidHom.ext fun y => ?_)⟩
  rw [Subsingleton.elim y 0, map_zero, map_zero]

omit [NeZero n] in
include P in

theorem ptCompactDualMap_ptLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom M) r) :
    ptCompactDualMap φ D M t h' ((ptLocalToCompact φ M r).hom ξ) = ptLocalDualMap φ D M inv h ξ := by
  refine AddMonoidHom.ext fun y => ?_
  rw [ptCompactDualMap_apply, compactCupRes_ptLocalToCompact φ D M h h', P.localToCompact_two,
    ptLocalDualMap_apply]
  rfl

include P in

theorem exact_stage (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3) :
    Function.Exact (ptGlobalToLocal φ M r).hom (ptLocalDualMap φ D M inv h) ∧
      Function.Exact (ptLocalDualMap φ D M inv h)
        (ptDualToGlobal φ D t M h' (P.bijective_ptCompactDualMap M hM h')) ∧
      Function.Exact (ptDualToGlobal φ D t M h' (P.bijective_ptCompactDualMap M hM h'))
        (ptGlobalToLocal φ M (r + 1)).hom := by
  set e := AddEquiv.ofBijective _ (P.bijective_ptCompactDualMap M hM h')
  have hlam : ptLocalDualMap φ D M inv h = e.toAddMonoidHom.comp (ptLocalToCompact φ M r).hom.toAddMonoidHom :=
    AddMonoidHom.ext fun ξ => (P.ptCompactDualMap_ptLocalToCompact M h h' ξ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlam]
    exact exact_comp_addEquiv (ptExact_local φ M r) e
  · rw [hlam]
    exact exact_addEquiv_comp_comp_symm (g := (ptLocalToCompact φ M r).hom.toAddMonoidHom)
      (ptExact_compact φ M r) e
  · exact exact_comp_symm_addEquiv (ptExact_global φ M (r + 1)) e

include P in

theorem injective_ptGlobalToLocal_zero (hM : ∀ m : M, n • m = 0) :
    Function.Injective (ptGlobalToLocal φ M 0).hom := by
  have := P.subsingleton_compactCohomologyRes_zero M hM
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := (ptExact_global φ M 0 x).1 hx
  rw [Subsingleton.elim z 0]
  exact map_zero _

include P in

theorem surjective_ptLocalDualMap_two (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) := by
  intro χ
  set e := AddEquiv.ofBijective _ (P.bijective_ptCompactDualMap M hM (show 2 + 1 + 0 = 3 from rfl))
  have := P.subsingleton_three M hM
  obtain ⟨ξ, hξ⟩ := (ptExact_compact φ M 2 (e.symm χ)).1 (Subsingleton.elim _ _)
  refine ⟨ξ, ?_⟩
  rw [← P.ptCompactDualMap_ptLocalToCompact M _ (show 2 + 1 + 0 = 3 from rfl), hξ]
  exact e.apply_symm_apply χ

include P in

theorem nineTerm (hM : ∀ m : M, n • m = 0) :
    Function.Injective (ptGlobalToLocal φ M 0).hom ∧
    Function.Exact (ptGlobalToLocal φ M 0).hom (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl))
      (ptDualToGlobal φ D t M (show 1 + 2 = 3 from rfl) (P.bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal φ D t M (show 1 + 2 = 3 from rfl)
        (P.bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal φ M 1).hom ∧
    Function.Exact (ptGlobalToLocal φ M 1).hom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl))
      (ptDualToGlobal φ D t M (show 2 + 1 = 3 from rfl) (P.bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal φ D t M (show 2 + 1 = 3 from rfl)
        (P.bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal φ M 2).hom ∧
    Function.Exact (ptGlobalToLocal φ M 2).hom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) := by
  obtain ⟨a0, b0, c0⟩ := P.exact_stage M hM (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 3 from rfl)
  obtain ⟨a1, b1, c1⟩ := P.exact_stage M hM (show 1 + 1 = 2 from rfl) (show 1 + 1 + 1 = 3 from rfl)
  obtain ⟨a2, -, -⟩ := P.exact_stage M hM (show 2 + 0 = 2 from rfl) (show 2 + 1 + 0 = 3 from rfl)
  exact ⟨P.injective_ptGlobalToLocal_zero M hM, a0, b0, c0, a1, b1, c1, a2,
    P.surjective_ptLocalDualMap_two M hM⟩

include P in

theorem bijective_ptShaPairing (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptShaPairing φ D M t) := by
  classical
  obtain ⟨U₀, H⟩ := P.compactDuality
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have hMD : ∀ f : dualRep D M, n • f = 0 := nsmul_dualRep_eq_zero hnD
  have : Finite D := finite_of_nonempty_addEquiv H.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have hψ := P.bijective_ptCompactDualMap M hM (show 1 + 2 = 3 from rfl)
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun χ => ?_⟩
  ·
    set f := ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) (ptShaLift φ M x)
    have hker : (ptGlobalToLocal φ (dualRep D M) 2).hom.toAddMonoidHom.ker ≤ f.ker := fun y hy =>
      AddMonoidHom.mem_ker.2 (DFunLike.congr_fun hx ⟨y, hy⟩)
    obtain ⟨g, hg⟩ := QZ.exists_comp_eq_of_ker_le
      (ptGlobalToLocal φ (dualRep D M) 2).hom.toAddMonoidHom f hker
    have hloc : ∀ v, ∃ ξv, ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl) ξv =
        g.comp (AddMonoidHom.single (fun w => cohomology (Rep.res (φ w).toMonoidHom (dualRep D M)) 2) v) :=
      fun v => P.surjective_localPairing M hM v _
    choose ξ hξ using hloc
    have hf : ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl) ξ = f := by
      refine AddMonoidHom.ext fun y => ?_
      rw [ptLocalDualMap_apply, ← hg, AddMonoidHom.comp_apply]
      simp_rw [hξ, AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
      rw [← map_sum, Finset.univ_sum_single]
      rfl
    rw [← P.ptCompactDualMap_ptLocalToCompact M _ (show 0 + 1 + 2 = 3 from rfl)] at hf
    have hx' : (ptLocalToCompact φ M 0).hom ξ = ptShaLift φ M x := hψ.1 hf
    apply Subtype.ext
    rw [← ptCompactToGlobal_ptShaLift φ M x, ← hx']
    exact (ptExact_compact φ M 0 _).2 ⟨ξ, rfl⟩
  · obtain ⟨f, hf⟩ := QZ.exists_comp_eq_of_injective (ptSha φ (dualRep D M) 2).subtype
      Subtype.val_injective χ
    obtain ⟨x, hx⟩ := hψ.2 f
    refine ⟨⟨_, ptCompactToGlobal_mem_ptSha φ M x⟩, AddMonoidHom.ext fun y => ?_⟩
    rw [ptShaPairing_apply, hx, ← hf]
    rfl

include P in

theorem sha (hM : ∀ m : M, n • m = 0) :
    Finite (ptSha φ M 1) ∧ Finite (ptSha φ (dualRep D M) 2) ∧
      Function.Bijective (ptShaPairing φ D M t) ∧ Function.Bijective (ptShaPairing φ D M t).flip := by
  obtain ⟨U₀, H⟩ := P.compactDuality
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv H.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have := P.finite_cohomology M hM 1
  have := P.finite_cohomology (dualRep D M) (nsmul_dualRep_eq_zero hnD) 2
  have h1 : Finite (ptSha φ M 1) := Finite.of_injective _ Subtype.val_injective
  have h2 : Finite (ptSha φ (dualRep D M) 2) := Finite.of_injective _ Subtype.val_injective
  have hb := P.bijective_ptShaPairing M hM
  exact ⟨h1, h2, hb, bijective_flip_of_bijective_qz _ hb⟩

end PoitouTateHypotheses

end GroundTheory.ProfCoh
