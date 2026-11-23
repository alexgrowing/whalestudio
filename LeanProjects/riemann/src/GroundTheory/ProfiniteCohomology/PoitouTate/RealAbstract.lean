import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.Abstract
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

attribute [local instance 2000] Rep.hV2

theorem finite_of_finite_addMonoidHom_zmod {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hA : ∀ a : A, n • a = 0) [Finite (A →+ ZMod n)] : Finite A := by
  refine Finite.of_injective (fun a (χ : A →+ ZMod n) => χ a) fun a b hab => ?_
  by_contra hne
  obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero (sub_ne_zero.2 hne)
  have hn : ∀ x, n • χ x = 0 := fun x => by rw [← map_nsmul, hA, map_zero]
  have h := congrFun hab (zmodOfQZ χ hn)
  apply hχ
  rw [map_sub, ← zmodToQZ_zmodOfQZ χ hn a, ← zmodToQZ_zmodOfQZ χ hn b]
  change zmodToQZ n (zmodOfQZ χ hn a) - zmodToQZ n (zmodOfQZ χ hn b) = 0
  rw [show zmodOfQZ χ hn a = zmodOfQZ χ hn b from h, sub_self]

section NormZero

variable {k F : Type} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F]

theorem normClass_zero (B : Rep k F) [IsDiscreteRep B] : normClass B 0 = 0 := by
  have h : (H0Iso B).hom.hom (normClass B 0) = 0 :=
    Subtype.ext ((H0Iso_hom_normClass B 0).trans (map_zero _))
  calc normClass B 0 = (H0Iso B).inv.hom ((H0Iso B).hom.hom (normClass B 0)) :=
        (hom_apply_hom_apply_of_comp_eq (H0Iso B).hom_inv_id _).symm
    _ = 0 := by rw [h, map_zero]

end NormZero

section Hypotheses

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G) [Fintype κ]
  {n : ℕ} [NeZero n] (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D]
  (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n)
  (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
  (invr : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom D) 2 →+ QZ)

structure TatePoitouTateHypotheses : Prop where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  duality : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
    ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective (tateCompactDualityMap φ ψ D h t M)

  finite_cohomology : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, r ≤ 2 → Finite (cohomology M r)

  localToCompact_two : ∀ ξ : ptTLocal φ ψ D 2,
    zmodToQZ n (t ((ptTLocalToCompact φ ψ D 2).hom ξ)) = ∑ v, inv v (ξ.1 v) + ∑ w, invr w (ξ.2 w)

  injective_res_zero : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M],
    Function.Injective fun (x : cohomology M 0) v => ptRes φ M v 0 x

  surjective_localPairing_zero : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))

  surjective_localPairing_two : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 2 + 0 = 2 from rfl))

  surjective_realPairing_zero : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ w,
      Function.Surjective (ptLocalPairing ψ D M invr w (show 0 + 2 = 2 from rfl))

  surjective_realPairing_two : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ w
      (χ : cohomology (Rep.res (ψ w).toMonoidHom (dualRep D M)) 0 →+ QZ),
      (∀ x ∈ normClasses (Rep.res (ψ w).toMonoidHom (dualRep D M)), χ x = 0) →
      ∃ ξ, ptLocalPairing ψ D M invr w (show 2 + 0 = 2 from rfl) ξ = χ

variable (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M]

def ptTDualToGlobal {r s : ℕ} (h : r + s = 3)
    (hb : Function.Bijective (ptTCompactDualMap φ ψ D M t h)) :
    (cohomology (dualRep D M) s →+ QZ) →+ cohomology M r :=
  (ptTToGlobal φ ψ M r).hom.toAddMonoidHom.comp (AddEquiv.ofBijective _ hb).symm.toAddMonoidHom

omit [Fintype ι] [Fintype κ] [IsDiscreteRep D] in

theorem bijective_tateCompactCohomologyResMap_of_comp_eq_id {A B : Rep (ULift.{0} ℤ) G}
    [IsDiscreteRep A] [IsDiscreteRep B] (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A)
    (hgf : g ≫ f = 𝟙 B) (m : ℕ) : Function.Bijective (tateCompactCohomologyResMap φ ψ f m) := by
  refine Function.bijective_iff_has_inverse.2 ⟨tateCompactCohomologyResMap φ ψ g m, fun x => ?_,
    fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp, hfg,
      tateCompactCohomologyResMap_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp, hgf,
      tateCompactCohomologyResMap_id]
    rfl

namespace TatePoitouTateHypotheses

variable {φ ψ D t inv invr} (P : TatePoitouTateHypotheses φ ψ D t inv invr)

include P in

theorem bijective_ptTCompactDualMap (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3)
    (hr : 1 ≤ r) : Function.Bijective (ptTCompactDualMap φ ψ D M t h) := by
  have hD := P.nonempty_addEquiv
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv hD
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : IsDiscreteRep (dualRep D M) := isDiscreteRep_dualRep D M
  have : IsDiscreteRep (dualRep D (dualRep D M)) := isDiscreteRep_dualRep D (dualRep D M)
  have hMD : ∀ f : dualRep D M, n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hMDD : ∀ f : dualRep D (dualRep D M), n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hφ := P.duality (dualRep D M) hMD (r := s) (s := r) (by omega) hr
  have : Finite (cohomology (dualRep D M) s) := P.finite_cohomology (dualRep D M) hMD s (by omega)
  have : Finite (tateCompactCohomologyRes φ ψ (dualRep D (dualRep D M)) r →+ ZMod n) :=
    Finite.of_surjective _ hφ.2
  have : Finite (tateCompactCohomologyRes φ ψ (dualRep D (dualRep D M)) r) :=
    finite_of_finite_addMonoidHom_zmod (nsmul_tateCompactCohomologyRes_eq_zero φ ψ hMDD r)
  have hflip := bijective_of_bijective_flip (nsmul_tateCompactCohomologyRes_eq_zero φ ψ hMDD r)
    (bilinAddHom (tateCompactCupRes φ ψ (dualEvalPairing D (dualRep D M)) h)) t hφ
  set e := Rep.isoOfBijective (toDualDual D M) (bijective_toDualDual hD hM)
  have hg := bijective_tateCompactCohomologyResMap_of_comp_eq_id φ ψ e.hom e.inv e.hom_inv_id
    e.inv_hom_id r
  have hμ : (toDualDual D M ⊗ₘ 𝟙 (dualRep D M)) ≫ dualEvalPairing D (dualRep D M) =
      (𝟙 M ⊗ₘ 𝟙 (dualRep D M)) ≫ evalPairing D M := by
    refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a f => rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  let β : tateCompactCohomologyRes φ ψ M r →+ (cohomology (dualRep D M) s →+ ZMod n) :=
    (AddMonoidHom.compHom t).comp (bilinAddHom (tateCompactCupRes φ ψ (evalPairing D M) h))
  have hβ : Function.Bijective β := by
    convert hflip.comp hg using 1
    funext x
    refine AddMonoidHom.ext fun y => ?_
    change t (tateCompactCupRes φ ψ (evalPairing D M) h x y) =
      t (tateCompactCupRes φ ψ (dualEvalPairing D (dualRep D M)) h
        ((tateCompactCohomologyResMap φ ψ (toDualDual D M) r).hom x) y)
    rw [tateCompactCupRes_tateCompactCohomologyResMap φ ψ _ (evalPairing D M) _ (𝟙 _) hμ,
      cohomologyMap_id]
    rfl
  exact bijective_compHom_zmodToQZ β (nsmul_cohomology_eq_zero _ hMD s) hβ

omit [NeZero n] in
include P in

theorem ptTCompactDualMap_ptTLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ptTLocal φ ψ M r) :
    ptTCompactDualMap φ ψ D M t h' ((ptTLocalToCompact φ ψ M r).hom ξ) =
      ptTLocalDualMap φ ψ D M inv invr h ξ := by
  refine AddMonoidHom.ext fun y => ?_
  rw [ptTCompactDualMap_apply, tateCompactCupRes_ptTLocalToCompact φ ψ D M h h',
    P.localToCompact_two, ptTLocalDualMap_apply]
  rfl

include P in

theorem exact_stage_succ (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + 1 + s = 2)
    (h' : r + 1 + 1 + s = 3) :
    Function.Exact (ptTGlobalToLocal φ ψ M (r + 1)).hom (ptTLocalDualMap φ ψ D M inv invr h) ∧
      Function.Exact (ptTLocalDualMap φ ψ D M inv invr h)
        (ptTDualToGlobal φ ψ D t M h' (P.bijective_ptTCompactDualMap M hM h' (by omega))) ∧
      Function.Exact (ptTDualToGlobal φ ψ D t M h' (P.bijective_ptTCompactDualMap M hM h' (by omega)))
        (ptTGlobalToLocal φ ψ M (r + 1 + 1)).hom := by
  set e := AddEquiv.ofBijective _ (P.bijective_ptTCompactDualMap M hM h' (by omega))
  have hlam : ptTLocalDualMap φ ψ D M inv invr h =
      e.toAddMonoidHom.comp (ptTLocalToCompact φ ψ M (r + 1)).hom.toAddMonoidHom :=
    AddMonoidHom.ext fun ξ => (P.ptTCompactDualMap_ptTLocalToCompact M h h' ξ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlam]
    exact exact_comp_addEquiv (ptTExact_local φ ψ M r) e
  · rw [hlam]
    exact exact_addEquiv_comp_comp_symm (g := (ptTLocalToCompact φ ψ M (r + 1)).hom.toAddMonoidHom)
      (ptTExact_compact φ ψ M (r + 1)) e
  · exact exact_comp_symm_addEquiv (ptTExact_global φ ψ M (r + 1)) e

end TatePoitouTateHypotheses

section DegreeZero

variable {φ ψ}

omit [Fintype ι] [Fintype κ] [Finite M] in

theorem exact_ptTLocalHatToCompact_ptTToGlobal :
    Function.Exact (ptTLocalHatToCompact φ ψ M) (ptTToGlobal φ ψ M 1).hom := fun z => by
  rw [ptTExact_compact φ ψ M 0 z]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ptTHatMk φ ψ M ξ, ptTLocalHatToCompact_hatMk φ ψ M ξ⟩
  · rintro ⟨ξ', rfl⟩
    obtain ⟨ξ, rfl⟩ := ptTHatMk_surjective φ ψ M ξ'
    exact ⟨ξ, (ptTLocalHatToCompact_hatMk φ ψ M ξ).symm⟩

omit [Fintype ι] [Fintype κ] [Finite M] in

theorem exact_ptTGlobalToLocalHat_ptTLocalHatToCompact :
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatToCompact φ ψ M) := fun ξ' => by
  obtain ⟨ξ, rfl⟩ := ptTHatMk_surjective φ ψ M ξ'
  rw [ptTLocalHatToCompact_hatMk]
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_localZero φ ψ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w).toMonoidHom M) (fun _ => 𝟙 _))
  constructor
  · intro h0
    obtain ⟨⟨x, e⟩, hxe⟩ := (hex ξ).1 h0
    refine ⟨x, ?_⟩
    rw [ptTGlobalToLocalHat_apply, ← sub_eq_zero, ← map_sub, ptTHatMk_eq_zero_iff]
    rw [← hxe, tateGlobalZeroToLocal_hom_apply, tateGlobalToLocal_hom_apply]
    refine ⟨sub_self _, fun w => ?_⟩
    change (globalToLocal ψ M _ (fun _ => 𝟙 _) 0).hom x w -
      ((globalToLocal ψ M _ (fun _ => 𝟙 _) 0).hom x w + normClass _ (e w)) ∈ _
    rw [sub_add_cancel_left]
    exact neg_mem (normClass_mem_normClasses _ (e w))
  · rintro ⟨x, hx⟩
    rw [ptTGlobalToLocalHat_apply, ← sub_eq_zero, ← map_sub] at hx
    have h1 := ptTLocalToCompact_of_hatMk_eq_zero φ ψ M _ hx
    rw [map_sub, sub_eq_zero] at h1
    rw [← h1]
    have hx0 : (tateGlobalZeroToLocal φ ψ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom M) (fun _ => 𝟙 _)).hom (x, 0) =
          (ptTGlobalToLocal φ ψ M 0).hom x := by
      rw [tateGlobalZeroToLocal_hom_apply, tateGlobalToLocal_hom_apply]
      refine Prod.ext rfl (funext fun w => ?_)
      change _ + normClass _ 0 = _
      rw [normClass_zero, add_zero]
    rw [← hx0]
    exact hom_apply_hom_apply_of_comp_eq (tateGlobalZeroToLocal_tateLocalToCompact φ ψ M _ _ _ _) _

end DegreeZero

namespace TatePoitouTateHypotheses

variable {φ ψ D t inv invr} (P : TatePoitouTateHypotheses φ ψ D t inv invr)

include P in

theorem exact_stage_zero (hM : ∀ m : M, n • m = 0) :
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatDualMap φ ψ D M inv invr) ∧
      Function.Exact (ptTLocalHatDualMap φ ψ D M inv invr)
        (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl)
          (P.bijective_ptTCompactDualMap M hM _ le_rfl)) ∧
      Function.Exact (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl)
          (P.bijective_ptTCompactDualMap M hM _ le_rfl)) (ptTGlobalToLocal φ ψ M 1).hom := by
  set e := AddEquiv.ofBijective _ (P.bijective_ptTCompactDualMap M hM (show 1 + 2 = 3 from rfl) le_rfl)
  have hlam : ptTLocalHatDualMap φ ψ D M inv invr = e.toAddMonoidHom.comp (ptTLocalHatToCompact φ ψ M) :=
    AddMonoidHom.ext fun ξ' => by
      obtain ⟨ξ, rfl⟩ := ptTHatMk_surjective φ ψ M ξ'
      rw [ptTLocalHatDualMap_hatMk, AddMonoidHom.comp_apply, ptTLocalHatToCompact_hatMk]
      exact (P.ptTCompactDualMap_ptTLocalToCompact M (show 0 + 2 = 2 from rfl)
        (show 0 + 1 + 2 = 3 from rfl) ξ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlam]
    exact exact_comp_addEquiv (exact_ptTGlobalToLocalHat_ptTLocalHatToCompact M) e
  · rw [hlam]
    exact exact_addEquiv_comp_comp_symm (g := ptTLocalHatToCompact φ ψ M)
      (exact_ptTLocalHatToCompact_ptTToGlobal M) e
  · exact exact_comp_symm_addEquiv (ptTExact_global φ ψ M 0) e

omit [NeZero n] [Finite M] in
include P in

theorem injective_ptTGlobalToLocalHat : Function.Injective (ptTGlobalToLocalHat φ ψ M) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => P.injective_res_zero M ?_
  have h1 := congrArg Prod.fst hx
  change (fun v => ptRes φ M v 0 x) = 0 at h1
  exact h1.trans (funext fun v => (map_zero (ptRes φ M v 0)).symm)

include P in

theorem surjective_ptTLocalDualMap_two (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl)) := by
  classical
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  intro χ
  obtain ⟨g, hg⟩ := QZ.exists_comp_eq_of_injective (ptTGlobalToLocalHat φ ψ (dualRep D M))
    (P.injective_ptTGlobalToLocalHat (dualRep D M)) χ
  have hv : ∀ v, ∃ ξv, ptLocalPairing φ D M inv v (show 2 + 0 = 2 from rfl) ξv =
      g.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single
        (fun v => cohomology (Rep.res (φ v).toMonoidHom (dualRep D M)) 0) v)) :=
    fun v => P.surjective_localPairing_two M hM v _
  have hw : ∀ w, ∃ ξw, ptLocalPairing ψ D M invr w (show 2 + 0 = 2 from rfl) ξw =
      g.comp ((AddMonoidHom.inr _ _).comp ((AddMonoidHom.single
        (fun w => cohomologyTateZero (Rep.res (ψ w).toMonoidHom (dualRep D M))) w).comp
          (normClasses (Rep.res (ψ w).toMonoidHom (dualRep D M))).mkQ.toAddMonoidHom)) :=
    fun w => P.surjective_realPairing_two M hM w _ fun x hx => by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
  choose ξ₁ hξ₁ using hv
  choose ξ₂ hξ₂ using hw
  refine ⟨(ξ₁, ξ₂), AddMonoidHom.ext fun y => ?_⟩
  have hdec : ptTGlobalToLocalHat φ ψ (dualRep D M) y =
      (∑ v, AddMonoidHom.inl _ _ (Pi.single v (ptRes φ (dualRep D M) v 0 y))) +
        ∑ w, AddMonoidHom.inr _ _
          (Pi.single w (Submodule.Quotient.mk (p := normClasses (Rep.res (ψ w).toMonoidHom (dualRep D M)))
            (ptRes ψ (dualRep D M) w 0 y))) := by
    rw [ptTGlobalToLocalHat_apply, ptTGlobalToLocal_apply, ptTHatMk_apply, ← map_sum, ← map_sum]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, add_zero]
      exact (Finset.univ_sum_single _).symm
    · simp only [Prod.snd_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, zero_add]
      exact (Finset.univ_sum_single _).symm
  rw [ptTLocalDualMap_apply, ← hg, AddMonoidHom.comp_apply, hdec, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [hξ₁]
    rfl
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [hξ₂]
    rfl

include P in

theorem surjective_ptTLocalToCompact_two (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (ptTLocalToCompact φ ψ M 2).hom := fun z => by
  have hb := P.bijective_ptTCompactDualMap M hM (show 3 + 0 = 3 from rfl) (by norm_num)
  obtain ⟨ξ, hξ⟩ := P.surjective_ptTLocalDualMap_two M hM (ptTCompactDualMap φ ψ D M t _ z)
  refine ⟨ξ, hb.1 ?_⟩
  rw [P.ptTCompactDualMap_ptTLocalToCompact M (show 2 + 0 = 2 from rfl)
    (show 2 + 1 + 0 = 3 from rfl), hξ]

include P in

theorem injective_ptTGlobalToLocal_three (hM : ∀ m : M, n • m = 0) :
    Function.Injective (ptTGlobalToLocal φ ψ M 3).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := (ptTExact_global φ ψ M 2 x).1 hx
  obtain ⟨ξ, rfl⟩ := P.surjective_ptTLocalToCompact_two M hM z
  exact (ptTExact_compact φ ψ M 2 _).2 ⟨ξ, rfl⟩

include P in

theorem nineTerm (hM : ∀ m : M, n • m = 0) :
    Function.Injective (ptTGlobalToLocalHat φ ψ M) ∧
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatDualMap φ ψ D M inv invr) ∧
    Function.Exact (ptTLocalHatDualMap φ ψ D M inv invr)
      (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl) (P.bijective_ptTCompactDualMap M hM _ le_rfl)) ∧
    Function.Exact (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl)
        (P.bijective_ptTCompactDualMap M hM _ le_rfl)) (ptTGlobalToLocal φ ψ M 1).hom ∧
    Function.Exact (ptTGlobalToLocal φ ψ M 1).hom
      (ptTLocalDualMap φ ψ D M inv invr (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptTLocalDualMap φ ψ D M inv invr (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal φ ψ D t M (show 2 + 1 = 3 from rfl)
        (P.bijective_ptTCompactDualMap M hM _ (by norm_num))) ∧
    Function.Exact (ptTDualToGlobal φ ψ D t M (show 2 + 1 = 3 from rfl)
        (P.bijective_ptTCompactDualMap M hM _ (by norm_num))) (ptTGlobalToLocal φ ψ M 2).hom ∧
    Function.Exact (ptTGlobalToLocal φ ψ M 2).hom
      (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl)) := by
  obtain ⟨a0, b0, c0⟩ := P.exact_stage_zero M hM
  obtain ⟨a1, b1, c1⟩ := P.exact_stage_succ M hM (r := 0) (s := 1) rfl rfl
  obtain ⟨a2, -, -⟩ := P.exact_stage_succ M hM (r := 1) (s := 0) rfl rfl
  exact ⟨P.injective_ptTGlobalToLocalHat M, a0, b0, c0, a1, b1, c1, a2,
    P.surjective_ptTLocalDualMap_two M hM⟩

include P in

theorem bijective_ptTShaPairing (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptTShaPairing φ ψ D M t) := by
  classical
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have hψ := P.bijective_ptTCompactDualMap M hM (show 1 + 2 = 3 from rfl) le_rfl
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun χ => ?_⟩
  ·
    set f := ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) (ptTShaLift φ ψ M x)
    have hker : (ptTGlobalToLocal φ ψ (dualRep D M) 2).hom.toAddMonoidHom.ker ≤ f.ker := fun y hy =>
      AddMonoidHom.mem_ker.2 (DFunLike.congr_fun hx ⟨y, hy⟩)
    obtain ⟨g, hg⟩ := QZ.exists_comp_eq_of_ker_le
      (ptTGlobalToLocal φ ψ (dualRep D M) 2).hom.toAddMonoidHom f hker
    have hv : ∀ v, ∃ ξv, ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl) ξv =
        g.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single
          (fun v => cohomology (Rep.res (φ v).toMonoidHom (dualRep D M)) 2) v)) :=
      fun v => P.surjective_localPairing_zero M hM v _
    have hw : ∀ w, ∃ ξw, ptLocalPairing ψ D M invr w (show 0 + 2 = 2 from rfl) ξw =
        g.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.single
          (fun w => cohomology (Rep.res (ψ w).toMonoidHom (dualRep D M)) 2) w)) :=
      fun w => P.surjective_realPairing_zero M hM w _
    choose ξ₁ hξ₁ using hv
    choose ξ₂ hξ₂ using hw
    have hf : ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl) (ξ₁, ξ₂) = f := by
      refine AddMonoidHom.ext fun y => ?_
      have hdec : (ptTGlobalToLocal φ ψ (dualRep D M) 2).hom y =
          (∑ v, AddMonoidHom.inl _ _ (Pi.single v (ptRes φ (dualRep D M) v 2 y))) +
            ∑ w, AddMonoidHom.inr _ _ (Pi.single w (ptRes ψ (dualRep D M) w 2 y)) := by
        rw [ptTGlobalToLocal_apply, ← map_sum, ← map_sum]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, add_zero]
          exact (Finset.univ_sum_single _).symm
        · simp only [Prod.snd_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, zero_add]
          exact (Finset.univ_sum_single _).symm
      rw [ptTLocalDualMap_apply, ← hg, AddMonoidHom.comp_apply]
      change _ = g ((ptTGlobalToLocal φ ψ (dualRep D M) 2).hom y)
      rw [hdec, map_add, map_sum, map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun v _ => ?_
        rw [hξ₁]
        rfl
      · refine Finset.sum_congr rfl fun w _ => ?_
        rw [hξ₂]
        rfl
    rw [← P.ptTCompactDualMap_ptTLocalToCompact M _ (show 0 + 1 + 2 = 3 from rfl)] at hf
    have hx' : (ptTLocalToCompact φ ψ M 0).hom (ξ₁, ξ₂) = ptTShaLift φ ψ M x := hψ.1 hf
    apply Subtype.ext
    rw [← ptTToGlobal_ptTShaLift φ ψ M x, ← hx']
    exact (ptTExact_compact φ ψ M 0 _).2 ⟨(ξ₁, ξ₂), rfl⟩
  · obtain ⟨f, hf⟩ := QZ.exists_comp_eq_of_injective (ptTSha φ ψ (dualRep D M) 2).subtype
      Subtype.val_injective χ
    obtain ⟨x, hx⟩ := hψ.2 f
    refine ⟨⟨_, ptTToGlobal_mem_ptTSha φ ψ M (r := 0) x⟩, AddMonoidHom.ext fun y => ?_⟩
    rw [ptTShaPairing_apply, hx, ← hf]
    rfl

include P in

theorem sha (hM : ∀ m : M, n • m = 0) :
    Finite (ptTSha φ ψ M 1) ∧ Finite (ptTSha φ ψ (dualRep D M) 2) ∧
      Function.Bijective (ptTShaPairing φ ψ D M t) ∧
        Function.Bijective (ptTShaPairing φ ψ D M t).flip := by
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have := P.finite_cohomology M hM 1 (by norm_num)
  have := P.finite_cohomology (dualRep D M) (nsmul_dualRep_eq_zero hnD) 2 le_rfl
  have h1 : Finite (ptTSha φ ψ M 1) := Finite.of_injective _ Subtype.val_injective
  have h2 : Finite (ptTSha φ ψ (dualRep D M) 2) := Finite.of_injective _ Subtype.val_injective
  have hb := P.bijective_ptTShaPairing M hM
  exact ⟨h1, h2, hb, bijective_flip_of_bijective_qz _ hb⟩

end TatePoitouTateHypotheses

end Hypotheses

end GroundTheory.ProfCoh
