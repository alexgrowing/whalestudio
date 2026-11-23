import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

namespace SerreCriterion

variable {X : Scheme.{0}}

theorem exists_germ_eq_of_support_subset {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    (hF : support F ⊆ {y}) (t : (F.presheaf.stalk y :)) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t := by
  classical
  by_cases h : y ∈ support F
  · obtain ⟨s, hs⟩ := (germ_support_bijective (F := F) ((Set.finite_singleton y).subset hF)
      fun x hx => by rw [show x = y from hF hx]; exact hy).2
      (Function.update (fun _ => 0) ⟨y, h⟩ t)
    refine ⟨s, (congrFun hs ⟨y, h⟩).trans ?_⟩
    simp
  · exact ⟨0, (notMem_support_iff.1 h).elim _ _⟩

theorem support_pushforward_subscheme_subset (Y : X.IdealSheafData) :
    support ((Scheme.Modules.pushforward Y.subschemeι).obj (structureModule Y.subscheme)) ⊆
      Y.support := by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t => ?_) hx
  obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem (U := Y.support.compl) h t
  have e : Y.subschemeι ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun z hz => (hV hz (Y.range_subschemeι.le ⟨z, rfl⟩)).elim
  have : Subsingleton Γ(Y.subscheme, Y.subschemeι ⁻¹ᵁ V) := by
    rw [e]
    infer_instance
  have hs : s = 0 := this.elim s 0
  rw [hs, map_zero]

theorem not_isUnit_of_toSubscheme_eq_zero (Y : X.IdealSheafData) {y : X} (hy : y ∈ Y.support)
    (g : ((structureModule X).presheaf.stalk y :)) (hg : stalkLinear (toSubscheme Y) y g = 0) :
    ¬ IsUnit (structureModuleStalkEquiv y g) := by
  have hex := (exact_iff_stalkLinear (ShortComplex.mk (kernel.ι (toSubscheme Y)) (toSubscheme Y)
    (kernel.condition _))).1 (ShortComplex.exact_kernel _) y
  obtain ⟨u, rfl⟩ := (hex g).1 hg
  obtain ⟨V, hV, u, rfl⟩ := (idealModule Y).presheaf.exists_germ_eq u
  intro hu
  refine notMem_support_of_mem_basicOpen Y u ((X.mem_basicOpen _ y hV).2 ?_) hy
  rw [← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
  exact hu

theorem exists_mem_nonzeroLocus {M : LB X} (hM : M.IsLB) {J : X.Modules}
    (j : J ⟶ structureModule X) (Y : X.IdealSheafData) {y : X} (hY : (Y.support : Set X) = {y})
    (h : Subsingleton (coh (twist (kernel (j ≫ toSubscheme Y)) M) 1))
    {U : X.Opens} (hU : y ∈ U) (t : Γ(J, U))
    (ht : structureModuleSectionsEquiv U (j.app U t) = 1) :
    ∃ a : Γ(twist J M, ⊤), y ∈ nonzeroLocus (secOfTwist j a) := by
  set φ := j ≫ toSubscheme Y with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor M)).ShortExact := Twist.shortExact_map hM hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hyc : IsClosed ({y} : Set X) := hY ▸ Y.support.isClosed
  have hQ : support (twist S.X₃ M) ⊆ {y} := by
    rw [support_twist hM, ← hY]
    refine fun x hx => support_pushforward_subscheme_subset Y ?_
    have := mem_support_iff.1 hx
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) x).nontrivial
  obtain ⟨c, hc⟩ := exists_chart hM y
  obtain ⟨b, hb⟩ := exists_germ_eq_of_support_subset hyc hQ
    ((stalkEquiv S.X₃ hM c hc).symm (stalkLinear S.g y (J.presheaf.germ U y hU t)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨a, basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ y hc).2 ?_)⟩
  have hm : y ∈ ⊤ ⊓ M.U c := ⟨trivial, hc⟩
  replace hb := (stalkEquiv_germ hM c hc (V := ⊤) trivial _).symm.trans
    ((LinearEquiv.eq_symm_apply _).1 hb)
  have h₁ : stalkLinear S.g y (J.presheaf.germ _ y hm (coord (F := J) a c)) =
      stalkLinear S.g y (J.presheaf.germ U y hU t) :=
    (stalkLinear_germ S.g y hm _).trans hb
  have h₂ : stalkLinear φ y (J.presheaf.germ U y hU t -
      J.presheaf.germ _ y hm (coord (F := J) a c)) = 0 := by
    rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
    exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
  rw [hφ, stalkLinear_comp, LinearMap.comp_apply] at h₂
  have h₃ := not_isUnit_of_toSubscheme_eq_zero Y (y := y) (hY.ge rfl) _ h₂
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, structureModuleStalkEquiv_germ,
    structureModuleStalkEquiv_germ, ht, map_one] at h₃
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
  exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hc _)).mpr hu

end SerreCriterion

open SerreCriterion in

theorem isAmpleLB_of_subsingleton_coh_one (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (L : LB X) (hL : L.IsLB)
    (h : ∀ F : X.Modules, IsFiniteQC F →
      ∃ n : ℕ, 1 ≤ n ∧ Subsingleton (coh (twist F (lbPow L n)) 1)) : IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨y, hxy, hy⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  obtain ⟨W, hW, hyW⟩ := exists_affine_mem y
  let I := Scheme.IdealSheafData.vanishingIdeal W.compl
  have hI : ∀ z, z ∉ I.support ↔ z ∈ W := fun z => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact not_not
  let Y := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨{y}, hy⟩
  have hY : (Y.support : Set X) = {y} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨n, hn, hz⟩ := h (kernel (idealModuleι I ≫ toSubscheme Y)) (.of_mono (kernel.ι _))
  obtain ⟨t, ht⟩ := exists_idealModuleι_app_eq_one I fun z => (hI z).2
  have hM := isLB_lbPow hL n
  obtain ⟨a, ha⟩ := exists_mem_nonzeroLocus hM _ Y hY hz hyW t ht
  have hle : nonzeroLocus (secOfTwist (idealModuleι I) a) ≤ W := iSup_le fun c z hz => (hI z).1 <| by
    rw [secOfTwist_f] at hz
    exact notMem_support_of_mem_basicOpen I _ ((X.basicOpen_res _ (homOfLE _).op).le hz).2
  refine ⟨n, hn, _, (specializes_iff_mem_closure.2 hxy).mem_open (Opens.isOpen _) ha, ?_⟩
  exact inf_eq_left.2 hle ▸ isAffineOpen_nonzeroLocus_inf hM _ hW

end GlobalTheory
