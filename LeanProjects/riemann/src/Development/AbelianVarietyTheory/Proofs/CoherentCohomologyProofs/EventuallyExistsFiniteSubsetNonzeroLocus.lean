import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.QCoh GlobalTheory.Twist
open GlobalTheory.ThickeningDetermines (secIdeal exists_mem_chart associated_germ_sec)

universe v

namespace GlobalTheory

theorem topologicalKrullDim_add_one_le {T : Type*} [TopologicalSpace T] [QuasiSober T]
    {s t : Set T} (hs : IsClosed s) (ht : IsClosed t)
    (h : ∀ x ∈ s, ∃ y ∈ t, y ∉ s ∧ y ⤳ x) :
    topologicalKrullDim s + 1 ≤ topologicalKrullDim t := by
  have hst : s ⊆ t := fun x hx => have ⟨_, hy, _, hyx⟩ := h x hx; hyx.mem_closed ht hy
  have hi : Topology.IsInducing (Set.inclusion hst) := (Topology.IsEmbedding.inclusion hst).isInducing
  have key : ∀ Z : IrreducibleCloseds s, ∃ Z' : IrreducibleCloseds t,
      IrreducibleCloseds.map _ hi.continuous Z < Z' := by
    intro Z
    have := hs.isClosedEmbedding_subtypeVal.quasiSober
    obtain ⟨x, hx⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
    obtain ⟨y, hy, hys, hyx⟩ := h x x.2
    refine ⟨⟨closure {⟨y, hy⟩}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_, fun hle => ?_⟩
    · refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨z, hz, rfl⟩
      exact specializes_iff_mem_closure.1 ((subtype_specializes_iff _ _).2
        (hyx.trans ((subtype_specializes_iff _ _).1 (hx.specializes hz))))
    · have hc : IsClosed (Subtype.val ⁻¹' s : Set t) := hs.preimage continuous_subtype_val
      exact hys (closure_minimal (t := Subtype.val ⁻¹' s) (by rintro _ ⟨z, -, rfl⟩; exact z.2) hc
        (hle (subset_closure rfl)))
  rcases isEmpty_or_nonempty (IrreducibleCloseds s) with _ | hne
  · rw [topologicalKrullDim, Order.krullDim_eq_bot, WithBot.bot_add]
    exact bot_le
  choose g hg using key
  have : Nonempty (IrreducibleCloseds t) := hne.map g
  rw [topologicalKrullDim, topologicalKrullDim, Order.krullDim_eq_iSup_height_of_nonempty,
    Order.krullDim_eq_iSup_height_of_nonempty, ← WithBot.coe_one, ← WithBot.coe_add,
    WithBot.coe_le_coe, ENat.iSup_add]
  refine iSup_le fun Z => le_iSup_of_le (g Z) (le_trans ?_ (Order.height_add_one_le (hg Z)))
  gcongr
  exact Order.height_le_height_apply_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing hi) Z

section IsMulBy

variable {X : Scheme.{0}} {L : LB X} {F G : X.Modules}

def IsMulBy (φ : G ⟶ F) (s : L.Sec) : Prop :=
  ∀ (i : L.ι) (V : X.Opens) (h : V ≤ L.U i), ∃ e : Γ(G, V) ≃ₗ[Γ(X, V)] Γ(F, V),
    ∀ t, φ.app V t = resG X h (s.f i) • e t

theorem isMulBy_secHom (F : X.Modules) (hL : L.IsLB) (s : L.Sec) : IsMulBy (secHom F s) s :=
  fun i _ h => ⟨(chartEquiv hL i h).symm, fun t => (chartEquiv hL i h).injective (by
    rw [chartEquiv_secHom_app, map_smul, LinearEquiv.apply_symm_apply])⟩

namespace IsMulBy

variable {φ : G ⟶ F} {s : L.Sec}

theorem mem_range_app_iff (H : IsMulBy φ s) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (t : Γ(F, V)) :
    t ∈ Set.range (φ.app V) ↔ ∃ u, resG X h (s.f i) • u = t := by
  obtain ⟨e, he⟩ := H i V h
  exact ⟨fun ⟨u, hu⟩ => ⟨e u, (he u).symm.trans hu⟩,
    fun ⟨u, hu⟩ => ⟨e.symm u, by rw [he, e.apply_symm_apply, hu]⟩⟩

theorem mem_range_stalkLinear_iff (H : IsMulBy φ s) (i : L.ι) {x : X} (hx : x ∈ L.U i)
    (t : (F.presheaf.stalk x :)) :
    t ∈ Set.range (stalkLinear φ x) ↔ ∃ u, X.presheaf.germ _ x hx (s.f i) • u = t := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨V, hV, hxV, u, rfl⟩ := exists_germ_eq_of_mem hx u
    obtain ⟨w, hw⟩ := (H.mem_range_app_iff i hV _).1 ⟨u, rfl⟩
    refine ⟨F.presheaf.germ V x hxV w, ?_⟩
    rw [stalkLinear_germ, ← hw, QCoh.germ_smul]
    exact congrArg (· • _) (Cartier.germ_resG hV x hxV _).symm
  · rintro ⟨u, rfl⟩
    obtain ⟨V, hV, hxV, u, rfl⟩ := exists_germ_eq_of_mem hx u
    obtain ⟨w, hw⟩ := (H.mem_range_app_iff i hV _).2 ⟨u, rfl⟩
    refine ⟨G.presheaf.germ V x hxV w, ?_⟩
    rw [stalkLinear_germ, hw, QCoh.germ_smul]
    exact congrArg (· • _) (Cartier.germ_resG hV x hxV _)

theorem injective_app_iff (H : IsMulBy φ s) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) :
    Function.Injective (φ.app V) ↔ IsSMulRegular Γ(F, V) (resG X h (s.f i)) := by
  obtain ⟨e, he⟩ := H i V h
  rw [show ⇑(φ.app V) = (resG X h (s.f i) • ·) ∘ e from funext he]
  exact ⟨fun h' => Function.Injective.of_comp_right h' e.surjective, fun h' => h'.comp e.injective⟩

theorem mono_iff [IsLocallyNoetherian X] [F.IsQuasicoherent] (H : IsMulBy φ s) (hL : L.IsLB) :
    Mono φ ↔ assPoints F ⊆ nonzeroLocus s := by
  have hb : ∀ (i : L.ι) (V : X.Opens) (h : V ≤ L.U i) (x : X), x ∈ V →
      (x ∈ X.basicOpen (resG X h (s.f i)) ↔ x ∈ nonzeroLocus s) := fun i V h x hx => by
    rw [Cartier.mem_nonzeroLocus_iff s i (h hx), X.mem_basicOpen _ x hx,
      X.mem_basicOpen _ x (h hx)]
    exact iff_of_eq (congrArg IsUnit (Cartier.germ_resG h x hx _))
  refine ⟨fun _ x hx => ?_, fun h => mono_of_locally_app_injective φ fun W x hx => ?_⟩
  · obtain ⟨i, hi⟩ := exists_mem_chart hL x
    obtain ⟨V, hV, hxV, hle⟩ := exists_affine_mem_le x hi
    exact (hb i V hle x hxV).1 ((isSMulRegular_sections_iff hV _).1
      ((H.injective_app_iff i hle).1 (injective_app_of_mono φ V)) ⟨hx, hxV⟩)
  · obtain ⟨i, hi⟩ := exists_mem_chart hL x
    obtain ⟨V, hV, hxV, hle⟩ := exists_affine_mem_le (U := W ⊓ L.U i) x ⟨hx, hi⟩
    exact ⟨V, hxV, hle.trans inf_le_left, (H.injective_app_iff i (hle.trans inf_le_right)).2
      ((isSMulRegular_sections_iff hV _).2 fun y hy => (hb i V _ y hy.2).2 (h hy.1))⟩

theorem stalkLinear_π_eq_zero_iff (H : IsMulBy φ s) (i : L.ι) {x : X} (hx : x ∈ L.U i)
    (t : (F.presheaf.stalk x :)) :
    stalkLinear (cokernel.π φ) x t = 0 ↔ ∃ u, X.presheaf.germ _ x hx (s.f i) • u = t :=
  ((exact_iff_stalkLinear _).1 (ShortComplex.exact_cokernel φ) x t).trans
    (H.mem_range_stalkLinear_iff i hx t)

theorem support_cokernel_subset (H : IsMulBy φ s) :
    support (cokernel φ) ⊆ support F \ nonzeroLocus s := fun x hx => by
  refine ⟨support_subset_of_epi (cokernel.π φ) hx, fun hs => notMem_support_iff.2 ?_ hx⟩
  obtain ⟨i, hi⟩ := exists_chart_of_mem_nonzeroLocus hs
  obtain ⟨u, hu⟩ := (X.mem_basicOpen _ x hi).1 ((Cartier.mem_nonzeroLocus_iff s i hi).1 hs)
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨t, rfl⟩ := stalkLinear_surjective (cokernel.π φ) x t
  exact (H.stalkLinear_π_eq_zero_iff i hi t).2 ⟨u⁻¹ • t, by
    rw [← hu, ← Units.smul_def, smul_inv_smul]⟩

theorem support_cokernel [IsFiniteQC F] (H : IsMulBy φ s) (hL : L.IsLB) :
    support (cokernel φ) = support F \ nonzeroLocus s := by
  refine H.support_cokernel_subset.antisymm fun x ⟨hx, hs⟩ => by_contra fun h => ?_
  obtain ⟨i, hi⟩ := exists_mem_chart hL x
  have := notMem_support_iff.1 h
  have h₁ : X.presheaf.germ _ x hi (s.f i) ∈ IsLocalRing.maximalIdeal _ := fun hu =>
    hs ((Cartier.mem_nonzeroLocus_iff s i hi).2 ((X.mem_basicOpen _ x hi).2 hu))
  have h₂ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal _)
    (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) Module.Finite.fg_top
    (fun t _ => by
      obtain ⟨u, rfl⟩ := (H.stalkLinear_π_eq_zero_iff i hi t).1 (Subsingleton.elim _ _)
      exact Submodule.smul_mem_smul h₁ trivial) (IsLocalRing.maximalIdeal_le_jacobson _)
  exact notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t => h₂.le trivial) hx

theorem suppDim_cokernel_add_one_le [IsLocallyNoetherian X] [IsFiniteQC F] (H : IsMulBy φ s)
    (hL : L.IsLB) [Mono φ] : suppDim (cokernel φ) + 1 ≤ suppDim F := by
  unfold suppDim
  rw [H.support_cokernel hL]
  refine topologicalKrullDim_add_one_le ((isClosed_support F).sdiff (nonzeroLocus s).isOpen)
    (isClosed_support F) fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ := exists_mem_assPoints_specializes hx.1
  exact ⟨y, assPoints_subset_support F hy, fun h => h.2 ((H.mono_iff hL).1 inferInstance hy), hyx⟩

end IsMulBy

end IsMulBy

section Ideal

variable {X : Scheme.{0}} {L : LB X} {F G : X.Modules}

theorem ideal_secIdeal (hL : L.IsLB) (s : L.Sec) (W : X.affineOpens) (i : L.ι) (h : W.1 ≤ L.U i) :
    (secIdeal hL s).ideal W = Ideal.span {resG X h (s.f i)} :=
  EffCartierData.ideal_locIdeal _ _ _ _ W i h

theorem map_germ_ideal_secIdeal (hL : L.IsLB) (s : L.Sec) (W : X.affineOpens) {x : X}
    (hx : x ∈ W.1) (i : L.ι) (hi : x ∈ L.U i) :
    ((secIdeal hL s).ideal W).map (X.presheaf.germ W.1 x hx).hom =
      Ideal.span {X.presheaf.germ _ x hi (s.f i)} := by
  obtain ⟨V, hxV, hV⟩ := EffCartierData.exists_affine_le hi
  rw [← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ W x hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V x hxV,
    ideal_secIdeal hL s V i hV, Ideal.map_span, Set.image_singleton, Cartier.germ_resG]

theorem coe_support_secIdeal (hL : L.IsLB) (s : L.Sec) :
    ((secIdeal hL s).support : Set X) = (nonzeroLocus s : Set X)ᶜ := by
  ext x
  obtain ⟨i, hi⟩ := exists_mem_chart hL x
  obtain ⟨V, hxV, hV⟩ := EffCartierData.exists_affine_le hi
  refine (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId _ x).trans ?_
  rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V x hxV, map_germ_ideal_secIdeal hL s V hxV i hi, Ne,
    Ideal.span_singleton_eq_top, ← X.mem_basicOpen _ x hi, ← Cartier.mem_nonzeroLocus_iff s i hi]
  rfl

theorem IsMulBy.ker_π_app [F.IsQuasicoherent] {φ : G ⟶ F} {s : L.Sec} (H : IsMulBy φ s)
    (hL : L.IsLB) (W : X.affineOpens) :
    LinearMap.ker (appLinear (cokernel.π φ) W.1) = (secIdeal hL s).ideal W • ⊤ := by
  have key : ∀ (x : W.1) (t : (F.presheaf.stalk (x : X) :)), stalkLinear (cokernel.π φ) x t = 0 ↔
      t ∈ (secIdeal hL s).ideal W • (⊤ : Submodule Γ(X, W.1) (F.presheaf.stalk (x : X) :)) := by
    intro x t
    obtain ⟨i, hi⟩ := exists_mem_chart hL x
    rw [H.stalkLinear_π_eq_zero_iff i hi, ← Submodule.restrictScalars_top Γ(X, W.1)
      (X.presheaf.stalk (x : X)), ← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem]
    refine Iff.trans ?_ (iff_of_eq (congrArg (fun I : Ideal _ => t ∈ I • (⊤ : Submodule _ _))
      (map_germ_ideal_secIdeal hL s W x.2 i hi).symm))
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp
  refine le_antisymm (fun t ht => ?_) fun t ht => section_eq_zero_of_germ _ fun x hx => ?_
  · by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (((secIdeal hL s).ideal W • ⊤ :
      Submodule Γ(X, W.1) Γ(F, W.1)).comap (LinearMap.toSpanSingleton _ _ t)) fun h =>
        hn (by simpa using (Ideal.eq_top_iff_one _).1 h)
    have := isLocalizedModule_germLinear_pointOfPrime F W.2 P
    suffices germLinear F (pointOfPrime W.2 ⟨P, hP.isPrime⟩) t ∈
        ((secIdeal hL s).ideal W • ⊤ : Submodule Γ(X, W.1) Γ(F, W.1)).localized₀ P.primeCompl
          (germLinear F (pointOfPrime W.2 ⟨P, hP.isPrime⟩)) by
      obtain ⟨m, hm, r, hr⟩ := this
      rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at hr
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) hr
      refine (c * r).2 (hle ?_)
      change (c * r) • t ∈ (secIdeal hL s).ideal W • (⊤ : Submodule Γ(X, W.1) Γ(F, W.1))
      rw [mul_smul, ← hc]
      exact Submodule.smul_mem _ _ hm
    rw [Submodule.localized₀_smul, Submodule.localized₀_top, ← key, germLinear_apply,
      stalkLinear_germ, show (cokernel.π φ).app W.1 t = 0 from ht, map_zero]
  · obtain ⟨x, rfl⟩ : ∃ x' : W.1, x' = x := ⟨⟨x, hx⟩, rfl⟩
    rw [appLinear_apply, ← stalkLinear_germ]
    refine (key x _).2 ?_
    have := Submodule.mem_map_of_mem (f := germLinear F x) ht
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this

theorem surjective_and_ker_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {l : M →ₗ[A] N} (hl : IsBaseChange B l)
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective l ∧ LinearMap.ker l = RingHom.ker (algebraMap A B) • ⊤ := by
  let e : (A ⧸ RingHom.ker (algebraMap A B)) ≃ₗ[A] B :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) h).toLinearEquiv
  have e₁ : l = (hl.equiv.restrictScalars A).toLinearMap ∘ₗ (e.rTensor M).toLinearMap ∘ₗ
      TensorProduct.mk A (A ⧸ RingHom.ker (algebraMap A B)) M 1 := by
    ext m
    have : e 1 = 1 := map_one (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) h)
    simp [this]
  constructor
  · rw [e₁]
    exact hl.equiv.surjective.comp ((e.rTensor M).surjective.comp
      (TensorProduct.mk_surjective A M _ Ideal.Quotient.mk_surjective))
  · rw [e₁, LinearEquiv.ker_comp, LinearEquiv.ker_comp, LinearMap.ker_tensorProductMk]

theorem surjective_and_ker_unit_subschemeι (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (W : X.affineOpens) :
    Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).app W.1) ∧
    LinearMap.ker (appLinear
      ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F) W.1) =
        I.ideal W • ⊤ := by
  have e : I.subschemeι ⁻¹ᵁ W.1 ≤ I.subschemeι ⁻¹ᵁ W.1 := le_rfl
  letI := appLEAlgebra I.subschemeι e
  letI := appLEModule I.subschemeι ((Scheme.Modules.pullback I.subschemeι).obj F) e
  have := appLE_isScalarTower I.subschemeι ((Scheme.Modules.pullback I.subschemeι).obj F) e
  have e₀ : algebraMap Γ(X, W.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W.1) =
      (I.subschemeι.app W.1).hom := congrArg CommRingCat.Hom.hom (I.subschemeι.appLE_eq_app)
  obtain ⟨h₁, h₂⟩ := surjective_and_ker_of_isBaseChange
    (isBaseChange_pullbackSections I.subschemeι F (W.2.preimage I.subschemeι) W.2 e)
    (e₀ ▸ I.subschemeι_app_surjective W)
  have e₁ : ∀ t, pullbackSections I.subschemeι F e t =
      ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).app W.1 t :=
    fun t => resM_self _ _
  refine ⟨fun u => (h₁ u).imp fun t ht => (e₁ t).symm.trans ht, ?_⟩
  rw [← I.ker_subschemeι_app W, ← e₀, ← h₂]
  ext t
  exact iff_of_eq (congrArg (· = 0) (e₁ t).symm)

theorem surjective_and_ker_unitToPush_subschemeι (I : X.IdealSheafData) (W : X.affineOpens) :
    Function.Surjective ((unitToPush I.subschemeι).app W.1) ∧
      LinearMap.ker (appLinear (unitToPush I.subschemeι) W.1) = I.ideal W • ⊤ :=
  ⟨I.subschemeι_app_surjective W,
    (I.ker_subschemeι_app W).trans ((Ideal.mul_top _).symm.trans (Ideal.smul_eq_mul _ _).symm)⟩

theorem IsMulBy.exists_cokernel_iso [F.IsQuasicoherent] [G.IsQuasicoherent] {φ : G ⟶ F} {s : L.Sec}
    (H : IsMulBy φ s) (hL : L.IsLB) {E : X.Modules} [E.IsQuasicoherent] (η : F ⟶ E)
    (h : ∀ W : X.affineOpens, Function.Surjective (η.app W.1) ∧
      LinearMap.ker (appLinear η W.1) = (secIdeal hL s).ideal W • ⊤) :
    ∃ e : cokernel φ ≅ E, cokernel.π φ ≫ e.hom = η := by
  have key : ∀ W : X.Opens, IsAffineOpen W → Function.Exact (φ.app W) (η.app W) := fun W hW t =>
    (SetLike.ext_iff.1 ((h ⟨W, hW⟩).2.trans (H.ker_π_app hL ⟨W, hW⟩).symm) t).trans
      (exact_cokernel_π_app φ hW t)
  have w : φ ≫ η = 0 := (hom_eq_zero_iff_affineCover (fun W : X.affineOpens => W.1)
    (iSup_affineOpens_eq_top X) (fun W => W.2) _).2 fun W t => (key W.1 W.2).apply_apply_eq_zero t
  have hS : (ShortComplex.mk φ η w).Exact := (exact_iff_forall_affine _).2 key
  have : Epi (ShortComplex.mk φ η w).g := (epi_iff_forall_affine η).2 fun W hW => (h ⟨W, hW⟩).1
  exact ⟨(cokernelIsCokernel φ).coconePointUniqueUpToIso hS.gIsCokernel,
    (cokernelIsCokernel φ).comp_coconePointUniqueUpToIso_hom hS.gIsCokernel .one⟩

end Ideal

section Cut

variable {X : Scheme.{0}} {L : LB X} (F : X.Modules) (hL : L.IsLB) (s : L.Sec)

def cutHom : twistZ F L (-1) ⟶ F :=
  mulSecOfEq F (zofSec s) (neg_add_cancel 1) ≫ (twistZZeroIso F hL).inv

def cut : X.Modules := cokernel (cutHom F hL s)

def cutπ : F ⟶ cut F hL s := cokernel.π (cutHom F hL s)

theorem cutHom_app (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (t : Γ(twistZ F L (-1), V)) :
    (cutHom F hL s).app V t = resG X h (s.f i) • zchartEquiv hL (-1) i h t := by
  have e : ∀ u : Γ(F, V), zchartEquiv hL 0 i h ((twistZZeroIso F hL).hom.app V u) = u := fun u => by
    rw [zchartEquiv_apply, zcoord_twistZZeroIso_hom_app, resM_resM, resM_self]
  rw [← e ((cutHom F hL s).app V t), app_app, cutHom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, zchartEquiv_mulSecOfEq_app, zfun_zofSec]

theorem isMulBy_cutHom : IsMulBy (cutHom F hL s) s :=
  fun i _ h => ⟨zchartEquiv hL (-1) i h, cutHom_app F hL s i h⟩

instance epi_cutπ : Epi (cutπ F hL s) := inferInstanceAs (Epi (cokernel.π _))

instance isQuasicoherent_cut [F.IsQuasicoherent] : (cut F hL s).IsQuasicoherent :=
  have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL (-1))
  isQuasicoherent_cokernel _

instance isFiniteQC_cut [IsFiniteQC F] : IsFiniteQC (cut F hL s) :=
  have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL (-1))
  inferInstanceAs (IsFiniteQC (cokernel _))

def cutComplex : ShortComplex X.Modules :=
  .mk (cutHom F hL s) (cutπ F hL s) (cokernel.condition _)

theorem shortExact_cutComplex [h : Mono (cutHom F hL s)] : (cutComplex F hL s).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := h
  epi_g := epi_cutπ F hL s

theorem mono_cutHom_iff [IsLocallyNoetherian X] [F.IsQuasicoherent] :
    Mono (cutHom F hL s) ↔ assPoints F ⊆ nonzeroLocus s := (isMulBy_cutHom F hL s).mono_iff hL

include hL in

theorem mono_secHom_iff [IsLocallyNoetherian X] [F.IsQuasicoherent] :
    Mono (secHom F s) ↔ assPoints F ⊆ nonzeroLocus s := by
  have := isQuasicoherent_twist (F := F) hL
  rw [(isMulBy_secHom F hL s).mono_iff hL, assPoints_twist hL]

theorem support_cut [IsFiniteQC F] : support (cut F hL s) = support F \ nonzeroLocus s :=
  (isMulBy_cutHom F hL s).support_cokernel hL

theorem support_cut_eq_inter [IsFiniteQC F] :
    support (cut F hL s) = support F ∩ (secIdeal hL s).support := by
  rw [support_cut, coe_support_secIdeal, Set.diff_eq]

theorem surjective_cutπ_app [F.IsQuasicoherent] (W : X.affineOpens) :
    Function.Surjective ((cutπ F hL s).app W.1) := surjective_app_of_epi _ W.2

theorem ker_cutπ_app [F.IsQuasicoherent] (W : X.affineOpens) :
    LinearMap.ker (appLinear (cutπ F hL s) W.1) = (secIdeal hL s).ideal W • ⊤ :=
  (isMulBy_cutHom F hL s).ker_π_app hL W

theorem exists_cut_iso_pushforward_pullback [F.IsQuasicoherent] :
    ∃ e : cut F hL s ≅ (Scheme.Modules.pushforward (secIdeal hL s).subschemeι).obj
        ((Scheme.Modules.pullback (secIdeal hL s).subschemeι).obj F),
      cutπ F hL s ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction (secIdeal hL s).subschemeι).unit.app F :=
  have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL (-1))
  (isMulBy_cutHom F hL s).exists_cokernel_iso hL
    (E := (Scheme.Modules.pushforward _).obj ((Scheme.Modules.pullback _).obj F)) _
    (surjective_and_ker_unit_subschemeι _ F)

theorem exists_cut_structureModule_iso :
    ∃ e : cut (structureModule X) hL s ≅ (Scheme.Modules.pushforward
        (secIdeal hL s).subschemeι).obj (structureModule (secIdeal hL s).subscheme),
      cutπ _ hL s ≫ e.hom = unitToPush (secIdeal hL s).subschemeι :=
  have := isQuasicoherent_twist (F := structureModule X) (isLB_lbZPow hL (-1))
  (isMulBy_cutHom _ hL s).exists_cokernel_iso hL _ (surjective_and_ker_unitToPush_subschemeι _)

section Dim

variable [IsLocallyNoetherian X] [IsFiniteQC F] [Mono (cutHom F hL s)]

theorem suppDim_cut_add_one_le : suppDim (cut F hL s) + 1 ≤ suppDim F :=
  (isMulBy_cutHom F hL s).suppDim_cokernel_add_one_le hL

theorem suppDim_cut_le {d : ℕ} (h : suppDim F ≤ (d + 1 : ℕ)) : suppDim (cut F hL s) ≤ d :=
  ENat.WithBot.add_le_add_one_right_iff.1
    ((suppDim_cut_add_one_le F hL s).trans (h.trans_eq (Nat.cast_succ d)))

theorem isZero_cut (h : suppDim F ≤ 0) : IsZero (cut F hL s) := by
  rw [← suppDim_lt_zero_iff]
  by_contra! h'
  exact absurd ((add_le_add_left h' 1).trans ((suppDim_cut_add_one_le F hL s).trans h)) (by simp)

end Dim

section Inter

variable {k : Type v} [Field k] [Algebra k Γ(X, ⊤)] [Mono (cutHom F hL s)] {F}
  {d : ℕ} {P : Fin d → LB X}

theorem FiniteCohTwists.cut (h : FiniteCohTwists k F) : FiniteCohTwists k (cut F hL s) :=
  FiniteCohTwists.of_shortExact₃ (shortExact_cutComplex F hL s) (h.twist (isLB_lbZPow hL (-1))) h

theorem interNum_cons_eq_interNum_cut (hP : ∀ i, (P i).IsLB) (h : FiniteCohTwists k F) :
    interNum k F (Fin.cons L P : Fin (d + 1) → LB X) = interNum k (cut F hL s) P :=
  (interNum_cons k F hL hP).trans
    (interNum_cokernel _ hP (h.twist (isLB_lbZPow hL (-1))) h).symm

omit [Mono (cutHom F hL s)] in

theorem interNum_cons_eq_interNumSub [Mono (cutHom (structureModule X) hL s)]
    (hP : ∀ i, (P i).IsLB) (h : FiniteCohTwists k (structureModule X)) :
    interNum k (structureModule X) (Fin.cons L P : Fin (d + 1) → LB X) =
      interNumSub k (secIdeal hL s) P := by
  obtain ⟨e, -⟩ := exists_cut_structureModule_iso hL s
  rw [interNum_cons_eq_interNum_cut hL s hP h, interNum_congr k e]
  rfl

end Inter

end Cut

section Exists

variable {X : Scheme.{0}} {L : LB X} {k : Type v} [Field k] [Infinite k] [Algebra k Γ(X, ⊤)]

theorem exists_finite_subset_nonzeroLocus {W : Type*} [AddCommGroup W] [Module k W]
    (φ : W →ₛₗ[algebraMap k Γ(X, ⊤)] L.Sec) {S : Set X} (hS : S.Finite)
    (h : ∀ x ∈ S, ∃ w, x ∈ nonzeroLocus (φ w)) : ∃ w, S ⊆ nonzeroLocus (φ w) := by
  have := hS.to_subtype
  let p : S → Submodule k W := fun x =>
    { carrier := {w | x.1 ∉ nonzeroLocus (φ w)}
      add_mem' := fun {a b} ha hb hx => by
        rw [map_add] at hx
        exact (nonzeroLocus_add_le _ _ hx).elim ha hb
      zero_mem' := fun hx => by
        rw [map_zero] at hx
        exact nonzeroLocus_secZero.le hx
      smul_mem' := fun c a ha hx => by
        rw [φ.map_smulₛₗ] at hx
        exact ha ((nonzeroLocus_secScale _ _).le hx).2 }
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p fun x hx =>
    have ⟨w, hw⟩ := h x x.2
    (hx.ge (Submodule.mem_top (x := w)) :) hw
  exact ⟨w, fun x hx => not_not.1 (hw ⟨x, hx⟩)⟩

theorem exists_mem_finite_subset_nonzeroLocus [Module k L.Sec] [IsScalarTower k Γ(X, ⊤) L.Sec]
    (W : Submodule k L.Sec) {S : Set X} (hS : S.Finite)
    (h : ∀ x ∈ S, ∃ s ∈ W, x ∈ nonzeroLocus s) : ∃ s ∈ W, S ⊆ nonzeroLocus s :=
  have ⟨w, hw⟩ := exists_finite_subset_nonzeroLocus (k := k) (W := W)
    ⟨⟨Subtype.val, fun _ _ => rfl⟩, fun c w => (algebraMap_smul Γ(X, ⊤) c w.1).symm⟩ hS
    fun x hx => have ⟨s, hs, hx⟩ := h x hx; ⟨⟨s, hs⟩, hx⟩
  ⟨w, w.2, hw⟩

theorem exists_sum_finite_subset_nonzeroLocus {ι : Type*} [Fintype ι] (s : ι → L.Sec) {S : Set X}
    (hS : S.Finite) (h : ∀ x ∈ S, ∃ i, x ∈ nonzeroLocus (s i)) :
    ∃ c : ι → k, S ⊆ nonzeroLocus (∑ i, algebraMap k Γ(X, ⊤) (c i) • s i) := by
  classical
  refine exists_finite_subset_nonzeroLocus (k := k) (W := ι → k)
    ⟨⟨fun c => ∑ i, algebraMap k Γ(X, ⊤) (c i) • s i, fun a b => ?_⟩, fun c a => ?_⟩ hS
    fun x hx => ?_
  · simp [add_smul, Finset.sum_add_distrib]
  · simp [mul_smul, Finset.smul_sum]
  · obtain ⟨i, hi⟩ := h x hx
    refine ⟨Pi.single i 1, ?_⟩
    change x ∈ nonzeroLocus (∑ j, _)
    rwa [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
      one_smul]

variable [AlgebraicGeometry.IsNoetherian X] (F : X.Modules) [IsFiniteQC F]

theorem exists_mem_mono_cutHom (hL : L.IsLB) [Module k L.Sec] [IsScalarTower k Γ(X, ⊤) L.Sec]
    (W : Submodule k L.Sec) (h : ∀ x : X, ∃ s ∈ W, x ∈ nonzeroLocus s) :
    ∃ s ∈ W, Mono (cutHom F hL s) :=
  have ⟨s, hs, h'⟩ := exists_mem_finite_subset_nonzeroLocus W (finite_assPoints F) fun x _ => h x
  ⟨s, hs, (mono_cutHom_iff F hL s).2 h'⟩

theorem exists_sum_mono_cutHom (hL : L.IsLB) {ι : Type*} [Fintype ι] (s : ι → L.Sec)
    (h : ⨆ i, nonzeroLocus (s i) = ⊤) :
    ∃ c : ι → k, Mono (cutHom F hL (∑ i, algebraMap k Γ(X, ⊤) (c i) • s i)) :=
  have ⟨c, hc⟩ := exists_sum_finite_subset_nonzeroLocus (k := k) s (finite_assPoints F)
    fun x _ => Opens.mem_iSup.1 (h.ge (Set.mem_univ x))
  ⟨c, (mono_cutHom_iff F hL _).2 hc⟩

variable (k) in
include k in

theorem IsGenerated.exists_mono_cutHom (h : IsGenerated L) : ∃ s, Mono (cutHom F h.isLB s) :=
  have ⟨_, s, hs⟩ := h
  have ⟨_, hc⟩ := exists_sum_mono_cutHom (k := k) F h.isLB s hs
  ⟨_, hc⟩

omit [AlgebraicGeometry.IsNoetherian X] in

theorem IsAmpleLB.exists_mono_cutHom [IsLocallyNoetherian X] (h : IsAmpleLB L) :
    ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, Mono (cutHom F (isLB_lbPow h.isLB n) s) ∧
      IsAffineOpen (nonzeroLocus s) :=
  have := h.compactSpace
  have ⟨n, hn, s, h₁, _, h₂⟩ := h.exists_affine_finite_subset (finite_assPoints F)
    (U := ⊤) (Set.subset_univ _)
  ⟨n, hn, s, (mono_cutHom_iff F _ s).2 h₁, h₂⟩

end Exists

section Twists

open CechPic

variable {X : Scheme.{0}} {L M : LB X} [IsLocallyNoetherian X]

theorem IsAmpleLB.eventually_exists_mem_nonzeroLocus_le (h : IsAmpleLB L) (hM : M.IsLB) {x : X}
    {U : X.Opens} (hx : x ∈ U) : ∀ᶠ n : ℤ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      cls N hN = cls M hM + n • cls L h.isLB → ∃ t : N.Sec, x ∈ nonzeroLocus t ∧ nonzeroLocus t ≤ U := by
  let I := Scheme.IdealSheafData.vanishingIdeal U.compl
  have hI : ∀ y, y ∉ I.support ↔ y ∈ U := fun y => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact not_not
  have := isFiniteQC_twist (F := idealModule I) hM
  refine (h.eventually_isGloballyGenerated_twistZ (twist (idealModule I) M)).mono
    fun n hg N hN e => ?_
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (idealModule I) hM (isLB_lbZPow h.isLB n) hN
    (by rw [e, cls_lbZPow h.isLB])
  obtain ⟨m, a, ha⟩ := isGloballyGenerated_iff_spanStalks.1 (hg.of_epi e.hom)
  obtain ⟨t, ht⟩ := exists_idealModuleι_app_eq_one I fun y => (hI y).2
  obtain ⟨i, hi⟩ := exists_mem_nonzeroLocus_secOfTwist hN _ ha hx t ht
  refine ⟨_, hi, iSup_le fun c y hy => (hI y).1 ?_⟩
  rw [secOfTwist_f] at hy
  exact notMem_support_of_mem_basicOpen I _ ((X.basicOpen_res _ (homOfLE _).op).le hy).2

theorem IsAmpleLB.eventually_exists_finite_subset_nonzeroLocus (h : IsAmpleLB L) (hM : M.IsLB)
    {S : Set X} (hS : S.Finite) : ∀ᶠ n : ℤ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      cls N hN = cls M hM + n • cls L h.isLB → ∃ t : N.Sec, S ⊆ nonzeroLocus t := by
  classical
  lift S to Finset X using hS
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact .of_forall fun _ _ _ _ => ⟨0, by simp⟩
    letI := specializationPreorder X
    obtain ⟨x, hx, hmax⟩ := S.exists_maximal hne
    have hcl : IsClosed (⋃ y ∈ S.erase x, closure ({y} : Set X)) :=
      isClosed_biUnion_finset fun _ _ => isClosed_closure
    refine ((ih (S.erase x) (Finset.erase_ssubset hx)).and (h.eventually_exists_mem_nonzeroLocus_le
      hM (x := x) (U := ⟨_, hcl.isOpen_compl⟩) fun h => ?_)).mono fun n ⟨h₁, h₂⟩ N hN e => ?_
    · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 h
      have h₁ : y ⤳ x := specializes_iff_mem_closure.2 hxy
      have h₂ : x ⤳ y := hmax (Finset.mem_of_mem_erase hy) h₁
      exact Finset.ne_of_mem_erase hy (h₁.antisymm h₂).eq
    obtain ⟨s, hs⟩ := h₁ N hN e
    obtain ⟨t, hxt, ht⟩ := h₂ N hN e
    by_cases hxs : x ∈ nonzeroLocus s
    · refine ⟨s, fun y hy => ?_⟩
      rcases eq_or_ne y x with rfl | hyx
      exacts [hxs, hs (Finset.mem_erase.2 ⟨hyx, hy⟩)]
    refine ⟨s + t, fun y hy => ?_⟩
    rcases eq_or_ne y x with rfl | hyx
    · exact ((add_comm t s ▸ nonzeroLocus_le_add_sup t s) hxt).resolve_right hxs
    · have hy' : y ∈ S.erase x := Finset.mem_erase.2 ⟨hyx, hy⟩
      exact (nonzeroLocus_le_add_sup s t (hs hy')).resolve_right fun h =>
        ht h (Set.mem_iUnion₂.2 ⟨y, hy', subset_closure rfl⟩)

theorem IsAmpleLB.eventually_exists_mono_cutHom (h : IsAmpleLB L) (hM : M.IsLB) (F : X.Modules)
    [IsFiniteQC F] : ∀ᶠ n : ℤ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      cls N hN = cls M hM + n • cls L h.isLB → ∃ t : N.Sec, Mono (cutHom F hN t) :=
  have := h.compactSpace
  (h.eventually_exists_finite_subset_nonzeroLocus hM (finite_assPoints F)).mono fun _ hn N hN e =>
    (hn N hN e).imp fun t ht => (mono_cutHom_iff F hN t).2 ht

theorem IsAmpleLB.eventually_exists_mono_cutHom_pow (h : IsAmpleLB L) (F : X.Modules)
    [IsFiniteQC F] :
    ∀ᶠ n : ℕ in atTop, ∃ t : (lbPow L n).Sec, Mono (cutHom F (isLB_lbPow h.isLB n) t) :=
  (tendsto_natCast_atTop_atTop.eventually
    (h.eventually_exists_mono_cutHom (LB.isLB_triv X) F)).mono fun n hn =>
      hn _ _ (by rw [cls_triv, zero_add]; exact cls_lbZPow h.isLB n _)

theorem IsAmpleLB.exists_sub_of_mono_cutHom (h : IsAmpleLB L) (F : X.Modules) [IsFiniteQC F]
    (c : Pic X) : ∃ (A B : LB X) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec),
      Mono (cutHom F hA s) ∧ Mono (cutHom F hB t) ∧ c = cls A hA - cls B hB := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨n, h₁, h₂⟩ := ((h.eventually_exists_mono_cutHom hM F).and
    (h.eventually_exists_mono_cutHom (LB.isLB_triv X) F)).exists
  obtain ⟨A, hA, eA⟩ := cls_surj (cls M hM + n • cls L h.isLB)
  obtain ⟨B, hB, eB⟩ := cls_surj (cls _ (LB.isLB_triv X) + n • cls L h.isLB)
  obtain ⟨s, hs⟩ := h₁ A hA eA
  obtain ⟨t, ht⟩ := h₂ B hB eB
  exact ⟨A, B, hA, hB, s, t, hs, ht, by rw [eA, eB, cls_triv, zero_add, add_sub_cancel_right]⟩

end Twists

theorem cut_by_regular_section {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (F : X.Modules)
    [IsFiniteQC F] {L : LB X} (hL : L.IsLB) :
    (∀ s : L.Sec,
      (∀ (i : L.ι) (V : X.Opens) (h : V ≤ L.U i) (t : Γ(twistZ F L (-1), V)),
        (cutHom F hL s).app V t = resG X h (s.f i) • zchartEquiv hL (-1) i h t) ∧
      (Mono (cutHom F hL s) ↔ ∀ x ∈ assPoints F, x ∈ nonzeroLocus s) ∧
      IsFiniteQC (cokernel (cutHom F hL s)) ∧
      support (cokernel (cutHom F hL s)) = support F \ nonzeroLocus s ∧
      ((secIdeal hL s).support : Set X) = (nonzeroLocus s : Set X)ᶜ ∧
      (∀ (W : X.affineOpens) (i : L.ι) (h : W.1 ≤ L.U i),
        (secIdeal hL s).ideal W = Ideal.span {resG X h (s.f i)}) ∧
      (∀ W : X.affineOpens, Function.Surjective ((cokernel.π (cutHom F hL s)).app W.1) ∧
        LinearMap.ker (appLinear (cokernel.π (cutHom F hL s)) W.1) =
          (secIdeal hL s).ideal W • ⊤) ∧
      Nonempty (cokernel (cutHom F hL s) ≅
        (Scheme.Modules.pushforward (secIdeal hL s).subschemeι).obj
          ((Scheme.Modules.pullback (secIdeal hL s).subschemeι).obj F)) ∧
      (Mono (cutHom F hL s) →
        (∀ (k : Type v) [Field k] [Algebra k Γ(X, ⊤)], FiniteCohTwists k F →
          FiniteCohTwists k (cokernel (cutHom F hL s)) ∧
          ∀ (d : ℕ) (P : Fin d → LB X), (∀ i, (P i).IsLB) →
            interNum k F (Fin.cons L P : Fin (d + 1) → LB X) =
              interNum k (cokernel (cutHom F hL s)) P) ∧
        suppDim (cokernel (cutHom F hL s)) + 1 ≤ suppDim F ∧
        (∀ d : ℕ, suppDim F ≤ (d + 1 : ℕ) → suppDim (cokernel (cutHom F hL s)) ≤ d) ∧
        (suppDim F ≤ 0 → IsZero (cokernel (cutHom F hL s))))) ∧
    (∀ (k : Type v) [Field k] [Infinite k] [Algebra k Γ(X, ⊤)] [Module k L.Sec]
      [IsScalarTower k Γ(X, ⊤) L.Sec] (W : Submodule k L.Sec),
        (∀ x : X, ∃ s ∈ W, x ∈ nonzeroLocus s) → ∃ s ∈ W, Mono (cutHom F hL s)) ∧
    (IsAmpleLB L →
      (∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, Mono (cutHom F (isLB_lbPow hL n) s)) ∧
      ∀ᶠ n : ℕ in atTop, ∃ s : (lbPow L n).Sec, Mono (cutHom F (isLB_lbPow hL n) s)) :=
  ⟨fun s => ⟨fun i _ h => cutHom_app F hL s i h, mono_cutHom_iff F hL s, isFiniteQC_cut F hL s,
      support_cut F hL s, coe_support_secIdeal hL s, ideal_secIdeal hL s,
      fun W => ⟨surjective_cutπ_app F hL s W, ker_cutπ_app F hL s W⟩,
      (exists_cut_iso_pushforward_pullback F hL s).elim fun e _ => ⟨e⟩,
      fun _ => ⟨fun _ _ _ h => ⟨h.cut hL s, fun _ _ hP => interNum_cons_eq_interNum_cut hL s hP h⟩,
        suppDim_cut_add_one_le F hL s, fun _ => suppDim_cut_le F hL s, isZero_cut F hL s⟩⟩,
    fun _ _ _ _ _ _ => exists_mem_mono_cutHom F hL,
    fun h => ⟨have ⟨n, hn, s, hs, _⟩ := h.exists_mono_cutHom F; ⟨n, hn, s, hs⟩,
      h.eventually_exists_mono_cutHom_pow F⟩⟩

theorem mono_cutHom_structureModule_iff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {L : LB X} (hL : L.IsLB) (s : L.Sec) :
    Mono (cutHom (structureModule X) hL s) ↔ genericPoint X ∈ nonzeroLocus s := by
  rw [mono_cutHom_iff]
  refine ⟨fun h => h (mem_assPoints_of_forall_specializes (support_structureModule.ge trivial)
    fun y _ hy => (hy.antisymm (genericPoint_specializes y)).eq), fun h x hx => ?_⟩
  obtain ⟨i, hi⟩ := exists_mem_chart hL x
  have hg : genericPoint X ∈ L.U i := (genericPoint_specializes x).mem_open (L.U i).isOpen hi
  have h₀ : s.f i ≠ 0 := fun e => by
    have := (Cartier.mem_nonzeroLocus_iff s i hg).1 h
    rw [e, Scheme.basicOpen_zero] at this
    exact this
  refine basicOpen_le_nonzeroLocus s i ((isSMulRegular_stalk_iff (s.f i)).1
    (fun y hy => ?_) ⟨hx, hi⟩)
  have := Cartier.isRegularFn_iff_germ.1 (Cartier.isRegularFn_of_ne_zero h₀) y hy
  exact ((structureModuleStalkEquiv y).isSMulRegular_congr _).2
    (isSMulRegular_iff_right_eq_zero_of_smul.2 fun b hb => this.1 b hb)

end GlobalTheory
