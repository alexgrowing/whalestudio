import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Twist

namespace GlobalTheory.ProperFinite

variable {X X' : Scheme.{0}}

theorem notMem_support_of_subsingleton (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    [Subsingleton Γ(F, V)] {x : X} (hx : x ∈ V) : x ∉ support F := fun h => by
  have h' := (mem_support_iff_primeIdealOf (F := F) hV ⟨x, hx⟩).1 h
  rw [Module.support_eq_empty] at h'
  exact h'

theorem nonempty_coh_pushforward_equiv (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)]
    (π : X' ⟶ X) (hπ : ∀ r, π.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) r)
    (E : X'.Modules) [((Scheme.Modules.pushforward π).obj E).IsQuasicoherent] {m : ℕ} {U : Fin m → X.Opens}
    (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i))
    (hE : ∀ s : Finset (Fin m), s.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn E (π ⁻¹ᵁ (⨅ i ∈ s, U i)) q))
    (p : ℕ) : Nonempty (coh ((Scheme.Modules.pushforward π).obj E) p ≃ₗ[R] coh E p) := by
  have hc' : π ⁻¹ᵁ ⊤ ≤ ⨆ i, π ⁻¹ᵁ U i := by rw [← Scheme.Hom.preimage_iSup, hc]
  have ha : CechAcyclicMod (π ⁻¹ᵁ ⊤) (fun i => π ⁻¹ᵁ U i) E :=
    (cechAcyclicMod_iff_of_le fun _ => le_top).2 fun s hs q hq => by
      have := hE s hs q hq
      have e : π ⁻¹ᵁ (⊤ ⊓ ⨅ i ∈ s, U i) = ⊤ ⊓ ⨅ i ∈ s, π ⁻¹ᵁ U i := preimage_cechOpen π ⊤ U s
      rwa [← top_inf_eq (⨅ i ∈ s, U i), e, top_inf_eq] at this
  exact ⟨(cechHEquivCoh R hc hU _ p).symm ≪≫ₗ
    ((HomologicalComplex.homologyFunctor _ _ p).mapIso (cechPushforwardIso ⊤ U E hπ)).toLinearEquiv ≪≫ₗ
    cechHEquivCohOn R hc' ha p⟩

theorem eventually_subsingleton_cohOn [IsLocallyNoetherian X] (π : X' ⟶ X) [IsProper π] {L : LB X'}
    (hL : IsAmpleLB L) (E : X'.Modules) [IsFiniteQC E] {V : X.Opens} (hV : IsAffineOpen V) :
    ∀ᶠ n : ℕ in atTop, ∀ q, 0 < q → Subsingleton (cohOn (twist E (lbPow L n)) (π ⁻¹ᵁ V) q) := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have := hL.noetherianSpace
  let j := (π ⁻¹ᵁ V).ι
  let g : (π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(X, V) := π ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g := inferInstanceAs (IsProper (π ∣_ V ≫ hV.isoSpec.hom))
  letI := algebraΓOfHom g
  have hj : IsAmpleLB (L.pull j) := hL.pull_of_isImmersion j
  refine (hj.eventually_subsingleton_coh_twist (f := g) (fun _ => rfl) (E.restrict j)).mono fun n hn q hq => ?_
  have := hn q hq
  obtain ⟨e⟩ := nonempty_iso_of_lbIso (F := E.restrict j) (LB.isLB_pull (isLB_lbPow hL.isLB n) j)
    (isLB_lbPow hj.isLB n) (lbIso_lbPow_pull hL.isLB j n).symm
  let e' : (twist E (lbPow L n)).restrict j ≅ twist (E.restrict j) (lbPow (L.pull j) n) :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫ Twist.pullbackIso E j (isLB_lbPow hL.isLB n) ≪≫
      (twistFunctor _).mapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm ≪≫ e
  exact ((cohOn.restrictEquiv ℤ (g := j) (fun r => by simp) _ (π ⁻¹ᵁ V).ι_image_top q).trans
    (cohOn.mapIso ℤ ⊤ q e')).injective.subsingleton

theorem topIso_inv_appTop (π : X' ⟶ X) (V : X.Opens) :
    V.topIso.inv ≫ (π ∣_ V).appTop = π.appLE V ((π ⁻¹ᵁ V).ι ''ᵁ ⊤) (π ⁻¹ᵁ V).ι_image_top.le := by
  rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Hom.app_eq_appLE]
  exact (congrArg (_ ≫ ·) (π.appLE_map _ _)).trans (π.map_appLE _ _)

theorem isFiniteQC_pushforward [IsLocallyNoetherian X] (π : X' ⟶ X) [IsProper π] {L : LB X'}
    (hL : IsAmpleLB L) (E : X'.Modules) [IsFiniteQC E] : IsFiniteQC ((Scheme.Modules.pushforward π).obj E) := by
  refine ⟨inferInstance, fun V hV => ?_⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have := hL.noetherianSpace
  let j := (π ⁻¹ᵁ V).ι
  let g : (π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(X, V) := π ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g := inferInstanceAs (IsProper (π ∣_ V ≫ hV.isoSpec.hom))
  letI := algebraΓOfHom g
  have hj : IsAmpleLB (L.pull j) := hL.pull_of_isImmersion j
  have hfin := hj.finite_coh (f := g) (fun _ => rfl) (E.restrict j) 0
  have hfin' := Module.Finite.equiv (cohOn.zeroEquiv Γ(X, V) (E.restrict j) ⊤)
  have hle : j ''ᵁ ⊤ ≤ π ⁻¹ᵁ V := (π ⁻¹ᵁ V).ι_image_top.le
  have ha : ∀ r, algebraMap Γ(X, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) r = π.appLE V (j ''ᵁ ⊤) hle r := fun r => by
    change (π ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(X, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, topIso_inv_appTop]
    rfl
  let ρ : Γ((Scheme.Modules.pushforward π).obj E, V) →ₗ[Γ(X, V)] sectionsOn (E.restrict j) ⊤ :=
    { toFun := fun s => (sectionsOn.toΓ (E.restrict j) ⊤).symm (E.presheaf.map (homOfLE hle).op s)
      map_add' := fun s t => (congrArg _ (map_add (E.presheaf.map (homOfLE hle).op).hom s t)).trans (map_add _ _ _)
      map_smul' := fun r s => (sectionsOn.toΓ (E.restrict j) ⊤).injective (by
        rw [sectionsOn.toΓ_smul, RingHom.id_apply, ha]
        change E.presheaf.map (homOfLE hle).op (π.app V r • (show Γ(E, π ⁻¹ᵁ V) from s)) =
          (j.appIso ⊤).inv (restrictGlobal _ ⊤ (π.appLE V (j ''ᵁ ⊤) hle r)) • E.presheaf.map (homOfLE hle).op s
        rw [Scheme.Modules.map_smul, Scheme.Opens.ι_appIso]
        exact congrArg (· • _) (res_self_ring (X := (π ⁻¹ᵁ V).toScheme) le_top _).symm) }
  have hρ : Function.Bijective ρ :=
    (sectionsOn.toΓ (E.restrict j) ⊤).symm.bijective.comp (res_bijective_of_eq E hle (π ⁻¹ᵁ V).ι_image_top)
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ).symm

theorem bijective_unit_app (π : X' ⟶ X) {U V : X.Opens} [IsIso (π ∣_ U)] (h : V ≤ U) (hV : IsAffineOpen V)
    (G : X.Modules) [G.IsQuasicoherent] :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app G).app V) := by
  have hi : IsIso (π ∣_ V) := by
    have h₁ : IsIso (π ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
    have h₂ := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict π U (U.ι ⁻¹ᵁ V))).1 h₁
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h] at h₂
  have hV' : IsAffineOpen (π ⁻¹ᵁ V) := by
    have : IsAffine V := hV
    exact IsAffine.of_isIso (π ∣_ V)
  have hb : Function.Bijective (π.appLE V (π ⁻¹ᵁ V) le_rfl) := by
    have h₀ : IsIso (π ∣_ V).appTop := inferInstanceAs (IsIso ((π ∣_ V).app ⊤))
    have h₁ : IsIso (V.topIso.inv ≫ (π ∣_ V).appTop) := inferInstance
    rw [topIso_inv_appTop, ← π.appLE_map le_rfl (eqToHom (π ⁻¹ᵁ V).ι_image_top).op] at h₁
    have := @IsIso.of_isIso_comp_right _ _ _ _ _ (π.appLE V (π ⁻¹ᵁ V) le_rfl)
      (X'.presheaf.map (eqToHom (π ⁻¹ᵁ V).ι_image_top).op) inferInstance h₁
    exact ConcreteCategory.bijective_of_isIso _
  letI := appLEAlgebra π (le_refl (π ⁻¹ᵁ V))
  letI := appLEModule π ((Scheme.Modules.pullback π).obj G) (le_refl (π ⁻¹ᵁ V))
  haveI := appLE_isScalarTower π ((Scheme.Modules.pullback π).obj G) (le_refl (π ⁻¹ᵁ V))
  have hB := isBaseChange_pullbackSections π G hV' hV le_rfl
  have h₁ : Function.Bijective (pullbackSections π G (le_refl (π ⁻¹ᵁ V))) := by
    let e := (TensorProduct.lid Γ(X, V) Γ(G, V)).symm ≪≫ₗ
      (LinearEquiv.ofBijective (Algebra.linearMap Γ(X, V) Γ(X', π ⁻¹ᵁ V)) hb).rTensor Γ(G, V)
    have he : ⇑(pullbackSections π G (le_refl (π ⁻¹ᵁ V))) = hB.equiv ∘ e := funext fun m => by
      change _ = hB.equiv (algebraMap Γ(X, V) Γ(X', π ⁻¹ᵁ V) 1 ⊗ₜ m)
      rw [map_one, hB.equiv_tmul, one_smul]
    rw [he]
    exact hB.equiv.bijective.comp e.bijective
  exact (Function.Bijective.of_comp_iff' (res_bijective_of_eq ((Scheme.Modules.pullback π).obj G)
    (le_refl (π ⁻¹ᵁ V)) rfl) _).1 h₁

def VanishesSomewhere (E : X.Modules) : Prop :=
  ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ V ≤ W, IsAffineOpen V → Subsingleton Γ(E, V)

theorem finite_coh_of_bijective [IsLocallyNoetherian X] (R : Type) [CommRing R] [IsNoetherianRing R]
    [Algebra R Γ(X, ⊤)]
    (ih : ∀ E : X.Modules, IsFiniteQC E → VanishesSomewhere E → ∀ p, Module.Finite R (coh E p))
    {F G : X.Modules} [IsFiniteQC F] [IsFiniteQC G] (φ : F ⟶ G) {W : X.Opens} (hW : (W : Set X).Nonempty)
    (hφ : ∀ V ≤ W, IsAffineOpen V → Function.Bijective (φ.app V)) (hG : ∀ p, Module.Finite R (coh G p)) :
    ∀ p, Module.Finite R (coh F p) := by
  let ψ : F ⟶ kernel (cokernel.π φ) := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι _ = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have h₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have h₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have hC := ih (cokernel φ) inferInstance ⟨W, hW, fun V hV ha => by
    refine subsingleton_of_forall_eq 0 fun c => ?_
    obtain ⟨g, rfl⟩ := app_surjective_of_epi_of_isAffineOpen (cokernel.π φ) ha c
    obtain ⟨f, rfl⟩ := (hφ V hV ha).2 g
    change (φ ≫ cokernel.π φ).app V f = 0
    rw [cokernel.condition]
    rfl⟩
  have hK := ih (kernel ψ) inferInstance ⟨W, hW, fun V hV ha => by
    refine subsingleton_of_forall_eq 0 fun c => injective_kernel_ι_app ψ V ((hφ V hV ha).1 ?_)
    change (kernel.ι ψ ≫ φ).app V c = (kernel.ι ψ ≫ φ).app V 0
    rw [show kernel.ι ψ ≫ φ = 0 from (congrArg (_ ≫ ·) hψ.symm).trans (by rw [kernel.condition_assoc, zero_comp])]
    rfl⟩
  exact cohOn.forall_finite₂ R h₁ ⊤ hK (cohOn.forall_finite₁ R h₂ ⊤ hG hC)

theorem finite_coh_of_modification {R : Type} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Sp R) [IsProper f]
    (π : X' ⟶ X) (hP : IsProjOver (π ≫ f)) {U : X.Opens} (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)]
    (ih : letI := algebraΓOfHom f
      ∀ E : X.Modules, IsFiniteQC E → VanishesSomewhere E → ∀ p, Module.Finite R (coh E p))
    (G : X.Modules) [IsFiniteQC G] : letI := algebraΓOfHom f; ∀ p, Module.Finite R (coh G p) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom (π ≫ f)
  obtain ⟨_, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hP
  have : IsProper π := .of_comp π f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  let E := (Scheme.Modules.pullback π).obj G
  obtain ⟨u, hu⟩ := hU
  let σ : U.toScheme ⟶ X' := inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  obtain ⟨d, hd, s, hs, -⟩ := hL.exists_affine (σ ⟨u, hu⟩)
  have H : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist E (lbPow L n)) (π ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI => eventually_subsingleton_cohOn π hL E (hD' I hI)
  obtain ⟨n, hn⟩ := eventually_atTop.1 H
  have hN := isLB_lbPow hL.isLB (d * (n + 1))
  let t : (lbPow L (d * (n + 1))).Sec := secPow s (n + 1)
  have ht : Out.nonzeroLocus t = Out.nonzeroLocus s := nonzeroLocus_secPow s n.succ_pos
  have := isFiniteQC_twist (F := E) hN
  have := isFiniteQC_pushforward π hL (twist E (lbPow L (d * (n + 1))))
  refine finite_coh_of_bijective R ih ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app G ≫
    (Scheme.Modules.pushforward π).map (secHom E t)) (W := U.ι ''ᵁ (σ ⁻¹ᵁ Out.nonzeroLocus s))
    ⟨u, ⟨u, hu⟩, hs, rfl⟩ (fun V hV ha => ?_) fun p => ?_
  · have h₁ : V ≤ U := hV.trans (U.ι_image_le _)
    have h₂ : π ⁻¹ᵁ V ≤ Out.nonzeroLocus t := fun x hx => by
      obtain ⟨y, hy, e⟩ := hV hx
      have e₁ : (π ∣_ U) ⟨x, h₁ hx⟩ = y := Subtype.ext ((morphismRestrict_base_coe π U _).trans e.symm)
      have e₂ : σ y = x := by
        rw [← e₁]
        exact congrArg (fun q => q (⟨x, h₁ hx⟩ : (π ⁻¹ᵁ U).toScheme)) (IsIso.hom_inv_id_assoc (π ∣_ U) (π ⁻¹ᵁ U).ι)
      rw [ht, ← e₂]
      exact hy
    exact (bijective_secHom_app hN t h₂).comp (bijective_unit_app π h₁ ha G)
  · obtain ⟨e⟩ := nonempty_coh_pushforward_equiv R π (fun _ => rfl) (twist E (lbPow L (d * (n + 1)))) hc hD'
      (hn _ (le_trans n.le_succ (Nat.le_mul_of_pos_left _ hd))) p
    have := hL.finite_coh (f := π ≫ f) (fun _ => rfl) (twist E (lbPow L (d * (n + 1)))) p
    exact Module.Finite.equiv e.symm

theorem support_pushforward_ssubset (ι : X' ⟶ X) [IsClosedImmersion ι] (E : X'.Modules) [E.IsQuasicoherent]
    (h : VanishesSomewhere E) : support ((Scheme.Modules.pushforward ι).obj E) ⊂ Set.range ι := by
  obtain ⟨W, ⟨z, hz⟩, hW⟩ := h
  refine ⟨fun x hx => by_contra fun hx' => ?_, fun hle => ?_⟩
  · obtain ⟨V, hV, hxV, hle⟩ := exists_affine_mem_le
      (U := ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩) x hx'
    have e : ι ⁻¹ᵁ V = ⊥ := le_bot_iff.1 fun y hy => (hle hy ⟨y, rfl⟩).elim
    have : Subsingleton Γ((Scheme.Modules.pushforward ι).obj E, V) := by
      change Subsingleton Γ(E, ι ⁻¹ᵁ V)
      exact hW _ (e ▸ bot_le) (hV.preimage ι)
    exact notMem_support_of_subsingleton _ hV hxV hx
  · obtain ⟨O, hO, e⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1 W.isOpen
    obtain ⟨V, hV, hxV, hle'⟩ := exists_affine_mem_le (U := ⟨O, hO⟩) (ι z) (e.ge hz)
    have : Subsingleton Γ((Scheme.Modules.pushforward ι).obj E, V) := by
      change Subsingleton Γ(E, ι ⁻¹ᵁ V)
      exact hW _ (fun y hy => e.le (hle' hy)) (hV.preimage ι)
    exact notMem_support_of_subsingleton _ hV hxV (hle ⟨z, rfl⟩)

theorem finite_coh_of_forall_modification {R : Type} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Sp R) [IsProper f]
    (h : ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι : Z ⟶ X) [IsClosedImmersion ι], ∃ (Z' : Scheme.{0}) (π : Z' ⟶ Z)
      (U : Z.Opens), IsProjOver (π ≫ ι ≫ f) ∧ (U : Set Z).Nonempty ∧ IsIso (π ∣_ U))
    (F : X.Modules) [IsFiniteQC F] : letI := algebraΓOfHom f; ∀ p, Module.Finite R (coh F p) := by
  letI := algebraΓOfHom f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := {}
  refine devissage X (fun F => ∀ p, Module.Finite R (coh F p)) (fun F hF p => ?_)
    (fun S hS _ _ h₁ h₃ => cohOn.forall_finite₂ R hS ⊤ h₁ h₃) (fun Z hZ ih G hG p => ?_) F inferInstance
  · have := cohOn.subsingleton_of_isZero hF ⊤ p
    infer_instance
  · have := isIntegral_red hZ
    letI := algebraΓOfHom (redι Z ≫ f)
    obtain ⟨Z', π, U, hP, hU, _⟩ := h _ (redι Z)
    have := finite_coh_of_modification (redι Z ≫ f) π hP hU (fun E hE hv q => by
      have := ih ((Scheme.Modules.pushforward (redι Z)).obj E)
        ⟨inferInstance, fun V hV => finite_sections_pushforward _ _ hV (hF := finite_sections E (hV.preimage _))⟩
        (range_redι Z ▸ support_pushforward_ssubset (redι Z) E hv) q
      exact Module.Finite.equiv (coh.pushforwardEquiv R (g := redι Z) (fun _ => rfl) E q)) G p
    exact Module.Finite.equiv (coh.pushforwardEquiv R (g := redι Z) (fun _ => rfl) G p).symm

end GlobalTheory.ProperFinite
