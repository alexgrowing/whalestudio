import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionSubobject
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.QcqsPushforward
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Extend

section Defs

variable {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}

def extMap (f : P.restrict O.ι ⟶ E) (S : Subobject E) :
    P ⟶ (Scheme.Modules.pushforward O.ι).obj (cokernel S.arrow) :=
  (Scheme.Modules.restrictAdjunction O.ι).homEquiv P _ (f ≫ cokernel.π S.arrow)

def extSub (f : P.restrict O.ι ⟶ E) (S : Subobject E) : Subobject P :=
  kernelSubobject (extMap O f S)

lemma extMap_app (f : P.restrict O.ι ⟶ E) (S : Subobject E) (V : X.Opens) (x : Γ(P, V)) :
    (extMap O f S).app V x = (f ≫ cokernel.π S.arrow).app (O.ι ⁻¹ᵁ V)
      ((P.restrictAppIso O.ι _).inv (P.presheaf.map (homOfLE (O.ι.image_preimage_le V)).op x)) := by
  rfl

lemma mem_secs_extSub (f : P.restrict O.ι ⟶ E) (S : Subobject E) (V : X.Opens) (x : Γ(P, V)) :
    x ∈ secs (extSub O f S) V ↔ (extMap O f S).app V x = 0 := by
  constructor
  · rintro ⟨k, rfl⟩
    change ((kernelSubobject (extMap O f S)).arrow.app V ≫ (extMap O f S).app V) k = 0
    rw [← Scheme.Modules.Hom.comp_app, kernelSubobject_arrow_comp, Scheme.Modules.Hom.zero_app]
    rfl
  · intro hx
    obtain ⟨k, hk⟩ := kernel_ι_app_exact (extMap O f S) V x hx
    refine ⟨(kernelSubobjectIso (extMap O f S)).inv.app V k, ?_⟩
    rw [← hk, ← kernelSubobject_arrow' (extMap O f S)]
    rfl

end Defs

end GlobalTheory.CompanionTheory.GE.Extend

namespace GlobalTheory.CompanionTheory.GE.Extend

lemma isNoetherian_of_proper {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] : IsNoetherian X := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  first | infer_instance | exact {}

lemma isClosed_image {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ T : (O : Scheme.{0}).IdealSheafData,
      IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) →
      IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro T hT
  have e : T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A)) =
      (T.subschemeι ≫ O.ι) ≫ (X ↘ Spec (.of A)) := by
    rw [Category.assoc]; rfl
  haveI : UniversallyClosed ((T.subschemeι ≫ O.ι) ≫ (X ↘ Spec (.of A))) := by
    rw [← e]; infer_instance
  haveI : UniversallyClosed (T.subschemeι ≫ O.ι) :=
    UniversallyClosed.of_comp_of_isSeparated _ (X ↘ Spec (.of A))
  have hc : IsClosed (Set.range (T.subschemeι ≫ O.ι)) :=
    (T.subschemeι ≫ O.ι).isClosedMap.isClosed_range
  have hr : Set.range (T.subschemeι ≫ O.ι) = O.ι '' (T.support : Set (O : Scheme.{0})) := by
    rw [← T.range_subschemeι, ← Set.range_comp]
    rfl
  rwa [hr] at hc

lemma map_injective_of_le_of_le {Y : Scheme.{0}} (M : Y.Modules) {U U' : Y.Opens} (h : U ≤ U')
    (h' : U' ≤ U) : Function.Injective (M.presheaf.map (homOfLE h).op) := by
  intro a b hab
  have e : ∀ z, M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op z) = z := by
    intro z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rw [show (homOfLE h).op ≫ (homOfLE h').op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
    rfl
  rw [← e a, hab, e b]

variable {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}

lemma extMap_app_image (f : P.restrict O.ι ⟶ E) (S : Subobject E) (W : (O : Scheme.{0}).Opens)
    (x : Γ(P, O.ι ''ᵁ W)) :
    (extMap O f S).app (O.ι ''ᵁ W) x = 0 ↔
      (cokernel.π S.arrow).app W (f.app W ((P.restrictAppIso O.ι W).inv x)) = 0 := by
  have h1 : W ≤ O.ι ⁻¹ᵁ (O.ι ''ᵁ W) := (O.ι.preimage_image_eq W).ge
  have h2 : O.ι ⁻¹ᵁ (O.ι ''ᵁ W) ≤ W := (O.ι.preimage_image_eq W).le
  set y := (P.restrictAppIso O.ι _).inv
    (P.presheaf.map (homOfLE (O.ι.image_preimage_le (O.ι ''ᵁ W))).op x) with hy
  have hres : (P.restrict O.ι).presheaf.map (homOfLE h1).op y = (P.restrictAppIso O.ι W).inv x := by
    rw [hy, Scheme.Modules.restrictAppIso_inv_map_apply]
    change P.presheaf.map _ (P.presheaf.map _ x) = x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hid : ∀ g : Opposite.op (O.ι ''ᵁ W) ⟶ Opposite.op (O.ι ''ᵁ W), P.presheaf.map g x = x := by
      intro g
      rw [show g = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
      rfl
    exact hid _
  have key : (cokernel S.arrow).presheaf.map (homOfLE h1).op
      ((f ≫ cokernel.π S.arrow).app (O.ι ⁻¹ᵁ (O.ι ''ᵁ W)) y) =
      (cokernel.π S.arrow).app W (f.app W ((P.restrictAppIso O.ι W).inv x)) := by
    have nat := ConcreteCategory.congr_hom
      ((f ≫ cokernel.π S.arrow).mapPresheaf.naturality (homOfLE h1).op) y
    refine nat.symm.trans ?_
    change (f ≫ cokernel.π S.arrow).app W ((P.restrict O.ι).presheaf.map (homOfLE h1).op y) = _
    rw [hres, Scheme.Modules.Hom.comp_app]
    rfl
  rw [extMap_app, ← key]
  constructor
  · intro h
    rw [h]
    exact AddMonoidHom.map_zero _
  · intro h
    exact map_injective_of_le_of_le _ h1 h2 (h.trans (map_zero _).symm)

lemma extMap_app_eq_zero_of_disjoint (f : P.restrict O.ι ⟶ E) (S : Subobject E)
    {T : Set (O : Scheme.{0})} (hT : Scheme.Modules.SupportedIn (cokernel S.arrow) T) (V : X.Opens)
    (hV : Disjoint (V : Set X) (O.ι '' T)) (x : Γ(P, V)) : (extMap O f S).app V x = 0 := by
  rw [extMap_app]
  refine hT _ ?_ _
  rw [Set.disjoint_left]
  intro y hy hyT
  exact Set.disjoint_left.1 hV hy ⟨y, hyT, rfl⟩

end GlobalTheory.CompanionTheory.GE.Extend

namespace GlobalTheory.CompanionTheory.GE.Extend

lemma qc_extSub {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) {P : X.Modules}
    {E : (O : Scheme.{0}).Modules} [P.IsQuasicoherent] (hE : IsCoherent E)
    (f : P.restrict O.ι ⟶ E) (S : Subobject E) (hS : (S : (O : Scheme.{0}).Modules).IsQuasicoherent) :
    ((extSub O f S : Subobject P) : X.Modules).IsQuasicoherent := by
  haveI := hS
  haveI : IsNoetherian X := isNoetherian_of_proper (A := A)
  haveI := (isCoherent_cokernel S.arrow hE).1
  haveI := isQuasicoherent_pushforward_of_qcqs O.ι (cokernel S.arrow)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelSubobjectIso (extMap O f S)).symm (isQuasicoherent_kernel _)

lemma exists_powSub_lift {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent →
      ∀ (f : P.restrict O.ι ⟶ E), Epi f → ∀ (n : ℕ) (W : (O : Scheme.{0}).Opens), IsAffineOpen W →
      ∀ y : Γ(E, W), y ∈ secs (powSub I E n) W →
        ∃ t ∈ secs (powSub I P n) (O.ι ''ᵁ W), f.app W ((P.restrictAppIso O.ι W).inv t) = y := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf n W hW y hy
  haveI := hP
  haveI := hE
  haveI := hf
  haveI : (P.restrict O.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
  rw [secs_powSub I E hE n W hW] at hy
  simp only [secs_powSub I P hP n _ hW']
  have hmul : ∀ (a : Γ(X, O.ι ''ᵁ W)) (m : Γ(P, O.ι ''ᵁ W)),
      f.app W ((P.restrictAppIso O.ι W).inv (a • m)) =
        (O.ι.appIso W).hom a • f.app W ((P.restrictAppIso O.ι W).inv m) := by
    intro a m
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]
  let JP : Submodule Γ(X, O.ι ''ᵁ W) Γ(P, O.ι ''ᵁ W) :=
    Ideal.map (toFunctions (A := A) (O.ι ''ᵁ W)) (I ^ n) • ⊤
  let N : Submodule Γ((O : Scheme.{0}), W) Γ(E, W) :=
    { carrier := {y | ∃ t ∈ JP, f.app W ((P.restrictAppIso O.ι W).inv t) = y}
      add_mem' := by
        rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
        exact ⟨t + t', JP.add_mem ht ht', by rw [map_add, map_add]⟩
      zero_mem' := ⟨0, JP.zero_mem, by rw [map_zero, map_zero]⟩
      smul_mem' := by
        rintro r _ ⟨t, ht, rfl⟩
        refine ⟨(O.ι.appIso W).inv r • t, JP.smul_mem _ ht, ?_⟩
        rw [hmul]
        congr 1
        rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
        rfl }
  have hJ : Ideal.map (toFunctions (A := A) W) (I ^ n) =
      Ideal.map (O.ι.appIso W).hom.hom (Ideal.map (toFunctions (A := A) (O.ι ''ᵁ W)) (I ^ n)) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact (ImageOpen.toFunctions_open O W r).symm
  have hsurj : Function.Surjective (O.ι.appIso W).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (O.ι.appIso W).hom).2
  have hle : (Ideal.map (toFunctions (A := A) W) (I ^ n) • ⊤ : Submodule Γ((O : Scheme.{0}), W) Γ(E, W))
      ≤ N := by
    refine Submodule.smul_le.2 fun a ha m _ => ?_
    rw [hJ] at ha
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 ha
    obtain ⟨z, rfl⟩ := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen f hW m
    obtain ⟨z', rfl⟩ : ∃ z', (P.restrictAppIso O.ι W).inv z' = z := ⟨z, rfl⟩
    exact ⟨b • z', Submodule.smul_mem_smul hb Submodule.mem_top, hmul b z'⟩
  exact hle hy

lemma le_of_cover {X : Scheme.{0}} (O : X.Opens) {Z : Set X} (hZ : IsClosed Z)
    (hZO : Z ⊆ (O : Set X)) {P : X.Modules} [P.IsQuasicoherent] (S S' : Subobject P)
    (hS : (S : X.Modules).IsQuasicoherent) (hS' : (S' : X.Modules).IsQuasicoherent)
    (h1 : ∀ W : (O : Scheme.{0}).Opens, IsAffineOpen W → secs S (O.ι ''ᵁ W) ⊆ secs S' (O.ι ''ᵁ W))
    (h2 : ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) Z → secs S U ⊆ secs S' U) :
    S ≤ S' := by
  let V : (O : Scheme.{0}).affineOpens ⊕ {U : X.affineOpens // Disjoint ((U : X.Opens) : Set X) Z} →
      X.Opens := Sum.elim (fun W => O.ι ''ᵁ (W : (O : Scheme.{0}).Opens)) (fun U => (U.1 : X.Opens))
  refine le_of_secs_subset_cover S S' hS hS' V ?_ ?_ ?_
  · rintro (W | U)
    · exact W.2.image_of_isOpenImmersion O.ι
    · exact U.1.2
  · rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ (O : Set X)
    · rw [← Scheme.Opens.range_ι] at hx
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
        (O : Scheme.{0}).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl ⟨W, hW⟩, ⟨y, hyW, rfl⟩⟩
    · have hxZ : x ∈ Zᶜ := fun h => hx (hZO h)
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUZ⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxZ hZ.isOpen_compl
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨Sum.inr ⟨⟨U, hU⟩, Set.subset_compl_iff_disjoint_right.1 hUZ⟩, hxU⟩
  · rintro (W | U)
    · exact h1 W.1 W.2
    · exact h2 U.1.1 U.1.2 U.2

end GlobalTheory.CompanionTheory.GE.Extend

namespace GlobalTheory.CompanionTheory.GE.Extend

theorem extend : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ T : (O : Scheme.{0}).IdealSheafData, IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) → Scheme.Modules.SupportedIn (cokernel (S 0).arrow) (T.support : Set (O : Scheme.{0})) → IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) ∧ ∃ Sb : ℕ → Subobject P, ClosedSys I P Sb ∧ (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) ∧ ∀ e (V : X.Opens), Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs (Sb e) V = Set.univ := by
  intro A _ _ I X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf S hS T hT hsupp
  haveI := hP.1
  haveI := hE.1
  have hZ := isClosed_image (A := A) O T hT
  set Z : Set X := O.ι '' (T.support : Set (O : Scheme.{0})) with hZdef
  have hZO : Z ⊆ (O : Set X) := by
    rintro _ ⟨y, -, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩

  have hsuppe : ∀ e, Scheme.Modules.SupportedIn (cokernel (S e).arrow) (T.support : Set (O : Scheme.{0})) :=
    fun e => Comb.supportedIn_of_secs_eq_univ hE.1 (hS.qcoh e) fun U hU hd =>
      Comb.secs_sys_univ hS hE.1 hU (Comb.secs_eq_univ_of_supportedIn hE.1 (hS.qcoh 0) hsupp hU hd) e
  let Sb : ℕ → Subobject P := fun e => extSub O f (S e)
  have hq : ∀ e, ((Sb e : Subobject P) : X.Modules).IsQuasicoherent :=
    fun e => qc_extSub (A := A) O hE f (S e) (hS.qcoh e)
  have hchar : ∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W),
      x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W := by
    intro e W hW x
    haveI := hS.qcoh e
    rw [mem_secs_extSub, extMap_app_image]
    exact (mem_range_app_iff (S e).arrow hW _).symm
  have huniv : ∀ e (V : X.Opens), Disjoint (V : Set X) Z → secs (Sb e) V = Set.univ := by
    intro e V hV
    refine Set.eq_univ_of_forall fun x => ?_
    rw [mem_secs_extSub]
    exact extMap_app_eq_zero_of_disjoint O f (S e) (hsuppe e) V hV x
  have hpowq : ∀ e, ((powSub I P (e + 1) : Subobject P) : X.Modules).IsQuasicoherent :=
    fun e => (closedSys_pow I P).qcoh e
  have hpow : ∀ e, powSub I P (e + 1) ≤ Sb e := by
    intro e
    refine le_of_cover O hZ hZO _ _ (hpowq e) (hq e) (fun W hW x hx => ?_)
      (fun U _ hU x _ => by rw [huniv e U hU]; trivial)
    rw [hchar e W hW]
    exact Comb.secs_mono (hS.pow_le e) W (ImageOpen.map_mem_secs_powSub I O hP.1 hE.1 f (e + 1) W hW x hx)
  have hsup : ∀ e, (((Sb (e + 1) ⊔ powSub I P (e + 1)) : Subobject P) : X.Modules).IsQuasicoherent ∧
      ∀ V : X.Opens, IsAffineOpen V → secs (Sb (e + 1) ⊔ powSub I P (e + 1)) V =
        {x | ∃ s ∈ secs (Sb (e + 1)) V, ∃ t ∈ secs (powSub I P (e + 1)) V, x = s + t} :=
    fun e => supsecs hP.1 _ _ (hq (e + 1)) (hpowq e)
  refine ⟨hZ, Sb, ⟨hq, hpow, fun e => le_antisymm ?_ ?_⟩, hchar, huniv⟩
  · refine le_of_cover O hZ hZO _ _ (hq e) (hsup e).1 (fun W hW x hx => ?_) (fun U hU hd x _ => ?_)
    · have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
      rw [hchar e W hW, hS.succ e,
        (supsecs hE.1 _ _ (hS.qcoh (e + 1)) ((closedSys_pow I E).qcoh e)).2 W hW] at hx
      obtain ⟨s, hs, t, ht, hst⟩ := hx
      obtain ⟨t', ht', hft'⟩ := exists_powSub_lift I O hP.1 hE.1 f hf (e + 1) W hW t ht
      rw [(hsup e).2 _ hW']
      refine ⟨x - t', ?_, t', ht', by abel⟩
      rw [hchar (e + 1) W hW, map_sub, map_sub, hft', hst, add_sub_cancel_right]
      exact hs
    · rw [(hsup e).2 U hU]
      refine ⟨x, by rw [huniv (e + 1) U hd]; trivial, 0, ⟨0, map_zero _⟩, (add_zero x).symm⟩
  · refine sup_le ?_ (hpow e)
    refine le_of_cover O hZ hZO _ _ (hq (e + 1)) (hq e) (fun W hW x hx => ?_)
      (fun U _ hU x _ => by rw [huniv e U hU]; trivial)
    rw [hchar e W hW]
    rw [hchar (e + 1) W hW] at hx
    exact Comb.secs_mono ((hS.succ e).symm ▸ le_sup_left) W hx

end GlobalTheory.CompanionTheory.GE.Extend
