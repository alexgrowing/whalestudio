import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens} {ι : Type} [Fintype ι]

def IsFrame (e : ι → Γ(F, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i))

theorem resM_linearCombination (e : ι → Γ(F, U)) (h : V ≤ U) (h' : W ≤ V) (a : ι → Γ(X, V)) :
    resM F h' (Fintype.linearCombination Γ(X, V) (fun i => resM F h (e i)) a) =
      Fintype.linearCombination Γ(X, W) (fun i => resM F (h'.trans h) (e i))
        fun i => resG X h' (a i) := by
  simp only [Fintype.linearCombination_apply, map_sum, resM_smul, resM_resM]

namespace IsFrame

variable {e : ι → Γ(F, U)}

def basis (he : IsFrame e) (h : V ≤ U) : Module.Basis ι Γ(X, V) Γ(F, V) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (he V h)).symm

theorem basis_equivFun_symm (he : IsFrame e) (h : V ≤ U) (a : ι → Γ(X, V)) :
    (he.basis h).equivFun.symm a = ∑ i, a i • resM F h (e i) := by
  rw [basis, Module.Basis.equivFun_ofEquivFun, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply,
    Fintype.linearCombination_apply]

@[simp] theorem basis_apply (he : IsFrame e) (h : V ≤ U) (i : ι) :
    he.basis h i = resM F h (e i) := by
  classical
  have := he.basis_equivFun_symm h (Pi.single i 1)
  rw [Module.Basis.equivFun_symm_apply] at this
  simpa [Pi.single_apply] using this

theorem coe_basis (he : IsFrame e) (h : V ≤ U) : ⇑(he.basis h) = fun i => resM F h (e i) :=
  funext (he.basis_apply h)

theorem repr_resM (he : IsFrame e) (h : V ≤ U) (h' : W ≤ V) (s : Γ(F, V)) (i : ι) :
    (he.basis (h'.trans h)).repr (resM F h' s) i = resG X h' ((he.basis h).repr s i) := by
  conv_lhs => rw [← (he.basis h).sum_repr s]
  simp only [map_sum, resM_smul, basis_apply, resM_resM]
  simp only [← he.basis_apply (h'.trans h)]
  rw [← map_sum, Module.Basis.repr_sum_self]

theorem res (he : IsFrame e) (h : V ≤ U) : IsFrame fun i => resM F h (e i) := fun W h' => by
  simpa only [resM_resM] using he W (h'.trans h)

end IsFrame

theorem isFrame_of_basis {e : ι → Γ(F, U)}
    (b : ∀ V : X.Opens, V ≤ U → Module.Basis ι Γ(X, V) Γ(F, V))
    (hb : ∀ V h i, b V h i = resM F h (e i)) : IsFrame e := fun V h => by
  have : Fintype.linearCombination Γ(X, V) (fun i => resM F h (e i)) =
      (b V h).equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hb]
  rw [this]
  exact (b V h).equivFun.symm.bijective

theorem isFrame_iff {e : ι → Γ(F, U)} : IsFrame e ↔ ∀ (V : X.Opens) (h : V ≤ U),
    LinearIndependent Γ(X, V) (fun i => resM F h (e i)) ∧
      ⊤ ≤ Submodule.span Γ(X, V) (Set.range fun i => resM F h (e i)) :=
  ⟨fun he V h => by
    rw [← he.coe_basis h]
    exact ⟨(he.basis h).linearIndependent, (he.basis h).span_eq.ge⟩,
  fun H => isFrame_of_basis (fun V h => Module.Basis.mk (H V h).1 (H V h).2)
    fun _ _ _ => Module.Basis.mk_apply _ _ _⟩

theorem isFrame_of_forall_exists {e : ι → Γ(F, U)}
    (H : ∀ (V : X.Opens) (h : V ≤ U) (x : X), x ∈ V → ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧
      Function.Bijective (Fintype.linearCombination Γ(X, W) fun i => resM F (h'.trans h) (e i))) :
    IsFrame e := by
  have inj (V : X.Opens) (h : V ≤ U) :
      Function.Injective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)) := by
    intro a b hab
    choose W hW hx hb using fun x : V => H V h x x.2
    funext i
    refine fun_ext_of_cover W hW (fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩) fun x => ?_
    have := congrArg (resM F (hW x)) hab
    rw [resM_linearCombination, resM_linearCombination] at this
    exact congrFun ((hb x).1 this) i
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx hb using fun x : V => H V h x x.2
  have hc : V ≤ iSup W := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  choose a ha using fun x => (hb x).2 (resM F (hW x) s)
  have key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← resM_linearCombination e ((hW x).trans h), ← resM_linearCombination e ((hW y).trans h),
      ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

namespace IsFrame

variable {e : ι → Γ(F, U)}

theorem map_of_linearEquiv (he : IsFrame e) {e' : ι → Γ(G, U)}
    (φ : ∀ V : X.Opens, V ≤ U → (Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V)))
    (hφ : ∀ V h i, φ V h (resM F h (e i)) = resM G h (e' i)) : IsFrame e' :=
  isFrame_of_basis (fun V h => (he.basis h).map (φ V h)) fun V h i => by
    rw [Module.Basis.map_apply, basis_apply, hφ]

theorem map_iso (he : IsFrame e) (φ : F ⟶ G) [IsIso φ] : IsFrame fun i => φ.app U (e i) :=
  he.map_of_linearEquiv
    (fun V _ => LinearEquiv.ofBijective (appLinear φ V)
      (ConcreteCategory.bijective_of_isIso (φ.app V)))
    fun _ h i => app_resM φ h (e i)

theorem comp_equiv (he : IsFrame e) {κ : Type} [Fintype κ] (σ : κ ≃ ι) : IsFrame (e ∘ σ) :=
  isFrame_of_basis (fun _ h => (he.basis h).reindex σ.symm) fun _ _ _ => by simp

theorem bijective_stalk (he : IsFrame e) (x : X) (hx : x ∈ U) :
    Function.Bijective (Fintype.linearCombination (X.presheaf.stalk x)
      fun i => (F.presheaf.germ U x hx (e i) : (F.presheaf.stalk x :))) := by
  have hg (V : X.Opens) (h : V ≤ U) (hxV : x ∈ V) (a : ι → Γ(X, V)) :
      F.presheaf.germ V x hxV (Fintype.linearCombination Γ(X, V) (fun i => resM F h (e i)) a) =
        Fintype.linearCombination (X.presheaf.stalk x)
          (fun i => (F.presheaf.germ U x hx (e i) : (F.presheaf.stalk x :)))
          fun i => X.presheaf.germ V x hxV (a i) := by
    simp only [Fintype.linearCombination_apply, map_sum, QCoh.germ_smul, germ_resM]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    choose W hW b hb using fun i => X.presheaf.exists_germ_eq (a i)
    let V : X.Opens := U ⊓ Finset.univ.inf W
    have hxV : x ∈ V := ⟨hx, by
      rw [Opens.coe_finset_inf]; simpa using hW⟩
    have hV (i : ι) : V ≤ W i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
    have hb' (i : ι) : X.presheaf.germ V x hxV (resG X (hV i) (b i)) = a i := by
      rw [← hb i]; exact X.presheaf.germ_res_apply (homOfLE (hV i)) x hxV (b i)
    have h0 := hg V inf_le_left hxV fun i => resG X (hV i) (b i)
    simp only [hb'] at h0
    rw [show (fun i => a i) = a from rfl, ha, ← map_zero (F.presheaf.germ V x hxV).hom] at h0
    obtain ⟨V', hxV', i₁, i₂, h1⟩ := F.presheaf.germ_eq x hxV hxV _ _ h0
    have h2 : resM F i₁.le (Fintype.linearCombination Γ(X, V) (fun i => resM F inf_le_left (e i))
      fun i => resG X (hV i) (b i)) = 0 := h1.trans (map_zero _)
    rw [resM_linearCombination, ← map_zero (Fintype.linearCombination Γ(X, V')
      fun i => resM F (i₁.le.trans inf_le_left) (e i))] at h2
    funext i
    have h3 := congrFun ((he V' _).1 h2) i
    rw [← hb' i, ← X.presheaf.germ_res_apply i₁ x hxV']
    exact (congrArg _ h3).trans (map_zero _)
  · intro t
    obtain ⟨V, h, hxV, s, rfl⟩ := Twist.exists_germ_eq_of_mem hx t
    obtain ⟨a, rfl⟩ := (he V h).2 s
    exact ⟨_, (hg V h hxV a).symm⟩

def stalkBasis (he : IsFrame e) (x : X) (hx : x ∈ U) :
    Module.Basis ι (X.presheaf.stalk x) (F.presheaf.stalk x :) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (he.bijective_stalk x hx)).symm

@[simp] theorem stalkBasis_apply (he : IsFrame e) (x : X) (hx : x ∈ U) (i : ι) :
    he.stalkBasis x hx i = F.presheaf.germ U x hx (e i) := by
  classical
  simp [stalkBasis, Fintype.linearCombination_apply, Pi.single_apply]

theorem pullback [F.IsQuasicoherent] (he : IsFrame e) (f : Y ⟶ X) :
    IsFrame fun i => QCoh.pullbackSections f F (le_refl (f ⁻¹ᵁ U)) (e i) := by
  refine isFrame_of_forall_exists fun V h y hy => ?_
  obtain ⟨U', hU', hyU', hle⟩ := QCoh.exists_affine_mem_le (f y) (h hy)
  obtain ⟨W, hW, hyW, hWle⟩ := QCoh.exists_affine_mem_le (U := V ⊓ f ⁻¹ᵁ U') y ⟨hy, hyU'⟩
  refine ⟨W, hWle.trans inf_le_left, hyW, ?_⟩
  have e₁ : W ≤ f ⁻¹ᵁ U' := hWle.trans inf_le_right
  letI := QCoh.appLEAlgebra f e₁
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj F) e₁
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj F) e₁
  let b := (QCoh.isBaseChange_pullbackSections f F hW hU' e₁).basis (he.basis hle)
  have hb (i : ι) : b i = resM _ ((hWle.trans inf_le_left).trans h)
      (QCoh.pullbackSections f F (le_refl (f ⁻¹ᵁ U)) (e i)) := by
    rw [IsBaseChange.basis_apply, basis_apply]
    exact (QCoh.pullbackSections_res f F e₁ hle _).trans
      (QCoh.res_pullbackSections f F _ _ _).symm
  have : Fintype.linearCombination Γ(Y, W) (fun i => resM _ ((hWle.trans inf_le_left).trans h)
      (QCoh.pullbackSections f F (le_refl (f ⁻¹ᵁ U)) (e i))) = b.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hb]
  rw [this]
  exact b.equivFun.symm.bijective

variable {e' : ι → Γ(G, U)}

def equiv (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) : Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V) :=
  (he.basis h).equiv (he'.basis h) (Equiv.refl ι)

theorem equiv_resM_frame (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (i : ι) :
    he.equiv he' h (resM F h (e i)) = resM G h (e' i) := by
  rw [← he.basis_apply, equiv, Module.Basis.equiv_apply, basis_apply, Equiv.refl_apply]

theorem equiv_resM (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : W ≤ V) (s : Γ(F, V)) :
    he.equiv he' (h'.trans h) (resM F h' s) = resM G h' (he.equiv he' h s) := by
  obtain ⟨a, rfl⟩ := (he V h).2 s
  simp only [Fintype.linearCombination_apply, map_sum, resM_smul, resM_resM, map_smul,
    equiv_resM_frame]

def restrictIso (he : IsFrame e) (he' : IsFrame e') (g : Y ⟶ X) [IsOpenImmersion g]
    (hg : g.opensRange ≤ U) : F.restrict g ≅ G.restrict g :=
  Twist.restrictIsoOfLinear (fun _ h => he.equiv he' h) (fun h h' s => he.equiv_resM he' h h' s)
    g hg

def iso {e : ι → Γ(F, ⊤)} {e' : ι → Γ(G, ⊤)} (he : IsFrame e) (he' : IsFrame e') : F ≅ G :=
  isoOfLinear (fun _ => he.equiv he' le_top) fun h s => he.equiv_resM he' le_top h s

theorem iso_hom_app {e : ι → Γ(F, ⊤)} {e' : ι → Γ(G, ⊤)} (he : IsFrame e) (he' : IsFrame e')
    (i : ι) : (he.iso he').hom.app ⊤ (e i) = e' i := by
  have := he.equiv_resM_frame he' le_rfl i
  rwa [resM_self, resM_self] at this

end IsFrame

theorem isFrame_restrict_iff (g : Y ⟶ X) [IsOpenImmersion g] {W : Y.Opens}
    (e : ι → Γ(F, g ''ᵁ W)) : IsFrame (F := F.restrict g) (U := W) e ↔ IsFrame e := by
  have key (V : Y.Opens) (h : V ≤ W) :
      Function.Bijective (Fintype.linearCombination Γ(Y, V)
        fun i => resM (F.restrict g) h (e i)) ↔
      Function.Bijective (Fintype.linearCombination Γ(X, g ''ᵁ V)
        fun i => resM F (g.image_mono h) (e i)) := by
    have hb : Function.Bijective fun (a : ι → Γ(Y, V)) (i : ι) => (g.appIso V).inv (a i) :=
      Function.Bijective.piMap fun _ => ConcreteCategory.bijective_of_isIso (g.appIso V).inv
    rw [← hb.of_comp_iff]
    rfl
  refine ⟨fun H V h => ?_, fun H V h => (key V h).2 (H _ _)⟩
  obtain ⟨V', rfl⟩ : ∃ V' : Y.Opens, V = g ''ᵁ V' := ⟨g ⁻¹ᵁ V, by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact (inf_eq_right.2 (h.trans (g.image_le_opensRange W))).symm⟩
  have h' : V' ≤ W := by
    simpa only [Scheme.Hom.preimage_image_eq] using g.preimage_mono h
  exact (key V' h').1 (H V' h')

theorem isFrame_one (U : X.Opens) :
    IsFrame (F := structureModule X) (U := U) fun _ : Fin 1 => (1 : Γ(X, U)) :=
  isFrame_of_basis (fun V _ => Module.Basis.singleton (Fin 1) Γ(X, V)) fun V h i =>
    (Module.Basis.singleton_apply (Fin 1) Γ(X, V) i).trans (map_one (resG X h)).symm

variable (X) in

def freeFrame (ι : Type) (i : ι) : Γ(freeModule X ι, ⊤) :=
  Scheme.Modules.Hom.app (M := structureModule X) (N := freeModule X ι)
    (SheafOfModules.ιFree i) ⊤ (1 : Γ(X, ⊤))

theorem isFrame_biproduct (ι : Type) [Fintype ι] [HasBiproduct fun _ : ι => structureModule X] :
    IsFrame fun i : ι =>
      (biproduct.ι (fun _ : ι => structureModule X) i).app ⊤ (1 : Γ(X, ⊤)) := by
  classical
  let φ (V : X.Opens) : Γ(⨁ fun _ : ι => structureModule X, V) ≃ₗ[Γ(X, V)] (ι → Γ(X, V)) :=
    QCoh.biproductSectionsEquiv (fun _ : ι => structureModule X) V
  refine isFrame_of_basis (fun V _ => Module.Basis.ofEquivFun (φ V)) fun V h i => ?_
  rw [Module.Basis.coe_ofEquivFun]
  refine (QCoh.biproductSectionsEquiv_symm_apply _ _ _).trans
    (Eq.trans ?_ (app_resM (biproduct.ι (fun _ : ι => structureModule X) i) h _))
  refine (Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)).trans ?_
  · exact (congrArg _ (Pi.single_eq_of_ne hj _)).trans (map_zero _)
  · exact congrArg _ ((Pi.single_eq_same _ _).trans (map_one (resG X h)).symm)

variable (X) in

theorem isFrame_freeFrame (ι : Type) [Fintype ι] : IsFrame (freeFrame X ι) := by
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  have := (isFrame_biproduct (X := X) ι).map_iso
    (biproduct.isoCoproduct fun _ : ι => structureModule X).hom
  have e (i : ι) : Scheme.Modules.Hom.app
      (biproduct.isoCoproduct fun _ : ι => structureModule X).hom ⊤
      ((biproduct.ι (fun _ : ι => structureModule X) i).app ⊤ (1 : Γ(X, ⊤))) =
      freeFrame X ι i := by
    refine (QCoh.app_app _ _ _ _).trans ?_
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
    rfl
  rw [funext e] at this
  exact this

variable (F) in

def IsVB (r : ℕ) : Prop := ∀ x : X, ∃ (U : X.Opens) (e : Fin r → Γ(F, U)), x ∈ U ∧ IsFrame e

variable {r s : ℕ}

theorem isVB_of_frames (hr : Fintype.card ι = r)
    (h : ∀ x : X, ∃ (U : X.Opens) (e : ι → Γ(F, U)), x ∈ U ∧ IsFrame e) : IsVB F r := fun x =>
  have ⟨U, _, hx, he⟩ := h x
  ⟨U, _, hx, he.comp_equiv (Fintype.equivFinOfCardEq hr).symm⟩

theorem IsFrame.isVB {e : ι → Γ(F, ⊤)} (he : IsFrame e) : IsVB F (Fintype.card ι) :=
  isVB_of_frames rfl fun _ => ⟨⊤, e, trivial, he⟩

variable (X) in

theorem isVB_freeModule (ι : Type) [Fintype ι] : IsVB (freeModule X ι) (Fintype.card ι) :=
  (isFrame_freeFrame X ι).isVB

variable (X) in

theorem isVB_freeModule_fin (r : ℕ) : IsVB (freeModule X (Fin r)) r := by
  simpa using isVB_freeModule X (Fin r)

variable (X) in

theorem isVB_structureModule : IsVB (structureModule X) 1 :=
  fun _ => ⟨⊤, _, trivial, isFrame_one ⊤⟩

theorem isFrame_chartSec {L : LB X} (hL : L.IsLB) (i : L.ι) :
    IsFrame fun _ : Fin 1 => LB.chartSec hL i :=
  (isFrame_one (L.U i)).map_of_linearEquiv (fun _ h => (LB.chartEquiv hL i h).symm)
    fun V h _ => (congrArg (· • resM (toMod L) h (LB.chartSec hL i))
      (map_one (resG X h))).trans (one_smul _ _)

theorem isVB_toMod {L : LB X} (hL : L.IsLB) : IsVB (toMod L) 1 := fun x =>
  have ⟨i, hi⟩ := Semi.LB.mem_of_cover hL x
  ⟨_, _, hi, isFrame_chartSec hL i⟩

theorem isVB_iff_restrict : IsVB F r ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (freeModule U.toScheme (Fin r) ≅ F.restrict U.ι) := by
  refine forall_congr' fun x => ⟨fun ⟨U, e, hx, he⟩ => ⟨U, hx, ⟨?_⟩⟩, fun ⟨U, hx, ⟨φ⟩⟩ => ?_⟩
  · exact (isFrame_freeFrame _ _).iso
      ((isFrame_restrict_iff U.ι _).2 (he.res (U.ι_image_le ⊤)))
  · exact ⟨U.ι ''ᵁ ⊤, _, by simpa using hx,
      (isFrame_restrict_iff U.ι _).1 ((isFrame_freeFrame _ _).map_iso φ.hom)⟩

namespace IsVB

theorem exists_affine (h : IsVB F r) {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens) (e : Fin r → Γ(F, U)), IsAffineOpen U ∧ x ∈ U ∧ U ≤ V ∧ IsFrame e :=
  have ⟨U, _, hxU, he⟩ := h x
  have ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le (U := U ⊓ V) x ⟨hxU, hx⟩
  ⟨W, _, hW, hxW, hle.trans inf_le_right, he.res (hle.trans inf_le_left)⟩

theorem of_iso (h : IsVB F r) (φ : F ≅ G) : IsVB G r := fun x =>
  have ⟨U, _, hx, he⟩ := h x
  ⟨U, _, hx, he.map_iso φ.hom⟩

theorem isQuasicoherent (h : IsVB F r) : F.IsQuasicoherent := by
  choose U e hx he using h
  exact Twist.isQuasicoherent_of_locally_iso (F := freeModule X (Fin r)) (U := U)
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩) fun x =>
      ((isFrame_freeFrame X (Fin r)).res le_top).restrictIso (he x) _ (U x).opensRange_ι.le

theorem isFiniteQC (h : IsVB F r) : IsFiniteQC F :=
  have := h.isQuasicoherent
  .of_forall_exists_affine fun x =>
    have ⟨U, _, hU, hx, _, he⟩ := h.exists_affine (V := ⊤) (x := x) trivial
    ⟨U, hU, hx, Module.Finite.of_basis (he.basis le_rfl)⟩

set_option backward.isDefEq.respectTransparency false in

theorem isLocallyFree (h : IsVB F r) : F.IsLocallyFree := by
  choose U hx he using isVB_iff_restrict.1 h
  have φ (x : X) : SheafOfModules.free (R := X.ringCatSheaf.over (U x)) (Fin r) ≅ F.over (U x) :=
    let e := Scheme.Modules.overEquiv (U x)
    Sigma.mapIso (fun _ : Fin r =>
      ((U x).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm) ≪≫
    (PreservesCoproduct.iso e.inverse fun _ : Fin r => structureModule (U x).toScheme).symm ≪≫
    e.inverse.mapIso (he x).some ≪≫
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv (U x)).app F).symm ≪≫
      (e.unitIso.app (F.over (U x))).symm
  let q : SheafOfModules.LocalGeneratorsData.{0} F :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff]
        exact top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
      generators x := (SheafOfModules.free.generatingSections (Fin r)).ofEpi (φ x).hom }
  haveI : q.IsLocallyFreeData := ⟨fun x => LB.isIso_ofEpi_π (φ x)⟩
  exact q.isLocallyFree

theorem nonempty_basis_stalk (h : IsVB F r) (x : X) :
    Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x :)) :=
  have ⟨_, _, hx, he⟩ := h x
  ⟨he.stalkBasis x hx⟩

theorem free_stalk (h : IsVB F r) (x : X) :
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x :) :=
  (h.nonempty_basis_stalk x).elim .of_basis

theorem finrank_stalk (h : IsVB F r) (x : X) :
    Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x :) = r :=
  (h.nonempty_basis_stalk x).elim fun b => by simpa using Module.finrank_eq_card_basis b

theorem finrank_fibre (h : IsVB F r) (x : X) :
    Module.finrank (X.residueField x) (QCoh.fibre F x) = r :=
  (h.nonempty_basis_stalk x).elim fun b => by
    simpa using Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (X.residueField x) b)

theorem rank_unique [Nonempty X] (h : IsVB F r) (h' : IsVB F s) : r = s :=
  (h.finrank_stalk (Classical.arbitrary X)).symm.trans (h'.finrank_stalk _)

theorem pullback (h : IsVB F r) (f : Y ⟶ X) : IsVB ((Scheme.Modules.pullback f).obj F) r :=
  fun y =>
    have := h.isQuasicoherent
    have ⟨_, _, hx, he⟩ := h (f y)
    ⟨_, _, hx, he.pullback f⟩

theorem restrict (h : IsVB F r) (g : Y ⟶ X) [IsOpenImmersion g] : IsVB (F.restrict g) r :=
  (h.pullback g).of_iso ((Scheme.Modules.restrictFunctorIsoPullback g).app F).symm

theorem twist (h : IsVB F r) {L : LB X} (hL : L.IsLB) : IsVB (twist F L) r := fun x => by
  obtain ⟨i, hi⟩ := Semi.LB.mem_of_cover hL x
  obtain ⟨U, e, -, hx, hle, he⟩ := h.exists_affine hi
  refine ⟨U, fun j => (Twist.chartEquiv hL i hle).symm (e j), hx,
    he.map_of_linearEquiv (fun V hV => (Twist.chartEquiv hL i (hV.trans hle)).symm) ?_⟩
  exact fun V hV j => (Twist.resM_chartEquiv_symm hL i hle hV _).symm

theorem biprod (hF : IsVB F r) (hG : IsVB G s) : IsVB (F ⊞ G) (r + s) := by
  refine isVB_of_frames (ι := Fin r ⊕ Fin s) (by simp) fun x => ?_
  obtain ⟨U, e, hx, he⟩ := hF x
  obtain ⟨V, e', -, hx', hle, he'⟩ := hG.exists_affine hx
  refine ⟨V, Sum.elim (fun i => (biprod.inl : F ⟶ F ⊞ G).app V (resM F hle (e i)))
    fun i => (biprod.inr : G ⟶ F ⊞ G).app V (e' i), hx', isFrame_of_basis
      (fun W h => ((he.basis (h.trans hle)).prod (he'.basis h)).map
        (QCoh.biprodSectionsEquiv F G W).symm) ?_⟩
  rintro W h (i | i)
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl, Sum.elim_inl, ← app_resM]
    change (Limits.biprod.inl : F ⟶ F ⊞ G).app W _ + (Limits.biprod.inr : G ⟶ F ⊞ G).app W 0 = _
    simp
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr, Sum.elim_inr, ← app_resM]
    change (Limits.biprod.inl : F ⟶ F ⊞ G).app W 0 + (Limits.biprod.inr : G ⟶ F ⊞ G).app W _ = _
    simp

end IsVB

theorem isVB_congr (φ : F ≅ G) : IsVB F r ↔ IsVB G r :=
  ⟨fun h => h.of_iso φ, fun h => h.of_iso φ.symm⟩

theorem isVB_zero_iff : IsVB F 0 ↔ IsZero F := by
  refine ⟨fun h => QCoh.support_eq_empty_iff.1 (Set.eq_empty_of_forall_notMem fun x =>
    QCoh.notMem_support_iff.2 ?_), fun h x => ⟨⊤, Fin.elim0, trivial, fun V _ => ?_⟩⟩
  · obtain ⟨b⟩ := h.nonempty_basis_stalk x
    exact b.equivFun.injective.subsingleton
  · have := QCoh.subsingleton_sections_of_isZero h V
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

variable (F) in

structure Sub where

  sec (V : X.Opens) : Submodule Γ(X, V) Γ(F, V)

  res_mem {V W : X.Opens} (h : W ≤ V) {s : Γ(F, V)} : s ∈ sec V → resM F h s ∈ sec W

  mem_of_local {V : X.Opens} {s : Γ(F, V)} :
    (∀ x ∈ V, ∃ (W : X.Opens) (h : W ≤ V), x ∈ W ∧ resM F h s ∈ sec W) → s ∈ sec V

namespace Sub

variable (N : Sub F)

def res (h : W ≤ V) : N.sec V →+ N.sec W where
  toFun s := ⟨resM F h s.1, N.res_mem h s.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def presheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (N.sec V.unop)
  map f := AddCommGrpCat.ofHom (N.res (leOfHom f.unop))
  map_id V := by
    ext s
    exact resM_self _ _
  map_comp f g := by
    ext s
    exact (resM_resM _ _ _).symm

theorem isSheaf_presheaf : N.presheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  obtain ⟨t, ht⟩ := exists_sec_of_cover W (le_iSup W) le_rfl (fun k => (sf k).1)
    fun k l => congrArg Subtype.val (hsf k l)
  refine ⟨⟨t, N.mem_of_local fun x hx => ?_⟩, fun k => Subtype.ext (ht k), fun u hu =>
    Subtype.ext (sec_ext_of_cover W (le_iSup W) le_rfl fun k =>
      (congrArg Subtype.val (hu k)).trans (ht k).symm)⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
  exact ⟨W k, le_iSup W k, hk, (ht k).symm ▸ (sf k).2⟩

def toMod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) (N.presheaf.obj V) :=
    fun V => inferInstanceAs (Module Γ(X, V.unop) (N.sec V.unop))
  { val := PresheafOfModules.ofPresheaf N.presheaf fun _ _ f r m =>
      Subtype.ext (resM_smul (leOfHom f.unop) r m.1)
    isSheaf := N.isSheaf_presheaf }

def incl : N.toMod ⟶ F :=
  homOfLinear (F := N.toMod) (fun V => (N.sec V).subtype) fun _ _ => rfl

def mkSec (s : Γ(F, V)) (hs : s ∈ N.sec V) : Γ(N.toMod, V) := (⟨s, hs⟩ : N.sec V)

@[simp] theorem incl_app_mkSec (s : Γ(F, V)) (hs : s ∈ N.sec V) : N.incl.app V (N.mkSec s hs) = s := rfl

theorem incl_app_injective (V : X.Opens) : Function.Injective (N.incl.app V) := Subtype.val_injective

theorem incl_app_mem (s : Γ(N.toMod, V)) : N.incl.app V s ∈ N.sec V := (show N.sec V from s).2

theorem mem_sec_iff {s : Γ(F, V)} : s ∈ N.sec V ↔ ∃ t, N.incl.app V t = s :=
  ⟨fun h => ⟨N.mkSec s h, rfl⟩, fun ⟨t, ht⟩ => ht ▸ N.incl_app_mem t⟩

instance mono_incl : Mono N.incl :=
  QCoh.mono_of_locally_app_injective _ fun W _ hx => ⟨W, hx, le_rfl, N.incl_app_injective W⟩

def lift (φ : G ⟶ F) (h : ∀ V s, φ.app V s ∈ N.sec V) : G ⟶ N.toMod :=
  homOfLinear (G := N.toMod) (fun V => (appLinear φ V).codRestrict (N.sec V) (h V))
    fun hW s => Subtype.ext (app_resM φ hW s)

@[reassoc (attr := simp)] theorem lift_incl (φ : G ⟶ F) (h : ∀ V s, φ.app V s ∈ N.sec V) :
    N.lift φ h ≫ N.incl = φ := rfl

theorem exists_comp_incl_iff (φ : G ⟶ F) :
    (∃ ψ : G ⟶ N.toMod, ψ ≫ N.incl = φ) ↔ ∀ V s, φ.app V s ∈ N.sec V :=
  ⟨fun ⟨ψ, h⟩ V s => h ▸ N.incl_app_mem (ψ.app V s), fun h => ⟨N.lift φ h, rfl⟩⟩

theorem cokernel_π_app_eq_zero_iff {s : Γ(F, V)} :
    (cokernel.π N.incl).app V s = 0 ↔ s ∈ N.sec V :=
  (QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel N.incl) V s).trans
    N.mem_sec_iff.symm

theorem isQuasicoherent [F.IsQuasicoherent]
    (h : ∀ (U : X.Opens), IsAffineOpen U → ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      resM F (X.basicOpen_le f) t ∈ N.sec _ → ∃ n : ℕ, f ^ n • t ∈ N.sec U) :
    N.toMod.IsQuasicoherent := by
  refine (QCoh.isQuasicoherent_iff_forall_affine _).2 fun U hU f =>
    (QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨n, t, e⟩ := QCoh.exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl (N.incl.app _ s)
    obtain ⟨m, hm⟩ := h U hU f t (by
      change F.presheaf.map _ t ∈ _
      rw [← e]
      exact (N.sec _).smul_mem _ (N.incl_app_mem s))
    refine ⟨m + n, N.mkSec _ hm, N.incl_app_injective _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, QCoh.app_res, incl_app_mkSec, Scheme.Modules.map_smul, ← e,
      pow_add, mul_smul, map_pow]
  · obtain ⟨n, e⟩ := QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl (N.incl.app _ t)
      (by rw [← QCoh.app_res, ht, map_zero])
    exact ⟨n, N.incl_app_injective _ (by rw [Scheme.Modules.Hom.app_smul, e, map_zero])⟩

end Sub

def Sub.ker (φ : F ⟶ G) : Sub F where
  sec V := LinearMap.ker (appLinear φ V)
  res_mem h s hs := (app_resM φ h s).trans ((congrArg _ hs).trans (map_zero _))
  mem_of_local {V s} H := by
    choose W hW hx hs using fun x : V => H x x.2
    exact sec_ext_of_cover W hW (fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩) fun x =>
      (app_resM φ _ s).symm.trans ((hs x).trans (map_zero _).symm)

def Sub.iInf {κ : Type*} (N : κ → Sub F) : Sub F where
  sec V := ⨅ k, (N k).sec V
  res_mem h _ hs := (Submodule.mem_iInf _).2 fun k =>
    (N k).res_mem h ((Submodule.mem_iInf _).1 hs k)
  mem_of_local H := (Submodule.mem_iInf _).2 fun k => (N k).mem_of_local fun x hx =>
    have ⟨W, h, hxW, hs⟩ := H x hx
    ⟨W, h, hxW, (Submodule.mem_iInf _).1 hs k⟩

def Sub.ofStalks (N : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) : Sub F where
  sec V :=
    { carrier := {s | ∀ (x : X) (hx : x ∈ V), F.presheaf.germ V x hx s ∈ N x}
      add_mem' := fun hs ht x hx => by rw [map_add]; exact add_mem (hs x hx) (ht x hx)
      zero_mem' := fun x hx => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun a s hs x hx => by
        rw [QCoh.germ_smul]; exact (N x).smul_mem _ (hs x hx) }
  res_mem h s hs x hx := by rw [germ_resM]; exact hs x (h hx)
  mem_of_local H x hx := by
    obtain ⟨W, h, hxW, hs⟩ := H x hx
    have := hs x hxW
    rwa [germ_resM] at this

example (s : Γ(F, V)) :
    (s ∈ (Sub.ker (𝟙 F)).sec V ↔ s = 0) ∧ s ∈ (Sub.ker (0 : F ⟶ G)).sec V :=
  ⟨Iff.rfl, rfl⟩

end GlobalTheory.VB
