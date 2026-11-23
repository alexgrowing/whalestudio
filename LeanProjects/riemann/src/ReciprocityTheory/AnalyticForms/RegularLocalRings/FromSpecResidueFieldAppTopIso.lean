import Mathlib

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

def constSec (U : S.Opens) : ℂ →+* Γ(S, U) :=
  (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

def constRes (x : S) : ℂ →+* S.residueField x :=
  (S.evaluation ⊤ x trivial).hom.comp (constSec s ⊤)

def CPt (S : Scheme.{0}) : Type := {x : S // IsClosed ({x} : Set S)}

open Classical in

def valHom (x : S) : S.residueField x → ℂ :=
  if h : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ then h.choose else fun _ => 0

def val {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U) : ℂ :=
  valHom s x (S.evaluation U x hx f)

theorem fromSpecResidueField_appTop_iso (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop, Scheme.evaluation]
  have hid : (Spec (S.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
  simp [hid]

theorem constRes_eq (x : S) (hx : IsClosed ({x} : Set S)) [LocallyOfFiniteType s] :
    constRes s x = (residueFieldIsoBase s x hx).inv.hom := by
  have hφ := Scheme.ΓSpecIso_naturality (Spec.preimage (S.fromSpecResidueField x ≫ s))
  rw [Spec.map_preimage] at hφ
  have hpre : Spec.preimage (S.fromSpecResidueField x ≫ s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (S.fromSpecResidueField x ≫ s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField x)).hom := by
    rw [hφ, Iso.inv_hom_id_assoc]
  have hA : s.appLE ⊤ ⊤ le_top = s.appTop := (s.app_eq_appLE (U := ⊤)).symm
  have hc : constRes s x = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      S.evaluation ⊤ x trivial).hom := rfl
  rw [hc, hA, ← fromSpecResidueField_appTop_iso x]
  show _ = (Spec.preimage (S.fromSpecResidueField x ≫ s)).hom
  rw [hpre, Scheme.Hom.comp_appTop, Category.assoc]

theorem valHom_unique [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S))
    (ψ : S.residueField x →+* ℂ) (h : ψ.comp (constRes s x) = RingHom.id ℂ) :
    ψ = (residueFieldIsoBase s x hx).hom.hom := by
  ext y
  have h1 : (residueFieldIsoBase s x hx).inv.hom ((residueFieldIsoBase s x hx).hom.hom y) = y := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      RingHom.id_apply]
  have h2 := congrArg (fun f : ℂ →+* ℂ => f ((residueFieldIsoBase s x hx).hom.hom y)) h
  simp only [RingHom.comp_apply, RingHom.id_apply, constRes_eq s x hx, h1] at h2
  exact h2

theorem valHom_spec [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    ((residueFieldIsoBase s x hx).hom.hom).comp (constRes s x) = RingHom.id ℂ := by
  rw [constRes_eq s x hx, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]

theorem valHom_eq [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    valHom s x = (residueFieldIsoBase s x hx).hom.hom := by
  have hex : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ :=
    ⟨_, valHom_spec s x hx⟩
  unfold valHom
  rw [dif_pos hex, valHom_unique s x hx _ hex.choose_spec]

theorem evaluation_res {U V : S.Opens} (h : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    S.evaluation V x hx (S.presheaf.map (homOfLE h).op f) = S.evaluation U x (h hx) f := by
  have key : S.presheaf.map (homOfLE h).op ≫ S.evaluation V x hx = S.evaluation U x (h hx) := by
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  rw [← key]
  rfl

theorem constSec_res (U : S.Opens) (c : ℂ) :
    constSec s U c = S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (constSec s ⊤ c) := by
  simp only [constSec, RingHom.comp_apply]
  rw [← s.appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : U ≤ ⊤)).op]
  rfl

theorem isClosed_image_of_closed {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t] (x : S)
    (hc : IsClosed ({x} : Set S)) : IsClosed ({g.base x} : Set T) := by
  haveI : JacobsonSpace T := AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace t
  haveI : AlgebraicGeometry.LocallyOfFiniteType (g ≫ t) := by rw [hg]; infer_instance
  haveI : AlgebraicGeometry.LocallyOfFiniteType g := AlgebraicGeometry.locallyOfFiniteType_of_comp g t
  have hx : x ∈ closedPoints S := by simpa [mem_closedPoints_iff] using hc
  have := g.closePoints_subset_preimage_closedPoints hx
  simpa [mem_closedPoints_iff] using this

theorem residueFieldMap_constRes {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) (x : S) :
    (g.residueFieldMap x).hom.comp (constRes t (g.base x)) = constRes s x := by
  have hA : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)), y.appLE ⊤ ⊤ le_top = y.appTop :=
    fun Y y => (y.app_eq_appLE (U := ⊤)).symm
  have hc : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)) (z : Y), constRes y z =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ y.appTop ≫ Y.evaluation ⊤ z trivial).hom := by
    intro Y y z
    rw [← hA]; rfl
  rw [hc, hc, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc]
  rw [Scheme.evaluation_naturality g x (V := ⊤) trivial, ← hg, Scheme.Hom.comp_appTop,
    Category.assoc]
  rfl

theorem existsUnique_valHom [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    (∃! φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ) ∧
      Function.Bijective (valHom s x) := by
  refine ⟨⟨_, valHom_spec s x hx, fun ψ hψ => valHom_unique s x hx ψ hψ⟩, ?_⟩
  rw [valHom_eq s x hx]
  exact (residueFieldIsoBase s x hx).commRingCatIsoToRingEquiv.bijective

theorem val_ringHom [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    ∃ φ : Γ(S, U) →+* ℂ, ∀ f, φ f = val s f x hx := by
  refine ⟨(residueFieldIsoBase s x hc).hom.hom.comp (S.evaluation U x hx).hom, fun f => ?_⟩
  unfold val
  rw [valHom_eq s x hc]
  rfl

theorem val_const [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) (c : ℂ) : val s (constSec s U c) x hx = c := by
  unfold val
  rw [constSec_res s U c, evaluation_res le_top _ x hx, valHom_eq s x hc]
  exact DFunLike.congr_fun (valHom_spec s x hc) c

theorem val_restrict {U V : S.Opens} (hVU : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    val s (S.presheaf.map (homOfLE hVU).op f) x hx = val s f x (hVU hx) := by
  unfold val
  rw [evaluation_res hVU f x hx]

theorem val_eq_zero_iff [LocallyOfFiniteType s] {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) : val s f x hx = 0 ↔ S.evaluation U x hx f = 0 := by
  unfold val
  rw [valHom_eq s x hc]
  exact map_eq_zero_iff _ (residueFieldIsoBase s x hc).commRingCatIsoToRingEquiv.injective

theorem val_comp {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T) (hg : g ≫ t = s)
    [LocallyOfFiniteType s] [LocallyOfFiniteType t] {U : T.Opens} {V : S.Opens} (hVU : V ≤ g ⁻¹ᵁ U)
    (f : Γ(T, U)) (x : S) (hx : x ∈ V) (hc : IsClosed ({x} : Set S)) :
    IsClosed ({g.base x} : Set T) ∧ val s (g.appLE U V hVU f) x hx = val t f (g.base x) (hVU hx) := by
  have hcl := isClosed_image_of_closed s t g hg x hc
  refine ⟨hcl, ?_⟩
  have hmor : g.appLE U V hVU ≫ S.evaluation V x hx =
      T.evaluation U (g.base x) (hVU hx) ≫ g.residueFieldMap x := by
    rw [Scheme.evaluation_naturality g x (V := U) (hVU hx :), Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  have hres : (residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom =
      (residueFieldIsoBase t (g.base x) hcl).hom.hom := by
    apply valHom_unique t (g.base x) hcl
    rw [RingHom.comp_assoc, residueFieldMap_constRes s t g hg x, valHom_spec s x hc]
  unfold val
  rw [valHom_eq s x hc, valHom_eq t (g.base x) hcl, ← hres]
  show _ = ((residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom)
    ((T.evaluation U (g.base x) (hVU hx)).hom f)
  rw [RingHom.comp_apply, ← RingHom.comp_apply (g.residueFieldMap x).hom, ← CommRingCat.hom_comp,
    ← hmor]
  rfl

end

end ReciprocityTheory.AnForm.R
