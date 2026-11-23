import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Mh

section pb

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {X Y : Scheme.{0}}

def pb (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

def val (x : Spec (CommRingCat.of B) ⟶ X) : Γ(X, ⊤) →+* B :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom

theorem valAt_top (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) : valAt x ⊤ h s = val x s := by
  simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_ext {j j' : X ⟶ Spec (CommRingCat.of A)} (h : ∀ a, pb j a = pb j' a) : j = j' := by
  apply ext_of_isAffine
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j'.appTop := by
    ext a
    exact h a
  exact (cancel_epi _).1 e

theorem pb_comp (f : Y ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) : pb (f ≫ j) a = f.appTop (pb j a) := by
  unfold pb
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem val_comp (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X) (s : Γ(X, ⊤)) :
    val (x ≫ f) s = val x (f.appTop s) := by
  unfold val
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem pb_spec (j : X ⟶ Spec (CommRingCat.of B)) (ψ : A →+* B) (a : A) :
    pb (j ≫ Spec.map (CommRingCat.ofHom ψ)) a = pb j (ψ a) := by
  simp only [pb, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem val_pb_id (b : B) : val (𝟙 _) (pb (𝟙 (Spec (CommRingCat.of B))) b) = b := by
  simp [val, pb]

theorem val_pb_comp (x : Spec (CommRingCat.of B) ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    val x (pb j a) = val (𝟙 _) (pb (x ≫ j) a) := by
  rw [pb_comp, ← val_comp, Category.id_comp]

theorem val_pb {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : x ≫ j = Spec.map (CommRingCat.ofHom φ)) (a : A) : val x (pb j a) = φ a := by
  have e := pb_spec (𝟙 (Spec (CommRingCat.of B))) φ a
  rw [Category.id_comp] at e
  rw [val_pb_comp, h, e, val_pb_id]

theorem val_id_injective : Function.Injective (val (𝟙 (Spec (CommRingCat.of B)))) := by
  intro s t hst
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) s) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) t) := by
    rw [hst]
  simpa [val] using e

theorem comp_eq_spec {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : ∀ a, val x (pb j a) = φ a) : x ≫ j = Spec.map (CommRingCat.ofHom φ) := by
  refine pb_ext fun a => val_id_injective ?_
  rw [← val_pb_comp, h, val_pb (Category.id_comp _)]

theorem exists_pb (φ : A →+* Γ(X, ⊤)) : ∃ j : X ⟶ Spec (CommRingCat.of A), ∀ a, pb j a = φ a := by
  refine ⟨(ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) (CommRingCat.ofHom φ).op,
    fun a => ?_⟩
  rw [pb, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  rfl

theorem spec_inj {φ ψ : A →+* B} (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_comp (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp]
  rfl

end pb

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T]

theorem sec_ext (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)} (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') :
    s = s' := by
  rw [← sub_eq_zero]
  refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
  rw [valAt_top, map_sub, h, sub_self]

theorem hom_ext_pt (Γ : QFGroup R T) {A : Type} [CommRing A] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
  pb_ext fun a => sec_ext Γ fun t => by rw [val_pb_comp, h, ← val_pb_comp]

theorem mem_top_iff (Γ : QFGroup R T) (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
    ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
  have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
      (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
    intro B _ X x U hx a b
    simp only [valAt, map_sub]
  constructor
  · intro hf t
    rw [Twhopf.mem_order] at hf
    have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
        ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
          valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
      fun g => hf t g (by simp)
    choose U hgU s hs using hreg
    obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
      (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
        intro g g'
        rw [← sub_eq_zero]
        apply Twhopf.sec_inj R T Γ _ _
        intro h hh
        have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
        have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
        refine (hsub _ _ hh _ _).trans ?_
        erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
        rw [hs, hs, sub_self])
    refine ⟨g0, fun h => ?_⟩
    have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
      Twhopf.top_le_of_mem _ z (hgU _)
    refine (valAt_top _ htop g0).symm.trans ?_
    refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
    erw [hglue ((Γ.pt h).left z)]
    exact hs _ h hh
  · intro hf
    rw [Twhopf.mem_order]
    intro t g _
    obtain ⟨s, hs⟩ := hf t
    unfold QFGroup.RegularAt
    exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩

omit [Finite T] in
theorem val_const (Γ : QFGroup R T) (t : T) (r : R) :
    val (Γ.pt t).left (pb Γ.G.hom r) = algebraMap R (FractionRing R) r :=
  val_pb (Over.w (Γ.pt t)) r

omit [Finite T] in
theorem val_emb {Γ : QFGroup R T} {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (a : A) :
    val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
  val_pb (hj.pt t) a

theorem exists_emb (Γ : QFGroup R T) (A : Subalgebra R (T → R))
    (hA : ∀ a : A, ∃ s : Γ(Γ.G.left, ⊤), ∀ t, val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t)) :
    ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of A), Γ.IsEmb A j := by
  choose s hs using hA
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := sec_ext Γ fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => sec_ext Γ fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := sec_ext Γ fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => sec_ext Γ fun t => by rw [hs, map_add, hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hom_ext_pt Γ fun t => by rw [hj'.pt, hpt]⟩
  apply hom_ext_pt Γ
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end PositivityTheory.HtPt.Mh
