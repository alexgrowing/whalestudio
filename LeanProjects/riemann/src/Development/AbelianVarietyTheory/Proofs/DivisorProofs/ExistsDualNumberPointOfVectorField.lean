import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.EpsPoint

variable {S : Type} [CommRing S]

abbrev proj (S : Type) [CommRing S] : Sp (DualNumber S) ⟶ Sp S := spMap (algebraMap S (DualNumber S))

def epsOn (V : (Sp (DualNumber S)).Opens) : Γ(Sp (DualNumber S), V) :=
  ((Sp (DualNumber S)).presheaf.map (homOfLE le_top).op).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps)

theorem epsOn_mul_self (V : (Sp (DualNumber S)).Opens) : epsOn V * epsOn V = 0 := by
  rw [epsOn, ← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem epsOn_res {V V' : (Sp (DualNumber S)).Opens} (h : V' ≤ V) :
    ((Sp (DualNumber S)).presheaf.map (homOfLE h).op).hom (epsOn V) = epsOn V' := by
  rw [epsOn, epsOn, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}

theorem field_one (he : IsField W e) {V : Z.Opens} (hV : V ≤ W) : e V 1 = 0 := by
  have h := he.2.1 V hV 1 1
  simp only [mul_one, one_mul] at h
  linear_combination -h

theorem field_zero (he : IsField W e) {V : Z.Opens} (hV : V ≤ W) : e V 0 = 0 := by
  have h := he.1 V hV 0 0
  simp only [add_zero] at h
  linear_combination -h

variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

include hg in
theorem le_inf_preimage (U : Z.Opens) : (proj S ≫ g₀) ⁻¹ᵁ U ≤ (proj S ≫ g₀) ⁻¹ᵁ (U ⊓ W) :=
  fun _ hx => TopologicalSpace.Opens.mem_inf.2 ⟨hx, hg trivial⟩

theorem appLE_res (U : Z.Opens) (f : Γ(Z, U)) :
    ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (resG Z inf_le_left f) =
      ((proj S ≫ g₀).app U).hom f := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]

def psi (he : IsField W e) (U : Z.Opens) : Γ(Z, U) →+* Γ(Sp (DualNumber S), (proj S ≫ g₀) ⁻¹ᵁ U) where
  toFun f := ((proj S ≫ g₀).app U).hom f + epsOn _ *
    ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (e (U ⊓ W) (resG Z inf_le_left f))
  map_one' := by simp only [map_one, field_one he inf_le_right, map_zero, mul_zero, add_zero]
  map_mul' f f' := by
    simp only [map_mul, he.2.1 _ inf_le_right, map_add, appLE_res g₀ hg]
    linear_combination -(((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom
      (e (U ⊓ W) (resG Z inf_le_left f)) * ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom
      (e (U ⊓ W) (resG Z inf_le_left f'))) * epsOn_mul_self (S := S) ((proj S ≫ g₀) ⁻¹ᵁ U)
  map_zero' := by simp only [map_zero, field_zero he inf_le_right, mul_zero, add_zero]
  map_add' f f' := by
    simp only [map_add, he.1 _ inf_le_right]
    ring

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

theorem psi_res (he : IsField W e) {U U' : Z.Opens} (h : U' ≤ U) (f : Γ(Z, U)) :
    psi g₀ hg he U' (resG Z h f) =
      ((Sp (DualNumber S)).presheaf.map (homOfLE (fun _ hx => h hx : (proj S ≫ g₀) ⁻¹ᵁ U' ≤ (proj S ≫ g₀) ⁻¹ᵁ U)).op).hom
        (psi g₀ hg he U f) := by
  simp only [psi, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_mul, epsOn_res]
  congr 1
  · rw [resG, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  · congr 1
    have h2 : resG Z (inf_le_left : U' ⊓ W ≤ U') (resG Z h f) =
        resG Z (inf_le_inf_right W h) (resG Z (inf_le_left : U ⊓ W ≤ U) f) := by
      simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h2, he.2.2 _ _ _ inf_le_right, resG, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

def cMap (he : IsField W e) : Z.presheaf ⟶ (proj S ≫ g₀).base _* (Sp (DualNumber S)).presheaf where
  app U := CommRingCat.ofHom (R := Γ(Z, U.unop)) (S := Γ(Sp (DualNumber S), (proj S ≫ g₀) ⁻¹ᵁ U.unop))
    (psi g₀ hg he U.unop)
  naturality U U' i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact psi_res g₀ hg he i.unop.le f

def pshHom (he : IsField W e) : (Sp (DualNumber S)).toPresheafedSpace.Hom Z.toPresheafedSpace :=
  ⟨(proj S ≫ g₀).base, cMap g₀ hg he⟩

theorem isLocal (he : IsField W e) (y : Sp (DualNumber S)) :
    IsLocalHom ((pshHom g₀ hg he).stalkMap y).hom := by
  constructor
  intro a ha
  obtain ⟨U, hU, f, rfl⟩ := TopCat.Presheaf.germ_exist _ a
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  change IsUnit ((Sp (DualNumber S)).presheaf.germ _ y hU (((proj S ≫ g₀).app U).hom f + epsOn _ *
    ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (e (U ⊓ W) (resG Z inf_le_left f)))) at ha
  rw [map_add] at ha
  have hn : IsNilpotent ((Sp (DualNumber S)).presheaf.germ _ y hU (epsOn _ *
      ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (e (U ⊓ W) (resG Z inf_le_left f)))) := by
    refine ⟨2, ?_⟩
    rw [← map_pow, mul_pow, pow_two (epsOn _), epsOn_mul_self, zero_mul, map_zero]
  have h2 := hn.neg.isUnit_add_right_of_commute ha (Commute.all _ _)
  rw [add_comm, add_neg_cancel_right] at h2
  exact (isUnit_map_iff ((proj S ≫ g₀).stalkMap y).hom _).mp
    ((congrArg IsUnit (Scheme.Hom.germ_stalkMap_apply (proj S ≫ g₀) U y hU f)).mpr h2)

def epsPoint (he : IsField W e) : Sp (DualNumber S) ⟶ Z :=
  ⟨⟨pshHom g₀ hg he, isLocal g₀ hg he⟩⟩

theorem epsPoint_base (he : IsField W e) : (epsPoint g₀ hg he).base = (proj S ≫ g₀).base := rfl

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

theorem fst_comp_proj : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ proj S = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, CommRingCat.ofHom_id, Spec.map_id]

theorem fst_app_epsOn (V : (Sp (DualNumber S)).Opens) :
    ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app V).hom (epsOn V) = 0 := by
  rw [epsOn, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  have : ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) = 0 := by
    have h1 := congrArg (fun q => q.hom DualNumber.eps)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom S S S).toRingHom))
    have h2 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom S S S).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv).hom DualNumber.eps = 0 := by
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ((TrivSqZeroExt.fstHom S S S).toRingHom DualNumber.eps) = 0
      have h3 : (TrivSqZeroExt.fstHom S S S).toRingHom DualNumber.eps = 0 := by simp
      rw [h3, map_zero]
    exact h1.symm.trans h2
  rw [this, map_zero]

theorem comp_eq_of_app {X T Y : Scheme.{0}} (i : X ⟶ T) (w q : T ⟶ Y) (hb : w.base = q.base)
    (h : ∀ U : Y.Opens, w.app U ≫ i.app (w ⁻¹ᵁ U) = q.app U ≫ i.app (q ⁻¹ᵁ U) ≫
      X.presheaf.map (eqToHom (by rw [hb]) : i ⁻¹ᵁ (w ⁻¹ᵁ U) ⟶ i ⁻¹ᵁ (q ⁻¹ᵁ U)).op) : i ≫ w = i ≫ q := by
  refine Scheme.Hom.ext (by rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, hb]) fun U => ?_
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app, h U]
  erw [Category.assoc, Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem fst_app_psi (he : IsField W e) (U : Z.Opens) (a : Γ(Z, U)) :
    ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app ((proj S ≫ g₀) ⁻¹ᵁ U)).hom (psi g₀ hg he U a) =
      ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app ((proj S ≫ g₀) ⁻¹ᵁ U)).hom (((proj S ≫ g₀).app U).hom a) := by
  simp only [psi, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_mul, fst_app_epsOn, zero_mul,
    add_zero]

theorem fst_comp (he : IsField W e) : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ epsPoint g₀ hg he = g₀ := by
  have hb : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ proj S ≫ g₀ = g₀ := by
    rw [← Category.assoc, fst_comp_proj, Category.id_comp]
  refine Eq.trans (comp_eq_of_app _ _ (proj S ≫ g₀) (epsPoint_base g₀ hg he) fun U => ?_) hb
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact fst_app_psi g₀ hg he U a

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

theorem valR_comp_epsPoint (he : IsField W e) {C : Type} [CommRing C] (x : Sp C ⟶ Sp (DualNumber S))
    (O : Z.Opens) (f : Γ(Z, O)) :
    valR (x ≫ epsPoint g₀ hg he) O f = valR x ((proj S ≫ g₀) ⁻¹ᵁ O) (psi g₀ hg he O f) := by
  rw [GlobalTheory.Points.valR_comp]
  rfl

theorem snd_valR (he : IsField W e) {S' : Type} [CommRing S'] (ρ : S →+* S') (O : Z.Opens) (hO : O ≤ W)
    (hρ : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O) (f : Γ(Z, O)) :
    (valR (spMap (dualMap ρ) ≫ epsPoint g₀ hg he) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := by
  have hxπ : spMap (dualMap ρ) ≫ proj S = proj S' ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hy : spMap (dualMap ρ) ≫ proj S ≫ g₀ = proj S' ≫ spMap ρ ≫ g₀ := by
    rw [← Category.assoc, hxπ, Category.assoc]
  have hyO : ⊤ ≤ (spMap (dualMap ρ) ≫ proj S ≫ g₀) ⁻¹ᵁ O := by
    rw [hy]
    exact GlobalTheory.Points.le_preimage_comp _ _ hρ (GlobalTheory.Points.le_preimage_top _)
  have hyW : ⊤ ≤ (spMap (dualMap ρ) ≫ proj S ≫ g₀) ⁻¹ᵁ W := by
    rw [← Category.assoc]
    exact GlobalTheory.Points.le_preimage_comp _ _ hg (GlobalTheory.Points.le_preimage_top _)
  have hyOW : ⊤ ≤ (spMap (dualMap ρ) ≫ proj S ≫ g₀) ⁻¹ᵁ (O ⊓ W) :=
    fun z hz => TopologicalSpace.Opens.mem_inf.2 ⟨hyO hz, hyW hz⟩
  have hx : ⊤ ≤ spMap (dualMap ρ) ⁻¹ᵁ ((proj S ≫ g₀) ⁻¹ᵁ O) := hyO
  rw [valR_comp_epsPoint]
  simp only [psi, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [GlobalTheory.Points.valR_add _ _ hx, GlobalTheory.Points.valR_mul _ _ hx, ← GlobalTheory.Points.valR_comp,
    GlobalTheory.Points.valR_appLE _ _ _ hx, he.2.2 O (O ⊓ W) inf_le_left hO f,
    GlobalTheory.Points.valR_res _ _ hyOW, epsOn, GlobalTheory.Points.valR_res _ _ hx, GlobalTheory.Points.valR_specMap, hy,
    GlobalTheory.Points.valR_spMap_comp _ _ _ hρ, GlobalTheory.Points.valR_spMap_comp _ _ _ hρ]
  simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_epsPoint : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e →
    ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z,
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧
        ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O →
          ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := by
  intro Z W e he S _ g₀ hg
  exact ⟨epsPoint g₀ hg he, fst_comp g₀ hg he, fun S' _ ρ O hO hρ f => snd_valR g₀ hg he ρ O hO hρ f⟩

end GlobalTheory.EpsPoint
