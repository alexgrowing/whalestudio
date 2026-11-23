import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormLinks
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormClosed

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.Act

section Mass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.LatDict

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}

theorem inclCrd_inj {y y' : (VS D).V} (h : incl X.B.I (X.crd y) = incl X.B.I (X.crd y')) : y = y' := by
  apply X.bas.repr.injective
  ext i
  have h2 : X.crd y i = X.crd y' i := Formalism.L2.SG.Pf.inclInj_holds X (congrFun h i)
  have h3 : X.ιE.symm (X.bas.repr y i) = X.ιE.symm (X.bas.repr y' i) := h2
  exact X.ιE.symm.injective h3

theorem eq_zero_of_Xs {x : (VS D).V} (hx : x ∈ Xs X) (hf : ∀ a, (VS D).hT (X.fY a) x = 0) : x = 0 := by
  have h := pX_of_mem (e := X.eX) (f := X.fY) X.ef x hx
  rw [pX_apply] at h
  simp only [hf, zero_smul, Finset.sum_const_zero] at h
  exact h.symm

private theorem map_X_eq_of_mem_stabF {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ stabF D (X.Fu u)) :
    (X.Fu u).X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = (X.Fu u).X := by
  have hX : (X.Fu u).X = (X.Fu u).Xa D.R.rS := by
    unfold Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
    congr 1
    ext v
    simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [hX]
  exact hβ.2.1 D.R.rS

theorem stab_perpS {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ stabF D (X.Fu u)) {x : (VS D).V}
    (hx : x ∈ perpS (VS D) (X.Fu u).X) : β x ∈ perpS (VS D) (X.Fu u).X := by
  intro w hw
  have hw' : w ∈ (X.Fu u).X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    rw [map_X_eq_of_mem_stabF hβ]
    exact hw
  obtain ⟨w', hw'X, rfl⟩ := hw'
  exact (hβ.1 w' x).trans (hx w' hw'X)

theorem stab_X {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ stabF D (X.Fu u)) {x : (VS D).V}
    (hx : x ∈ (X.Fu u).X) : β x ∈ (X.Fu u).X := by
  rw [← map_X_eq_of_mem_stabF hβ]
  exact Submodule.mem_map_of_mem hx

def indW (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ stabF D (X.Fu u)) :
    WbQ D (X.Fu u) →ₗ[D.host.E] WbQ D (X.Fu u) :=
  Submodule.mapQ _ _ ((β : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (fun x hx => stab_perpS hβ hx))
    (fun x hx => stab_X hβ hx)

theorem indW_mk (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ stabF D (X.Fu u))
    (x : perpS (VS D) (X.Fu u).X) :
    indW β hβ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨β x.1, stab_perpS hβ x.2⟩ := rfl

theorem indW_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hβ : β ∈ stabF D (X.Fu u)) (hΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) :
    (indW β hβ : WbQ D (X.Fu u) → WbQ D (X.Fu u)) ∈ autLz D (X.Fu u) Λ :=
  ⟨β, hβ, hΛ, by intros; rfl⟩

theorem eq_of_indW {β β' : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ stabF D (X.Fu u))
    (hβ' : β' ∈ stabF D (X.Fu u)) (he : ∀ a, β (X.eX a) = X.eX a) (he' : ∀ a, β' (X.eX a) = X.eX a)
    (hf : ∀ a, β (X.fY a) = X.fY a) (hf' : ∀ a, β' (X.fY a) = X.fY a)
    (h : indW β hβ = indW β' hβ') : β = β' := by
  have hXs : (X.Fu u).X = Xs X := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e u]; rfl
  ext y
  have hdec : y = (y - prV X y) + prV X y := by abel
  have h1 : β (y - prV X y) = y - prV X y := by
    rw [sub_prV_eq, map_add, map_sum, map_sum]
    simp only [map_smul, he, hf]
  have h1' : β' (y - prV X y) = y - prV X y := by
    rw [sub_prV_eq, map_add, map_sum, map_sum]
    simp only [map_smul, he', hf']
  have hw : prV X y ∈ perpS (VS D) (X.Fu u).X := fun x hx => by
    rw [hXs] at hx
    exact hT_Xs_prV X hx y
  have h2 := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨prV X y, hw⟩)
  rw [indW_mk, indW_mk, Submodule.Quotient.eq] at h2
  have hd : β (prV X y) - β' (prV X y) ∈ Xs X := by
    rw [← hXs]; exact h2
  have hz : β (prV X y) - β' (prV X y) = 0 := by
    refine eq_zero_of_Xs hd fun a => ?_
    have ha := Formalism.L2.SG.Saturated.isom_apply hβ.1 (X.fY a) (prV X y)
    have ha' := Formalism.L2.SG.Saturated.isom_apply hβ'.1 (X.fY a) (prV X y)
    rw [hf] at ha
    rw [hf'] at ha'
    rw [map_sub, ha, ha', sub_self]
  rw [hdec, map_add, map_add, h1, h1', sub_eq_zero.1 hz]

variable {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

def GamL (q : {Λ // Λ ∈ what₂}) : Type :=
  {g : Gam X u // colD (cs.h (cs.base q.1)) (iotaF X u g * cs.h (cs.base q.1)) ∈ X.B.I.Kset}

theorem aK_eq (hb : Hfin X u) (γ : Gam X u) :
    ((hb : X.B.I.Gf) * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf) * ((hb : X.B.I.Gf) * X.xu u) =
      colD hb (iotaF X u γ * hb) := by
  first
    | rfl
    | (simp only [colD, Subgroup.coe_mul]; group)
    | (simp only [colD, Subgroup.coe_mul, Submonoid.coe_mul]; group)
    | (unfold colD; group)
    | (simp [colD, mul_assoc])

def gamL_levi (TR : TypedRed X) (q : {Λ // Λ ∈ what₂}) (g : GamL cs q) : Aset TR cs q :=
  ⟨levi TR (colD (cs.h (cs.base q.1)) (iotaF X u g.1 * cs.h (cs.base q.1))),
    g.1, by rw [aK_eq]; exact g.2, by rw [aK_eq]⟩

theorem isUni_one (TR : TypedRed X) (v : TR.Pl) : Formalism.L2.SG.GGMirabolic.IsUni D.R.k ((1 : Iof TR) v) := by
  unfold Formalism.L2.SG.GGMirabolic.IsUni
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply, ne_of_gt hij]

theorem gamL_levi_bij (TR : TypedRed X) (hK : X.LevelSubgroupCharacter) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK)
    (q : {Λ // Λ ∈ what₂}) : Function.Bijective (gamL_levi cs TR q) := by
  set hb : Hfin X u := cs.h (cs.base q.1) with hhb
  constructor
  · rintro ⟨g1, hP1⟩ ⟨g2, hP2⟩ heq
    have heq' : levi TR (colD hb (iotaF X u g1 * hb)) = levi TR (colD hb (iotaF X u g2 * hb)) :=
      congrArg Subtype.val heq
    have hmK : colD (iotaF X u g1 * hb) (iotaF X u g2 * hb) ∈ X.B.I.Kset := by
      rw [← colD_mul _ hb, ← colD_inv]; exact K_mul X.B.I (K_inv X.B.I hP1) hP2
    have hlm : levi TR (colD (iotaF X u g1 * hb) (iotaF X u g2 * hb)) = 1 := by
      rw [← colD_mul _ hb, ← colD_inv, levi_mul TR (good_inv X (good_colD hP1)) (good_colD hP2),
        levi_inv TR (good_colD hP1), heq', inv_mul_cancel]
    have hmU : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k
        (levi TR (colD (iotaF X u g1 * hb) (iotaF X u g2 * hb)) v) := by
      rw [hlm]; exact isUni_one TR
    have hm2 := mem_level_of_unitriangular TR (good_colD hmK) (ncong_colDiff u _ _ hmK) hmU
    have hku := colD_ku hK hm2
    have h0 : g1⁻¹ * g2 = 1 := by
      refine hN hb (g1⁻¹ * g2) ?_
      have e : (hb : Hfin X u)⁻¹ * iotaF X u (g1⁻¹ * g2) * hb =
          (iotaF X u g1 * hb)⁻¹ * (iotaF X u g2 * hb) := by
        simp only [map_mul, map_inv]; group
      rw [e]; exact hku
    rw [inv_mul_eq_one] at h0
    subst h0
    rfl
  · rintro ⟨x, γ, hγK, hx⟩
    refine ⟨⟨γ, by rw [← aK_eq]; exact hγK⟩, Subtype.ext ?_⟩
    show levi TR _ = x
    rw [hx]; exact congrArg (levi TR) (aK_eq _ _).symm

end Mass

end Formalism.L2.SG.Pf.Act

namespace Formalism.L2.SG.Pf.Act

section Mass2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.LatDict Formalism.L2.SG.Pf.LatDictK

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}

def isoG (g : Gam X u) : (VS D).V ≃ₗ[D.host.E] (VS D).V := (gamIsom_of X (inclInj_holds X) u g).choose

theorem isoG_stab (g : Gam X u) : isoG g ∈ stabF D (X.Fu u) := (gamIsom_of X (inclInj_holds X) u g).choose_spec.1

theorem isoG_spec (g : Gam X u) (y : (VS D).V) :
    incl X.B.I (X.crd (isoG g y)) = X.B.I.fmat (g : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y) := by
  first
    | exact (gamIsom_of X (inclInj_holds X) u g).choose_spec.2 y
    | exact (gamIsom_of X (inclInj_holds X) u g).choose_spec.2.1 y
    | exact ((gamIsom_of X (inclInj_holds X) u g).choose_spec.2 y).1
    | exact (gamIsom_of X (inclInj_holds X) u g).choose_spec.2.1 y

theorem isoG_fix (g : Gam X u) (y : (VS D).V) (hy : X.crd y ∈ fixSet X u) : isoG g y = y := by
  apply inclCrd_inj
  rw [isoG_spec]
  exact Formalism.L2.SG.PoincareInHH.Cut.hfin_fix (h := iotaF X u g) (v := X.crd y) (hv := hy)

theorem isoG_e (g : Gam X u) (a : Fin D.R.rS) : isoG g (X.eX a) = X.eX a :=
  isoG_fix g _ (Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix (X := X) (u := u) (a := a))

theorem isoG_f (g : Gam X u) (a : Fin D.R.rS) : isoG g (X.fY a) = X.fY a :=
  isoG_fix g _ (Formalism.L2.SG.PoincareInHH.Cut.fR_mem_fix (X := X) (u := u) (a := a))

theorem gf_eq {x x' : X.B.I.Gf} (h : ∀ y : (VS D).V,
    X.B.I.fmat x *ᵥ incl X.B.I (X.crd y) = X.B.I.fmat x' *ᵥ incl X.B.I (X.crd y)) : x = x' := by
  have hm : X.B.I.fmat x = X.B.I.fmat x' := by
    ext i j
    have hj := congrFun (h (X.bas j)) i
    have hc : incl X.B.I (X.crd (X.bas j)) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp [Formalism.L2.SG.HidaSetting.incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf]
      · simp [Formalism.L2.SG.HidaSetting.incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, hk,
          Ne.symm hk, Finsupp.single_apply]
    rw [hc] at hj
    simp only [Matrix.mulVec_single_one, Matrix.transpose_apply] at hj
    exact hj
  apply Subtype.ext
  apply Units.ext
  exact hm

variable {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem lam_iff (q : {Λ // Λ ∈ what₂}) (y : (VS D).V) :
    y ∈ q.1 ↔ X.B.I.fmat (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)⁻¹) *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  have := cs.lat_eq (cs.base q.1) y
  rwa [cs.base_lam q.1 q.2] at this

theorem lam_latOf (q : {Λ // Λ ∈ what₂}) : ((q.1 : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) =
    latOf X u (cs.h (cs.base q.1)) := by
  ext y
  first
    | exact lam_iff cs q y
    | (rw [SetLike.mem_coe, lam_iff cs q y]; rfl)
    | simp [latOf, lam_iff cs q y]

theorem isoG_lat (q : {Λ // Λ ∈ what₂}) (g : GamL cs q) : Formalism.HermitianLatticesTheory.gmap (isoG g.1) q.1 = q.1 := by
  set hb := cs.h (cs.base q.1)
  have hκ := g.2
  set κ := colD hb (iotaF X u g.1 * hb) with hκdef
  have hcomm : ((hb : X.B.I.Gf) * X.xu u)⁻¹ * (g.1 : X.B.I.GA).2 = κ * ((hb : X.B.I.Gf) * X.xu u)⁻¹ := by
    rw [hκdef]; unfold colD
    show _ = (((hb : X.B.I.Gf) * X.xu u)⁻¹ * (((iotaF X u g.1 : Hfin X u) : X.B.I.Gf) * hb * X.xu u)) * _
    show _ = (((hb : X.B.I.Gf) * X.xu u)⁻¹ * ((g.1 : X.B.I.GA).2 * hb * X.xu u)) * _
    group
  have key : ∀ y, isoG g.1 y ∈ q.1 ↔ y ∈ q.1 := by
    intro y
    rw [lam_iff, lam_iff, isoG_spec, mulVec_mulVec]
    have e : X.B.I.fmat (((hb : X.B.I.Gf) * X.xu u)⁻¹) * X.B.I.fmat (g.1 : X.B.I.GA).2 =
        X.B.I.fmat κ * X.B.I.fmat (((hb : X.B.I.Gf) * X.xu u)⁻¹) := by
      rw [← fmatK_mul, ← fmatK_mul, hcomm]
    rw [e, ← mulVec_mulVec]
    have := kset_iff X (K_inv X.B.I hκ) (X.B.I.fmat (((hb : X.B.I.Gf) * X.xu u)⁻¹) *ᵥ incl X.B.I (X.crd y))
    rwa [inv_inv] at this
  ext x
  rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
  constructor
  · intro h; have := (key _).2 h; rwa [LinearEquiv.apply_symm_apply] at this
  · intro h; exact (key _).1 (by rwa [LinearEquiv.apply_symm_apply])

def gamL_autLz (q : {Λ // Λ ∈ what₂}) (g : GamL cs q) : autLz D (X.Fu u) q.1 :=
  ⟨indW (isoG g.1) (isoG_stab g.1), indW_mem q.1 _ _ (isoG_lat cs q g)⟩

theorem gamL_autLz_bij (hK : X.LevelSubgroupCharacter) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK) (q : {Λ // Λ ∈ what₂}) :
    Function.Bijective (gamL_autLz cs q) := by
  have hXs : (X.Fu u).X = Xs X := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e u]; rfl
  constructor
  · rintro ⟨g1, hg1⟩ ⟨g2, hg2⟩ heq
    have hf : (indW (isoG g1) (isoG_stab g1) : WbQ D (X.Fu u) → WbQ D (X.Fu u)) =
        indW (isoG g2) (isoG_stab g2) := congrArg Subtype.val heq
    have hi := eq_of_indW (isoG_stab g1) (isoG_stab g2) (isoG_e g1) (isoG_e g2) (isoG_f g1) (isoG_f g2)
      (LinearMap.coe_injective hf)
    have h2 : (g1 : X.B.I.GA).2 = (g2 : X.B.I.GA).2 := gf_eq fun y => by
      rw [← isoG_spec, ← isoG_spec, hi]
    have h0 : g1⁻¹ * g2 = 1 := by
      refine hN 1 (g1⁻¹ * g2) ?_
      have e : (1 : Hfin X u)⁻¹ * iotaF X u (g1⁻¹ * g2) * 1 = 1 := by
        have : iotaF X u g1 = iotaF X u g2 := Subtype.ext h2
        simp only [inv_one, one_mul, mul_one, map_mul, map_inv, this, inv_mul_cancel]
      rw [e]; exact (Ku X u hK).one_mem
    rw [inv_mul_eq_one] at h0
    subst h0
    rfl
  · rintro ⟨φ, γ0, hγ0, hγ0Λ, hφ⟩
    set hb := cs.h (cs.base q.1) with hhb
    have hγ0' := stab_symm X u hγ0
    have h1 : gW X γ0 ∘ₗ gW X γ0.symm = LinearMap.id :=
      LinearMap.ext fun y => gW_gW X u hγ0 hγ0' (fun w => γ0.apply_symm_apply w) y
    have h2 : gW X γ0.symm ∘ₗ gW X γ0 = LinearMap.id :=
      LinearMap.ext fun y => gW_gW X u hγ0' hγ0 (fun w => γ0.symm_apply_apply w) y
    have hM := ratGL_UJ X (gW X γ0) (gW X γ0.symm) h1 h2 (gW_isom X u hγ0)
    have hfix : ∀ y ∈ fixSet X u, ((ratGL X (gW X γ0) (gW X γ0.symm) h1 h2 : GL (Fin X.B.I.n) X.B.I.E) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y := by
      rintro y ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hy)
      · show ratMat X (gW X γ0) *ᵥ X.crd (X.eX a) = X.crd (X.eX a)
        rw [ratMat_crd, gW_e]
      · show ratMat X (gW X γ0) *ᵥ X.crd (X.fY a) = X.crd (X.fY a)
        rw [ratMat_crd, gW_f]
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show ratMat X (gW X γ0) *ᵥ X.crd (X.zu u) = X.crd (X.zu u)
        rw [ratMat_crd, stabilizer_fix_anisotropic X u hγ0]
    set c := ratGam X u _ hM hfix with hc
    have hspec : ∀ y, X.B.I.fmat (rfinU X _ hM) *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd (gW X γ0 y)) := by
      intro y
      rw [fmat_rfinU]
      have h4 : incl X.B.I (ratMat X (gW X γ0) *ᵥ X.crd y) =
          (ratMat X (gW X γ0)).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd y) := by
        funext i
        exact RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (ratMat X (gW X γ0)) (X.crd y) i
      show (ratMat X (gW X γ0)).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd y) = _
      rw [← h4, ratMat_crd]
    have e2 : ∀ y, X.B.I.fmat (rfinU X _ hM)⁻¹ *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd (gW X γ0.symm y)) := by
      intro y
      have h3 := hspec (gW X γ0.symm y)
      rw [gW_gW X u hγ0 hγ0' (fun w => γ0.apply_symm_apply w) y] at h3
      rw [← h3, mulVec_mulVec, unitaryCongruence.fmat_inv_mul X.B.I, one_mulVec]
    have hlat := lam_latOf cs q
    have hmap : ∀ y ∈ latOf X u hb, γ0 y ∈ latOf X u hb := by
      intro y hy
      rw [← hlat] at hy ⊢
      rw [← hγ0Λ]
      exact (gmap_apply_mem γ0 _ y).2 hy
    have hmap' : ∀ y ∈ latOf X u hb, γ0.symm y ∈ latOf X u hb := by
      intro y hy
      rw [← hlat] at hy ⊢
      have : y ∈ Formalism.HermitianLatticesTheory.gmap γ0 q.1 := by rw [hγ0Λ]; exact hy
      rwa [Formalism.L2.SG.Saturated.mem_gmap_iff] at this
    have hgW : ∀ y, gW X γ0.symm y ∈ q.1 ↔ y ∈ q.1 := by
      intro y
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, hlat]
      constructor
      · intro hy
        have := gW_mem X u hb hb hmap hy
        rwa [gW_gW X u hγ0 hγ0' (fun w => γ0.apply_symm_apply w) y] at this
      · intro hy; exact gW_mem X u hb hb hmap' hy
    have hK0 : colD hb (iotaF X u c * hb) ∈ X.B.I.Kset := by
      have hd := dict_K X ((hb : X.B.I.Gf) * X.xu u) (((iotaF X u c * hb : Hfin X u) : X.B.I.Gf) * X.xu u)
        (q.1 : Set (VS D).V) (fun y => lam_iff cs q y) (fun y => by
          have e : (((iotaF X u c * hb : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ =
              ((hb : X.B.I.Gf) * X.xu u)⁻¹ * (rfinU X _ hM)⁻¹ := by
            rw [Subgroup.coe_mul, hc, iotaF_ratGam]; group
          show y ∈ q.1 ↔ _
          rw [e, fmatK_mul, ← mulVec_mulVec, e2, ← lam_iff cs q]
          exact (hgW y).symm)
      exact hd
    refine ⟨⟨c, hK0⟩, Subtype.ext ?_⟩
    have hiso : ∀ y, isoG c y = gW X γ0 y := fun y => by
      apply inclCrd_inj
      rw [isoG_spec]
      exact hspec y
    funext w
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      show indW (isoG c) (isoG_stab c) (Submodule.Quotient.mk x) = φ (Submodule.Quotient.mk x)
      rw [indW_mk, hφ x (stab_perpS hγ0 x.2), Submodule.Quotient.eq]
      show isoG c x.1 - γ0 x.1 ∈ (X.Fu u).X
      rw [hiso]
      refine hXs.ge ?_
      rw [gW_apply]
      have hx : ∀ a, (VS D).hT (X.eX a) x.1 = 0 := fun a =>
        x.2 _ (by rw [hXs]; exact eX_mem_Xs X a)
      have hA := sub_prV_mem_Xs X hx
      have hB := stab_Xs X u hγ0 hA
      have hC := stab_perp X u hγ0 x.1
      have e : x.1 - prV X x.1 + prV X (γ0 (prV X x.1)) - γ0 x.1 =
          (x.1 - prV X x.1) - γ0 (x.1 - prV X x.1) - (γ0 (prV X x.1) - prV X (γ0 (prV X x.1))) := by
        rw [map_sub]; abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ hA hB) hC

theorem card_autLz_eq (TR : TypedRed X) (hK : X.LevelSubgroupCharacter) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK)
    (q : {Λ // Λ ∈ what₂}) : Nat.card (autLz D (X.Fu u) q.1) = Nat.card (Aset TR cs q) := (Nat.card_congr (Equiv.ofBijective _ (gamL_autLz_bij cs hK hN q))).symm.trans
    (Nat.card_congr (Equiv.ofBijective _ (gamL_levi_bij cs TR hK hN q)))

theorem massA_of (TR : TypedRed X) (hK : X.LevelSubgroupCharacter) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK) :
    MassA TR (X.Fu u) cs := by
  intro q
  rw [← card_autLz_eq cs TR hK hN q]
  first
    | rfl
    | simp [wRow]
    | simp [Formalism.L2.SG.NormCut.wRow]

end Mass2

end Formalism.L2.SG.Pf.Act

namespace Formalism.L2.SG.Pf

theorem massAC_of (hN : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : Formalism.L2.SG.NormCut.MassAC := fun D X Y u => Formalism.L2.SG.Pf.Act.massA_of (Y.cs u) Y.TR Y.hK (hN D X Y u)

end Formalism.L2.SG.Pf
