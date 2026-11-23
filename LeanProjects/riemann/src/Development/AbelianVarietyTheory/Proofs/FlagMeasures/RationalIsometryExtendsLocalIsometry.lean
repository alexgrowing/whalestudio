import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocExt

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem isUnitary_of_span (H : HermSp M V) (g : V ≃ₗ[E] V) {S : Set V} (hS : Submodule.span E S = ⊤)
    (h : ∀ x ∈ S, ∀ y ∈ S, H.h (g x) (g y) = H.h x y) : IsUnitary H g := by
  have h1 : ∀ x, ∀ y ∈ S, H.h (g x) (g y) = H.h x y := by
    intro x y hy
    have hx : x ∈ Submodule.span E S := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx y hy
    | zero => rw [map_zero, H.h_zero_left, H.h_zero_left]
    | add x x' _ _ ih ih' => rw [map_add, H.h_add_left, H.h_add_left, ih, ih']
    | smul a x _ ih => rw [map_smul, H.h_smul_left, H.h_smul_left, ih]
  have h2 : ∀ y x, H.h (g y) (g x) = H.h y x := by
    intro y x
    have hy : y ∈ Submodule.span E S := hS ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => rw [H.h_herm, h1 x y hy, ← H.h_herm]
    | zero => rw [map_zero, H.h_zero_left, H.h_zero_left]
    | add y y' _ _ ih ih' => rw [map_add, H.h_add_left, H.h_add_left, ih, ih']
    | smul a y _ ih => rw [map_smul, H.h_smul_left, H.h_smul_left, ih]
  exact fun x y => h2 x y

end Gen

variable {D : D7}

theorem baseChange_mem_span (p : PlF D) {s : Set (VS D).V} {x : (VS D).V} (hx : x ∈ Submodule.span D.host.E s) :
    baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' s) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ ih

theorem ext_bcP (p : PlF D) {f g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p} (h : ∀ x, f (baseChange₂ D p x) = g (baseChange₂ D p x)) :
    f = g :=
  LinearMap.ext_on (span_baseChange_eq_top p) (by rintro _ ⟨x, rfl⟩; exact h x)

def locEnd (p : PlF D) (φ : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  Matrix.toLin' ((LinearMap.toMatrix (VS D).frame (VS D).frame φ).map (D.s.atP p).ιE)

theorem locEnd_bcP (p : PlF D) (φ : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    locEnd p φ (baseChange₂ D p x) = baseChange₂ D p (φ x) := by
  funext i
  have e := congrFun (LinearMap.toMatrix_mulVec_repr (VS D).frame (VS D).frame φ x) i
  simp only [locEnd, Matrix.toLin'_apply, baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

def locEquiv (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p :=
  LinearEquiv.ofLinearMap (locEnd p γ) (locEnd p γ.symm)
    (ext_bcP p fun x => by simp [locEnd_bcP])
    (ext_bcP p fun x => by simp [locEnd_bcP])

theorem locEquiv_ext (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Ext p γ (locEquiv p γ) := by
  intro x
  show locEnd p γ (baseChange₂ D p x) = _
  rw [locEnd_bcP]; rfl

theorem exists_dual {r : ℕ} (e : Fin r → (VS D).V) (he : LinearIndependent D.host.E e) :
    ∃ es : Fin r → (VS D).V, ∀ a b, (VS D).hT (e a) (es b) = if a = b then 1 else 0 := by
  let φ : (VS D).V →ₗ[D.host.E] (Fin r → D.host.E) := LinearMap.pi fun a => (VS D).hT (e a)
  have hsurj : LinearMap.range φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    set c : Fin r → D.host.E := fun a => f (fun j => if a = j then 1 else 0) with hc
    have hw : ∀ y, (VS D).hT (∑ a, star (c a) • e a) y = 0 := by
      intro y
      have h0 : f (φ y) = 0 := hle ⟨y, rfl⟩
      rw [LinearMap.pi_apply_eq_sum_univ] at h0
      rw [map_sum, LinearMap.sum_apply]
      rw [← h0]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    have h0 : ∑ a, star (c a) • e a = 0 := (VS D).nondeg.1 _ hw
    have hc0 : ∀ a, c a = 0 := fun a => by
      have := Fintype.linearIndependent_iff.1 he _ h0 a
      simpa using this
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    have := hc0 a
    simp only [hc] at this
    rw [this, smul_zero]
  have hex : ∀ b, ∃ y, φ y = Pi.single b 1 := fun b => by
    have : Pi.single b 1 ∈ LinearMap.range φ := hsurj ▸ Submodule.mem_top
    exact this
  choose es hes using hex
  refine ⟨es, fun a b => ?_⟩
  have := congrFun (hes b) a
  simp only [φ, LinearMap.pi_apply, Pi.single_apply] at this
  exact this

end GlobalTheory.LocExt

namespace GlobalTheory.LocExt

variable {D : D7}

theorem locEquiv_unitary (Z : LocDat D) (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) : Formalism.MainNotions.S.LocNG.IsUnitary (locH Z p) (locEquiv p γ) := by
  refine isUnitary_of_span (locH Z p) (locEquiv p γ) (span_baseChange_eq_top p) ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hx := locEquiv_ext p γ x
  have hy := locEquiv_ext p γ y
  show LocFacts₂ Z.M p _ _ = LocFacts₂ Z.M p _ _
  rw [hx, hy, baseChangeAt_form Z.M p (Z.hcj p), baseChangeAt_form Z.M p (Z.hcj p)]
  simp only [brS]
  rw [hγ y x]

theorem locEquiv_unique (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (h : Ext p γ g') : g' = locEquiv p γ := by
  apply LinearEquiv.toLinearMap_injective
  exact ext_bcP p fun x => by
    show g' (baseChange₂ D p x) = locEquiv p γ (baseChange₂ D p x)
    rw [h x, locEquiv_ext p γ x]

theorem locEquiv_img (Z : LocDat D) (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.MainNotions.S.LocNG.img (M := Z.M p) (locEquiv p γ) (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  unfold Formalism.MainNotions.S.LocNG.img lattice₂ Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_span]
  congr 1
  rw [Submodule.map_coe, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  exact locEquiv_ext p γ x

end GlobalTheory.LocExt

namespace GlobalTheory.LocExt

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (a : Fin D.R.rS) :
    frame F a.castSucc = F.fl.e a := by
  simp [frame, FlagG.fvec]

theorem baseChange_flagVector_mem_span (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (S : Set (Fin D.R.rS))
    (b : Fin D.R.rS) (hb : b ∈ S) :
    baseChange₂ D p (F.fl.e b) ∈ Submodule.span (D.s.atP p).Ep ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' S) := by
  obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p b.castSucc
  have e : baseChange₂ D p (F.fl.e b) = ((u⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) • scaled Z p (frame F) b.castSucc := by
    simp only [scaled, frame_castSucc, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem bcP_Xsp_mem (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {x : (VS D).V}
    (hx : x ∈ Xsp F) : baseChange₂ D p x ∈ (locH Z p).X (scaled Z p (frame F)) := by
  have h := baseChange_mem_span p (s := Set.range F.fl.e) hx
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  have := baseChange_flagVector_mem_span Z p F Set.univ b (Set.mem_univ b)
  rw [Set.image_univ] at this
  exact this

theorem perp_le (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {v : Vp D p}
    (hv : v ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F)))) :
    v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) (Xsp F) : Set (VS D).V)) := by
  obtain ⟨es, hes⟩ := exists_dual F.fl.e F.fl.e_indep
  have key : ∀ v : Vp D p, v - ∑ a, (locH Z p).h v (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a) ∈
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) (Xsp F) : Set (VS D).V)) := by
    intro v
    have hv : v ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := (span_baseChange_eq_top p) ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      set w : (VS D).V := x - ∑ a, (VS D).hT (F.fl.e a) x • es a with hw
      have hwo : w ∈ orth (VS D) (Xsp F) := by
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨c, rfl⟩ := hy
          simp [hw, map_sub, map_sum, map_smul, hes, Finset.sum_ite_eq]
        | zero => simp
        | add y y' _ _ ih ih' => simp [map_add, ih, ih']
        | smul a y _ ih => simp [map_smulₛₗ, ih]
      have e : baseChange₂ D p x - ∑ a, (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a) = baseChange₂ D p w := by
        show baseChange₂ D p x - ∑ a, LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a) = _
        simp only [baseChangeAt_form Z.M p (Z.hcj p), brS, hw, map_sub, map_sum, baseChange_smul₂]
      rw [e]
      exact Submodule.subset_span ⟨w, hwo, rfl⟩
    | zero =>
      simp only [(locH Z p).h_zero_left, zero_smul, Finset.sum_const_zero, sub_zero]
      exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
      have e : x + y - ∑ a, (locH Z p).h (x + y) (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a) =
          (x - ∑ a, (locH Z p).h x (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a)) +
          (y - ∑ a, (locH Z p).h y (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a)) := by
        simp only [(locH Z p).h_add_left, add_smul, Finset.sum_add_distrib]
        abel
      rw [e]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
      have e : c • x - ∑ a, (locH Z p).h (c • x) (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a) =
          c • (x - ∑ a, (locH Z p).h x (baseChange₂ D p (F.fl.e a)) • baseChange₂ D p (es a)) := by
        simp only [(locH Z p).h_smul_left, mul_smul, ← Finset.smul_sum, smul_sub]
      rw [e]; exact Submodule.smul_mem _ _ ih
  have h0 : ∀ a, (locH Z p).h v (baseChange₂ D p (F.fl.e a)) = 0 := fun a =>
    hv _ (bcP_Xsp_mem Z p F (Submodule.subset_span ⟨a, rfl⟩))
  have := key v
  simpa [h0] using this

theorem locEquiv_NU (Z : LocDat D) (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (hN : γ ∈ Formalism.L2.SG.NGData.NRat F) :
    locEquiv p γ ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  obtain ⟨hiso, hfl, hperp⟩ := hN
  have hg : ∀ x, locEquiv p γ (baseChange₂ D p x) = baseChange₂ D p (γ x) := locEquiv_ext p γ
  refine ⟨locEquiv_unitary Z p γ hiso, ?_, ?_⟩
  · intro a
    have hmem : F.fl.e a ∈ Xflag F (a.val + 1) :=
      Submodule.subset_span ⟨a, by simp, rfl⟩
    have h1 := hfl a.val (F.fl.e a) hmem
    have h2 := baseChange_mem_span p h1
    have e : locEquiv p γ (scaled Z p (frame F) a.castSucc) - scaled Z p (frame F) a.castSucc =
        frFac Z.δ p a.castSucc • baseChange₂ D p (γ (F.fl.e a) - F.fl.e a) := by
      simp only [scaled, frame_castSucc, map_smul, hg, map_sub, smul_sub]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.span_le.2 ?_ h2)
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact baseChange_flagVector_mem_span Z p F {b | b < a} b (show b < a from hb)
  · intro v hv
    have hv' := perp_le Z p F hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, hw, rfl⟩ := hv
      rw [hg, ← map_sub]
      exact bcP_Xsp_mem Z p F (hperp w hw)
    | zero => simp
    | add x y _ _ ihx ihy =>
      have e : locEquiv p γ (x + y) - (x + y) = (locEquiv p γ x - x) + (locEquiv p γ y - y) := by
        rw [map_add]; abel
      rw [e]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
      rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ ih

end GlobalTheory.LocExt

namespace GlobalTheory.LocExt

theorem ext_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (p : PlF D), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃ g, Ext p γ g ∧ LocNG.IsUnitary (locH Z p) g ∧ (∀ g', Ext p γ g' → g' = g) ∧ (∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap γ Λ)) ∧ ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), γ ∈ Formalism.L2.SG.NGData.NRat F → g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  intro D Z p γ hγ
  exact ⟨locEquiv p γ, locEquiv_ext p γ, locEquiv_unitary Z p γ hγ, fun g' h => locEquiv_unique p γ g' h,
    fun Λ => locEquiv_img Z p γ Λ, fun F hN => locEquiv_NU Z p γ F hN⟩

end GlobalTheory.LocExt
