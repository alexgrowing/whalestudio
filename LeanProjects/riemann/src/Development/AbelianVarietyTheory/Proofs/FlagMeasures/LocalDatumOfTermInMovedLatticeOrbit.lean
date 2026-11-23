import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.TermOrbit

section Gen

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {m : ℕ}

def Fl (R : Type) [CommRing R] [Module R V] (f : Fin m → V) (b : Fin m) : Submodule R V :=
  Submodule.span R (f '' {i | (i : ℕ) < (b : ℕ)})

def UT (R : Type) [CommRing R] [Module R V] (φ : V → V) (f g : Fin m → V) : Prop :=
  ∀ b, φ (f b) - g b ∈ Fl R g b

theorem mem_Fl {f : Fin m → V} {a b : Fin m} (h : a < b) : f a ∈ Fl R f b :=
  Submodule.subset_span ⟨a, Fin.lt_def.1 h, rfl⟩

theorem Fl_mono {f : Fin m → V} {a b : Fin m} (h : a ≤ b) : Fl R f a ≤ Fl R f b :=
  Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < a) => lt_of_lt_of_le hi (Fin.le_def.1 h))

theorem map_Fl (φ : V →ₗ[R] V) {f g : Fin m → V} (h : UT R φ f g) (b : Fin m) :
    ∀ x ∈ Fl R f b, φ x ∈ Fl R g b := by
  intro x hx
  have hle : Fl R f b ≤ (Fl R g b).comap φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hab : a < b := Fin.lt_def.2 ha
    show φ (f a) ∈ Fl R g b
    have e : φ (f a) = (φ (f a) - g a) + g a := by abel
    rw [e]
    exact Submodule.add_mem _ (Fl_mono hab.le (h a)) (mem_Fl hab)
  exact hle hx

theorem UT.comp (φ₂ : V ≃ₗ[R] V) {φ₁ : V → V} {f g k : Fin m → V} (h₁ : UT R φ₁ f g) (h₂ : UT R φ₂ g k) :
    UT R (fun x => φ₂ (φ₁ x)) f k := by
  intro b
  have e : φ₂ (φ₁ (f b)) - k b = φ₂ (φ₁ (f b) - g b) + (φ₂ (g b) - k b) := by
    rw [map_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (map_Fl (φ₂ : V →ₗ[R] V) h₂ b _ (h₁ b)) (h₂ b)

theorem UT.trans_id {φ : V → V} {f g k : Fin m → V} (h₁ : UT R φ f g) (h₂ : UT R id g k) : UT R φ f k :=
  UT.comp (LinearEquiv.refl R V) h₁ h₂

def conjH {W : Type} [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) : (V ≃ₗ[R] V) →* (W ≃ₗ[R] W) where
  toFun g := e.symm.trans (g.trans e)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem conjH_apply {W : Type} [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) (g : V ≃ₗ[R] V) (v : V) :
    conjH e g (e v) = e (g v) := by
  simp [conjH]

theorem UT.of_eq {φ : V → V} {f g : Fin m → V} (h : ∀ b, φ (f b) = g b) : UT R φ f g := by
  intro b; rw [h b, sub_self]; exact Submodule.zero_mem _

theorem UT.of_matrix (A : Matrix (Fin m) (Fin m) R) (h0 : ∀ a b, b < a → A a b = 0) (h1 : ∀ a, A a a = 1)
    {φ : V → V} {f g : Fin m → V} (h : ∀ b, φ (f b) = ∑ a, A a b • g a) : UT R φ f g := by
  intro b
  rw [h b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h1 b, one_smul, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun a ha => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with hab | hab
  · exact Submodule.smul_mem _ _ (mem_Fl hab)
  · rw [h0 a b hab, zero_smul]; exact Submodule.zero_mem _

theorem mem_Fl_map {W : Type} [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) {f : Fin m → V} {b : Fin m}
    {x : V} (hx : x ∈ Fl R f b) : e x ∈ Fl R (fun a => e (f a)) b := by
  have h := Submodule.mem_map_of_mem (f := (e : V →ₗ[R] W)) hx
  rw [Fl, Submodule.map_span, ← Set.image_comp] at h
  exact h

end Gen

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : Frames L r k)

theorem ut_of_Nof (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    {n : S.GLV} (hn : n ∈ S.Nof g) : UT E n g g := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hn
  obtain ⟨⟨-, h1⟩, h2⟩ := hn
  intro b
  by_cases hb : (b : ℕ) < r
  · have e : b = (⟨b, hb⟩ : Fin r).castSucc := Fin.ext rfl
    have := (h1 ⟨b, hb⟩).2 (g b) (Submodule.subset_span ⟨b, by simp, rfl⟩)
    exact this
  · have hr : b = Fin.last r := Fin.ext (by have := b.2; simp only [Fin.val_last]; omega)
    subst hr
    refine h2.2 _ ?_
    refine GlobalTheory.FramePsi.hf_span_right L S.Hm _ _ ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [hg, if_neg]
    rintro ⟨-, rfl⟩
    simp at hl

theorem ut_N {n : S.GLV} (hn : n ∈ S.N) : UT E n S.f S.f := ut_of_Nof S S.f _ S.gram hn

theorem ut_N' {n : S.GLV} (hn : n ∈ S.N') : UT E n S.f' S.f' := ut_of_Nof S S.f' _ S.gram' hn

end Loc

section Rat

open Formalism.L2.SG.Pf

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem ut_nlam {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : UT E n (frame F) (frame F) := by
  intro b
  by_cases hb : (b : ℕ) < r
  · have e : b = (⟨b, hb⟩ : Fin r).castSucc := Fin.ext rfl
    rw [e, frame_castSucc_td]
    have h1 := hn.2.1 b (F.fl.e ⟨b, hb⟩) (Submodule.subset_span ⟨⟨b, hb⟩, by simp, rfl⟩)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨a, ha, rfl⟩
    refine Submodule.subset_span ⟨a.castSucc, ?_, frame_castSucc_td F a⟩
    simp only [Set.mem_setOf_eq, Fin.coe_castSucc] at ha ⊢
    exact ha
  · have hr : b = Fin.last r := Fin.ext (by have := b.2; simp only [Fin.val_last]; omega)
    subst hr
    rw [frame_last_td]
    have h1 := hn.2.2 F.fl.z (Formalism.MainNotions.S.Lem.Comparison₂.z_mem_orth F)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨a.castSucc, ?_, frame_castSucc_td F a⟩
    simp

theorem ut_frameAct {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E))
    (h0 : ∀ a b, b < a → ξ a b = 0) (h1 : ∀ a, ξ a a = 1) : UT E id (frameAct f ξ) f :=
  UT.of_matrix (ξ.map fun x : 𝓞 E => (x : E)) (fun a b h => by simp [h0 a b h]) (fun a => by simp [h1 a])
    (fun b => rfl)

end Rat

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Glob

open Formalism.L2.SG.Pf

variable {D : D7}

theorem ut_loc (Z : LocDat D) (p : PlF D) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hext : Ext p γ g) {f f' : Fin (D.R.rS + 1) → (VS D).V}
    (h : UT D.host.E γ f f') :
    UT (D.s.atP p).Ep g (fun a => frFac Z.δ p a • baseChange₂ D p (f a)) (fun a => frFac Z.δ p a • baseChange₂ D p (f' a)) := by
  intro b
  have e1 : g (frFac Z.δ p b • baseChange₂ D p (f b)) - frFac Z.δ p b • baseChange₂ D p (f' b) =
      frFac Z.δ p b • baseChange₂ D p (γ (f b) - f' b) := by
    rw [map_smul, hext, map_sub, smul_sub]
  rw [e1]
  refine Submodule.smul_mem _ _ ?_
  have h2 := GlobalTheory.LocExt.baseChange_mem_span p (h b)
  refine Submodule.span_le.2 ?_ h2
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a
  have e2 : baseChange₂ D p (f' a) = ((u⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) • (frFac Z.δ p a • baseChange₂ D p (f' a)) := by
    rw [← hu, smul_smul, Units.inv_mul, one_smul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem dcrel_of_eqv (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    {P : LFlag (VS D) D.R.rS T' → Prop} {x y : Formalism.L2.SG.TermDef.Carrier P}
    (h : Relation.EqvGen (Formalism.L2.SG.TermDef.Rel Λ F P) x y) : Formalism.L2.SG.TermDef.DCRel Λ F x.1 y.1 := by
  induction h with
  | rel _ _ h => exact h
  | refl => exact Formalism.L2.SG.TermDef.dcrel_refl Λ F _
  | symm _ _ _ ih => exact dcrel_symm Λ F ih
  | trans _ _ _ _ _ ih1 ih2 => exact dcrel_trans Λ F ih1 ih2

theorem ut_moves {T : D.host.E} (F F0 : LFlag (VS D) D.R.rS T) (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hU : IsUpUni U)
    (h : ∀ b, ρ (frame F b) = ∑ a, U a b • frame F0 a) : UT D.host.E ρ (frame F) (frame F0) :=
  UT.of_matrix U (fun a b hab => (hU a b).1 hab) (fun a => (hU a a).2 rfl) h

end Glob

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section LocC

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
  {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem conj_mem_N (c : WCoord P S) {g : V ≃ₗ[E] V} (hg : g ∈ P.A.N) : conjH c.e g ∈ S.N := by
  have hle : P.A.N ≤ S.N.comap (conjH c.e) := by
    unfold LocNG.FrameD.N
    rw [Subgroup.closure_le]
    intro g hg
    exact (GlobalTheory.HL.CoordUnip.mem_NSet S c.e P.A S.f c.h_eq c.f_eq g (conjH c.e g)
      (fun v => conjH_apply _ _ _)).1 hg
  exact hle hg

theorem conj_mem_N' (c : WCoord P S) {g : V ≃ₗ[E] V} (hg : g ∈ P.B.N) : conjH c.e g ∈ S.N' := by
  have hle : P.B.N ≤ S.N'.comap (conjH c.e) := by
    unfold LocNG.FrameD.N
    rw [Subgroup.closure_le]
    intro g hg
    exact (GlobalTheory.HL.CoordUnip.mem_NSet S c.e P.B S.f' c.h_eq c.f'_eq g (conjH c.e g)
      (fun v => conjH_apply _ _ _)).1 hg
  exact hle hg

end LocC

section LocD

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : Frames L r k)

theorem datOf_St {s : S.GLV} (hs : s ∈ S.St) (Λ : Submodule L.O S.V) : S.datOf (s • Λ) = S.datOf Λ := by
  have DO := GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries L r k S
  have hs' := Subgroup.mem_inf.1 hs
  exact Prod.ext (DO.2.2.1 s hs'.1 Λ) (Prod.ext (DO.2.2.2.1 s hs'.2 Λ) (GlobalTheory.FrameAct.graph_smul S s hs Λ))

end LocD

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section LocO

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
  {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem local_orbit (hM : M.OK) (c : WCoord P S) {d d' : LocNG.Datum P} (hdd : LocNG.Datum.Rel d d')
    {t : Term V M r} (ht : LocNG.IsTermOver P d' t) (ψ0 : V ≃ₗ[E] V) (hu : LocNG.IsUnitary H ψ0)
    (hA : UT E ψ0 t.f P.A.f) (hB : UT E ψ0 t.f' P.B.f) (X : Submodule M.L.O S.V)
    (hX : conjH c.e ψ0 • c.lat t.abelian₂ = X) : ∃ h ∈ S.H0, h • c.dat d = S.datOf X := by
  haveI := hM.loc
  haveI := hM.char0
  have ht' := ht
  obtain ⟨-, -, ⟨nA, hnA, hfA, -⟩, ⟨nB, hnB, hfB, -⟩, -⟩ := ht'
  have hφ : ∀ v, conjH c.e ψ0 (c.e v) = c.e (ψ0 v) := conjH_apply _ _
  have hνA := conj_mem_N c hnA
  have hνB := conj_mem_N' c hnB
  have k1 : UT E ((conjH c.e nA).trans (conjH c.e ψ0)) S.f S.f := by
    intro b
    have hb : nA (P.A.f b) = t.f b := (congrFun hfA b).symm
    rw [LinearEquiv.trans_apply, c.f_eq b, conjH_apply, hφ, hb, ← map_sub,
      show S.f = fun a => c.e (P.A.f a) from funext c.f_eq]
    exact mem_Fl_map c.e (hA b)
  have k1' : UT E ((conjH c.e nB).trans (conjH c.e ψ0)) S.f' S.f' := by
    intro b
    have hb : nB (P.B.f b) = t.f' b := (congrFun hfB b).symm
    rw [LinearEquiv.trans_apply, c.f'_eq b, conjH_apply, hφ, hb, ← map_sub,
      show S.f' = fun a => c.e (P.B.f a) from funext c.f'_eq]
    exact mem_Fl_map c.e (hB b)
  have k2 : UT E (conjH c.e nA).symm S.f S.f := ut_N S (S.N.inv_mem hνA)
  have k2' : UT E (conjH c.e nB).symm S.f' S.f' := ut_N' S (S.N'.inv_mem hνB)
  have hf1 : ∀ b : Fin (r + 1), conjH c.e ψ0 (S.f b) - S.f b ∈ S.spanTo S.f b := by
    intro b
    have h := UT.comp _ k2 k1 b
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
    exact h
  have hf2 : ∀ b : Fin (r + 1), conjH c.e ψ0 (S.f' b) - S.f' b ∈ S.spanTo S.f' b := by
    intro b
    have h := UT.comp _ k2' k1' b
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
    exact h
  have hiso : conjH c.e ψ0 ∈ isomG M.L S.Hm := by
    intro x y
    obtain ⟨x, rfl⟩ := c.e.surjective x
    obtain ⟨y, rfl⟩ := c.e.surjective y
    show S.h (conjH c.e ψ0 (c.e x)) (conjH c.e ψ0 (c.e y)) = S.h (c.e x) (c.e y)
    rw [hφ, hφ, c.h_eq, c.h_eq, hu]
  have DO := GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries M.L r k S
  obtain ⟨s, hs, h, hh, hsh⟩ := DO.2.2.2.2 _ hiso hf1 hf2
  have W := GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates M hM H r k P S c
  obtain ⟨h1, hh1, hd⟩ := (W.2.1 d d').1 hdd
  have hterm := (W.1 d' t ht).1
  have hM' := DO.1 _ _ hterm
  refine ⟨h * h1, S.H0.mul_mem hh hh1, ?_⟩
  rw [← hX, hsh, mul_smul s h, datOf_St S hs, DO.2.1 h hh, ← hM', ← hd, mul_smul h h1]

end LocO

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section GlobL

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem lat_move_loc (Z : LocDat D) (p : PlF D) {FP : LocNG.FPair (locH Z p) D.R.rS} {k : ℕ}
    {S : Frames (Z.M p).L D.R.rS k} (cp : WCoord FP S) (ρ n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hn : ∀ x, n x ∈ Λ ↔ x ∈ Λ)
    (gl ρp : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hext : Ext p (ρ * n⁻¹) ρp) :
    conjH cp.e (gl.symm.trans ρp) • cp.lat (LocNG.img (M := Z.M p) gl (lattice₂ D Z.M p Λ)) =
      Submodule.span (Z.M p).L.O ((fun y => cp.e (baseChange₂ D p (ρ y))) '' (Λ : Set (VS D).V)) := by
  have hset : ∀ y, conjH cp.e (gl.symm.trans ρp) (cp.e (gl (baseChange₂ D p y))) = cp.e (baseChange₂ D p (ρ (n⁻¹ y))) := by
    intro y
    rw [conjH_apply, LinearEquiv.trans_apply, gl.symm_apply_apply, hext]
    rfl
  have hL : cp.lat (LocNG.img (M := Z.M p) gl (lattice₂ D Z.M p Λ)) =
      Submodule.span _ ((fun y => cp.e (gl (baseChange₂ D p y))) '' (Λ : Set (VS D).V)) := by
    simp only [WCoord.lat, LocNG.img, lattice₂, Submodule.map_span, Set.image_image]
    rfl
  rw [hL, Submodule.pointwise_smul_def, Submodule.map_span, Set.image_image]
  have hfun : (fun x => (DistribSMul.toLinearMap (Z.M p).L.O S.V (conjH cp.e (gl.symm.trans ρp)))
      (cp.e (gl (baseChange₂ D p x)))) = fun x => cp.e (baseChange₂ D p (ρ (n⁻¹ x))) := funext fun x => hset x
  rw [hfun]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : n⁻¹ x ∈ Λ := (hn (n⁻¹ x)).1 (by rwa [show n (n⁻¹ x) = x from n.apply_symm_apply x])
    exact ⟨n⁻¹ x, hx', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨n y, (hn y).2 hy, ?_⟩
    show cp.e (baseChange₂ D p (ρ (n.symm (n y)))) = _
    rw [n.symm_apply_apply]

end GlobL

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

open Formalism.L2.SG.Pf

set_option maxHeartbeats 1000000 in

theorem datum_in_orbit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (d : LocNG.Datum (FP p)), Over (FP p) d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')) → ∀ δ : G.Dat, δ p = (c.c p).dat d → ∃ h ∈ (G.S p).H0, h • δ p = G.datOf (c.lat ρ t₀.lam) p := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c t₀ ρ U U' hMv p d hOv δ hδ
  obtain ⟨gl, hgl, d', hdd', hTO⟩ := hOv
  have hOK : (Y.M p).OK := (Y.agree p).1
  haveI := hOK.loc
  haveI := hOK.char0
  have hTOc := hTO
  obtain ⟨-, -, ⟨nA, hnA, hfA, -⟩, ⟨nB, hnB, hfB, -⟩, -⟩ := hTO

  have hq : Relation.EqvGen (Formalism.L2.SG.TermDef.Rel t₀.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u'))
      (Quot.out t₀.toTerm.cls) ⟨t₀.frame, t₀.rep.2.2.2.2⟩ := Quot.eqvGen_exact (Quot.out_eq _)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := dcrel_symm _ _ (dcrel_of_eqv _ _ hq)

  have RA : UT D.host.E (ρ * n⁻¹) (frame (lf D (X.Fu u))) (frame F00) :=
    UT.comp ρ (ut_nlam (nlamPf_inv hn)) (ut_moves _ _ ρ U hMv.2.1 hMv.2.2.2.1)
  have hxi := admissibility_witness_unitriangular t₀.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1
  have hxi' := inv_unitri _ hxi.1 hxi.2
  have RB : UT D.host.E (ρ * n⁻¹)
      (frameAct (frame (Quot.out t₀.toTerm.cls).1) (admXi D t₀.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1)⁻¹)
      (frame F'0) := by
    have s1 := ut_frameAct (frame (Quot.out t₀.toTerm.cls).1) _ hxi'.1 hxi'.2
    have s2 : UT D.host.E ⇑(n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (frame (Quot.out t₀.toTerm.cls).1) (fun a => m (frame t₀.frame a)) :=
      UT.of_eq fun b => by
        rw [show frame (Quot.out t₀.toTerm.cls).1 b = n (m (frame t₀.frame b)) from hfr b]; simp
    have s3 : UT D.host.E id (fun a => m (frame t₀.frame a)) (frame t₀.frame) := fun b => ut_nlam hm b
    have s4 := ut_moves _ _ ρ U' hMv.2.2.1 hMv.2.2.2.2
    exact UT.comp ρ (UT.trans_id (UT.comp n⁻¹ s1 s2) s3) s4
  have hγ : ρ * n⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hMv.1 (nlamPf_inv hn).1.1
  obtain ⟨ρp, hρe, hρu, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D ⟨Y.δ, Y.M, Y.agree⟩ p (ρ * n⁻¹) hγ

  have UA : UT (D.s.atP p).Ep ρp
      (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f
      (FP p).A.f := by
    rw [(hAB p).1.1]
    exact ut_loc ⟨Y.δ, Y.M, Y.agree⟩ p hρe RA
  have UB : UT (D.s.atP p).Ep ρp
      (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f'
      (FP p).B.f := by
    rw [(hAB p).1.2.1]
    exact ut_loc ⟨Y.δ, Y.M, Y.agree⟩ p hρe RB
  have hA : UT (D.s.atP p).Ep (gl.symm.trans ρp)
      (move gl (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u)
        (Tu D u'))).f (FP p).A.f := fun b => by
    show ρp (gl.symm (gl _)) - _ ∈ _
    rw [gl.symm_apply_apply]
    exact UA b
  have hB : UT (D.s.atP p).Ep (gl.symm.trans ρp)
      (move gl (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u)
        (Tu D u'))).f' (FP p).B.f := fun b => by
    show ρp (gl.symm (gl _)) - _ ∈ _
    rw [gl.symm_apply_apply]
    exact UB b
  have hu : LocNG.IsUnitary (locH ⟨Y.δ, Y.M, Y.agree⟩ p) (gl.symm.trans ρp) := fun x y => by
    show (locH ⟨Y.δ, Y.M, Y.agree⟩ p).h (ρp (gl.symm x)) (ρp (gl.symm y)) = _
    rw [hρu, ← hgl (gl.symm x) (gl.symm y), gl.apply_symm_apply, gl.apply_symm_apply]

  have hn' : ∀ x, n x ∈ t₀.lam ↔ x ∈ t₀.lam := ((isAutLam_iff _ n).1 hn.1).2
  have hX1 := lat_move_loc ⟨Y.δ, Y.M, Y.agree⟩ p (c.c p) ρ n t₀.toTerm.lam hn' gl ρp hρe
  have hs : ((fun y => (c.c p).e (baseChange₂ D p (ρ y))) '' (t₀.lam : Set (VS D).V)) =
      (placesOf ⟨Y.δ, Y.M, Y.agree⟩).bc p '' ((c.lat ρ t₀.lam : Submodule (𝓞 D.host.E) G.V) : Set G.V) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨c.e (ρ y), ⟨y, hy, rfl⟩, (c.compat p (ρ y)).symm⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, c.compat p (ρ y)⟩
  have hX2 : Submodule.span (Y.M p).L.O ((fun y => (c.c p).e (baseChange₂ D p (ρ y))) '' (t₀.lam : Set (VS D).V)) =
      (placesOf ⟨Y.δ, Y.M, Y.agree⟩).lat p (c.lat ρ t₀.lam) := by
    rw [hs]
    rfl
  rw [hδ]
  exact local_orbit hOK (c.c p) hdd' hTOc (gl.symm.trans ρp) hu hA hB _ (hX1.trans hX2)

end GlobalTheory.HL.TermOrbit
