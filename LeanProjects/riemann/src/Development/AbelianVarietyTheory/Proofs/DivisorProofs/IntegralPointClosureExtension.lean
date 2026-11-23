import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.IntPt

theorem top_le_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (t : Sp R ⟶ X) {W : X.Opens}
    (h : t (IsLocalRing.closedPoint R) ∈ W) : ⊤ ≤ t ⁻¹ᵁ W := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map t.continuous).mem_open W.isOpen h

theorem w_eq_one_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O) :
    e.w c = 1 ↔ IsUnit c :=
  ⟨fun h => RegCrit.isUnit_of_one_le e c h.ge, fun h => OfModel.w_unit e h⟩

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_intPt : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (W : V.X.Opens) (x : V.X), x ∈ W → (l : 𝓞 F) ∈ (V.p x).asIdeal → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal ∧ z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) ∧ ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  intro F _ _ Y V l W x hx hl
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, -⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 1 one_ne_zero
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  have hc : yt (IsLocalRing.closedPoint e.O) = hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ := by
    change hU.fromSpec (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O)) = _
    congr 1
    exact PrimeSpectrum.ext h₂
  have hsp : x ⤳ yt (IsLocalRing.closedPoint e.O) := by
    have h0 : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ⤳ hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ :=
      ((PrimeSpectrum.le_iff_specializes _ ⟨𝔪, h𝔪.isPrime⟩).1 hle').map hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf] at h0
    rw [hc]
    exact h0
  have hl' : algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F) ∈ 𝔪 := by
    apply hle'
    have e1 : V.p x = (Spec.map (HorizPt.strHom V.p U)) (hU.primeIdealOf ⟨x, hxU⟩) := by
      rw [← fromSpec_str V.p hU]
      change V.p x = V.p (hU.fromSpec _)
      rw [hU.fromSpec_primeIdealOf]
    rw [e1] at hl
    exact hl
  have hv : (l : 𝓞 F) ∈ v.asIdeal := by
    have hm : φ (algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F)) ∈ IsLocalRing.maximalIdeal e.O := by
      rw [← Ideal.mem_comap, h₂]
      exact hl'
    have hlt : e.w ((φ (algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F)) : e.O) : AlgebraicClosure F) < 1 := by
      refine lt_of_le_of_ne ((e.mem_O _).1 (φ _).2) fun h => ?_
      exact (IsLocalRing.mem_maximalIdeal _).1 hm (RegCrit.isUnit_of_one_le e _ h.ge)
    rw [h₁, e.w_alg] at hlt
    exact (v.adicAbv_coe_lt_one_iff _ _).1 hlt
  refine ⟨v, e, V.pb.lift _ _ hw, yt, hv, V.pb.lift_snd _ _ hw, hy.symm, ?_, hsp, ?_⟩
  · intro p _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro g hg
    obtain ⟨W₀, hW₀, s, hs⟩ := hg.exists_fnOf
    have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := top_le_of_closedPoint yt hW₀
    have hb : below (V.pb.lift _ _ hw ≫ V.j) ∈ W₀ := by
      change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ W₀
      rw [hy]
      exact ht trivial
    have ht' : ⊤ ≤ (V.pb.lift _ _ hw ≫ V.j) ⁻¹ᵁ W₀ := fun p _ => by
      change (V.pb.lift _ _ hw ≫ V.j) p ∈ W₀
      rw [hy]
      exact ht (x := spMap e.O.subtype p) trivial
    have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (V.pb.lift _ _ hw ≫ V.j) yt
      (hy.symm.trans (Category.comp_id _).symm) (U := W₀) (W := W₀) le_rfl ht' ht s
    have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl).hom s = s := by
      have : (𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl = 𝟙 _ :=
        (Category.id_comp _).trans (V.X.presheaf.map_id _)
      rw [this]
      rfl
    rw [hid] at hev
    rw [← hs, OfModel.valAt_fnOf _ hb ht', hev, unitAt_fnOf_iff hW₀, ← RegCrit.isUnit_eval_iff yt ht s]
    exact w_eq_one_iff e _

end GlobalTheory.HtGen.IntPt
