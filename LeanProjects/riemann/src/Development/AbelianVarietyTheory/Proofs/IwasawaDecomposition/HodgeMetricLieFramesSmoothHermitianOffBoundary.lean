import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInteriorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricGramSmoothInFamilyFramesStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

open scoped ComplexOrder
open Matrix GlobalTheory GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.GoodMetric GlobalTheory.ProjVar.Var GlobalTheory.TrueGeo.Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ} {e : F ≃+* c.F} {X : Var F} {j : X.X ⟶ gen Z}
  {f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)} {S : Fr (ratOf X) Dw.mult 0} {A₀ : Mat Dw.mult X.Fn}

theorem spMap_evStalk_eq (y : CxPts X.str (σ.comp e.toRingHom)) : y.1 = spMap (evStalk y) ≫ stalkPt X (under y) :=
  (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm

theorem exists_frameAt (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (y : CxPts X.str (σ.comp e.toRingHom)) {A : Mat Dw.mult X.Fn} (hA : A ∈ S.S (under y)) :
    ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g := by
  obtain ⟨φ, fz, hc⟩ := hT.2 (under y) A hA
  have hφ : σ = (evStalk y).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under y)).commutes _).symm)
    show σ a = evStalk y (φ a)
    rw [h3]
    refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
    simp
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [spMap_evStalk_eq y]
    exact Category.assoc _ _ _
  obtain ⟨g, hg⟩ := fz.exists_isMap (evStalk y) hφ hx
  exact ⟨g, φ, fz, evStalk y, spMap_evStalk_eq y, hc, hg⟩

theorem map_ratVal_eq_co (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    {y : CxPts X.str (σ.comp e.toRingHom)} {A A' : Mat Dw.mult X.Fn} (hA' : A' ∈ S.S (under y)) {g g' : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z)} (hg : FrameAt e f₀ A₀ A y g)
    (hg' : FrameAt e f₀ A₀ A' y g') (τ : E →+* ℂ) : (A' * A⁻¹).map (ratVal · y) τ = (g.co g' τ)ᵀ := by
  obtain ⟨φ, fz, ψ, hψ, hc, hm⟩ := hg
  obtain ⟨φ', fz', ψ', hψ', hc', hm'⟩ := hg'
  obtain rfl : ψ = evStalk y :=
    EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hψ.symm.trans (spMap_evStalk_eq y)))
  obtain rfl : ψ' = evStalk y :=
    EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hψ'.symm.trans (spMap_evStalk_eq y)))
  obtain rfl : φ' = φ := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
    ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [spMap_evStalk_eq y]
    exact Category.assoc _ _ _
  obtain ⟨k, hk⟩ := fz.exists_isMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) hc.2.1 hc.1
  obtain ⟨k', hk'⟩ := fz'.exists_isMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) hc.2.1 hc.1
  have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc.2.2 τ i
  have h2 : k'.co f₀ τ = ((A₀ * A'⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk' τ)]; exact hc'.2.2 τ i
  have h3 : k.co k' τ = (fz.co fz' τ).map (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) :=
    hk.co τ hk' hc.1
  have h4 := k.co_mul k' f₀ τ
  rw [h1, h2, h3] at h4
  set M := (fz.co fz' τ).map (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) with hM
  have u0 : IsUnit (A₀ τ).det := isUnit_iff_ne_zero.2 (Fr.det_ne hT.1 τ)
  have u' : IsUnit (A' τ).det := isUnit_iff_ne_zero.2 (Fr.det_ne hA' τ)
  have h5 : A' τ * (A τ)⁻¹ = Mᵀ := by
    have h6 := congrArg Matrix.transpose h4
    rw [transpose_mul, transpose_transpose, transpose_transpose] at h6
    change A₀ τ * (A' τ)⁻¹ * Mᵀ = A₀ τ * (A τ)⁻¹ at h6
    have h7 : A' τ * (A₀ τ)⁻¹ * (A₀ τ * (A' τ)⁻¹) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A₀ τ)⁻¹, Matrix.nonsing_inv_mul _ u0, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ u']
    calc A' τ * (A τ)⁻¹ = A' τ * (A₀ τ)⁻¹ * (A₀ τ * (A τ)⁻¹) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A₀ τ)⁻¹, Matrix.nonsing_inv_mul _ u0, Matrix.one_mul]
      _ = Mᵀ := by rw [← h6, ← Matrix.mul_assoc, h7, Matrix.one_mul]
  rw [hm.co τ hm' hx]
  change ((A' τ * (A τ)⁻¹)).map (ratVal · y) = _
  rw [h5]
  ext a b
  simp only [map_apply, transpose_apply, hM]
  rw [ratVal_eq_valAt y ⟨_, rfl⟩, valAt_algebraMap]
  rfl

theorem isMetricOn_gramOf (G : EigMet Z σ) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (Ω : X.X.Opens) (hs : ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) Ω, ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ)
      (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧
        CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y) :
    IsMetricOn S Ω (gramOf e G hj f₀ A₀) := by
  refine ⟨fun y _ A hA τ => ?_, fun y hy A hA τ a b => hs y hy A hA τ a b, fun y _ A hA A' hA' τ => ?_⟩
  · have h := exists_frameAt hj hT y hA
    rw [gramOf, dif_pos h]
    exact (G.pos _ _ τ).transpose
  · have h := exists_frameAt hj hT y hA
    have h' := exists_frameAt hj hT y hA'
    unfold gramOf
    rw [dif_pos h, dif_pos h']
    rw [G.change _ h.choose h'.choose τ, map_ratVal_eq_co hj hT hA' h.choose_spec h'.choose_spec τ]
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
    congr 2

end GlobalTheory.LieBase

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier

theorem GlobalTheory.LieBase.isMetricOn_lieGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsMetricOn Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL
  have := T.smooth
  obtain ⟨hoi, -, hT⟩ := hL
  rw [lieGram_eq_gramOf]
  exact isMetricOn_gramOf (hodgeMet T.Z U) hj hT _
    (GlobalTheory.T.eigenMetricGram_smooth_in_familyFrames E H Dw l Xo c O β T.Z σ _ (GlobalTheory.T.hodgeMetric_uniformisation_smoothOn_interior E H Dw l Xo c O β T.Z σ U hσ hU) F e X j f₀ Eb A₀ hj hoi hT)
