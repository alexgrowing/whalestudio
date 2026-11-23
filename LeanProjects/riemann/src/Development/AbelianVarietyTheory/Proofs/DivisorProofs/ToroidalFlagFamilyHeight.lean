import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfInvertibleMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixStepIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixTransportFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleRankDualStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.Lift

theorem isUnit_det_lieMat (dual : Bool) {r : ℕ} {K : Type} [CommRing K] {d : Matrix (Fin r) (Fin r) K}
    (hd : IsUnit d.det) : IsUnit (lieMat dual d).det := by
  cases dual
  · exact hd
  · show IsUnit ((Matrix.transpose d⁻¹).submatrix Fin.revPerm id).det
    rw [Matrix.det_permute, Matrix.det_transpose]
    refine IsUnit.mul ?_ (Matrix.isUnit_nonsing_inv_det d hd)
    exact (Units.isUnit (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)))).map (Int.castRingHom K)

theorem exists_coord {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] {χ : c.F →+* K}
    {x : Sp K ⟶ Z.X} (g : EigFrame Z χ x) {τ : E →+* ℂ} {r : ℕ} (hr : r = Dw.mult τ)
    {u : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : ArLieBase.IsEigBasis Z χ x τ u) :
    ∃ d : Matrix (Fin r) (Fin r) K, IsUnit d.det ∧ ∀ i, IsCombAtG Z.t x u (d i) (g.v τ (Fin.cast hr i)) := by
  subst hr
  choose d hd using fun i => (hu.2 (g.v τ i) ⟨g.tan τ i, g.eig τ i⟩).exists
  choose d' hd' using fun i => (g.basis τ (u i) (hu.1 i).1 (hu.1 i).2).exists
  refine ⟨Matrix.of d, ?_, hd⟩
  refine Matrix.isUnit_det_of_left_inverse (B := Matrix.of d') (Matrix.ext fun i j => ?_)
  have h1 := isCombAtG_mul Z.t x (fun a => (hu.1 a).1) (g.tan τ) (hu.1 i).1 (Matrix.of fun a k => d k a) (d' i) hd (hd' i)
  have h2 := congrFun ((hu.2 _ (hu.1 i)).unique h1 (isCombAtG_single Z.t x (fun a => (hu.1 a).1) i)) j
  rw [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply] at *
  simp only [Matrix.of_apply] at h2 ⊢
  simp only [mul_comm (d' i _), h2, eq_comm]

theorem existsUnique_bears : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (ι : Type) (rk : ι → ℕ) (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a)) (Bs Bg Y : Scheme.{0}) (M : ι → Bs.Modules) (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)), (∀ a, IsLieFrames Z e jB πB (M a) (rk a) (emb a) (dual a) (u a)) → IsFlagBundle π M rk fl → ∀ (K : Type) [Field K] (xb : Sp K ⟶ Bg) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x), x = xb ≫ πB ≫ genι Z → xb ≫ πB ≫ genStr Z = spMap χ → ∃! y : Sp K ⟶ Y, Bears Z emb dual hr hM jB πB u π fl y xb g := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e ι rk emb dual hr Bs Bg Y M hM jB πB u π fl hL hfl K _ xb χ x g hx hχ
  subst hx
  choose V f hV hf using fun a => hM a ((xb ≫ jB) default)
  have hxV : ∀ a, ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V a := fun a p _ => by
    rw [Subsingleton.elim p default]; exact hV a
  have hψ : xb ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (χ.comp e.toRingHom) := by
    rw [← Category.assoc πB, ← Category.assoc xb, hχ, ← Spec.map_comp]; rfl
  have hχ' : (χ.comp e.toRingHom).comp e.symm.toRingHom = χ := RingHom.ext fun a => by simp
  have hb := fun a => (hL a).1 (V a) (f a) (hf a) K xb (hxV a) _ hψ
  rw [hχ'] at hb
  choose d hd hc using fun a => exists_coord Z g (hr a) (hb a)
  choose fl' hfl' using fun a => GlobalTheory.T.exists_flag_of_invertible_matrix Bs (M a) (rk a) (hM a) (V a) (f a) (hf a) K (xb ≫ jB) (hxV a) _
    (isUnit_det_lieMat (dual a) (hd a))
  obtain ⟨y, ⟨w, hy⟩, huq⟩ := hfl (Sp K) (xb ≫ jB) fl'
  refine ⟨y, ⟨w, rfl, hχ, fun a => ?_⟩, fun y' hy' => huq y' ⟨hy'.1, fun a => ?_⟩⟩
  · exact GlobalTheory.T.toroidal_flag_bundle_rank_dual E H Dw l Xo c Oz β Z F e (rk a) (emb a) (dual a) Bs Bg Y (M a) (hM a) jB πB (u a) π (fl a) (hL a)
      K y xb χ w hχ _ (V a) (f a) (hf a) (hxV a) (d a) (hd a) (hc a)
      (GlobalTheory.T.flag_matrix_step_isomorphism Bs Y (M a) (rk a) (hM a) π (fl a) (V a) (f a) (hf a) K (xb ≫ jB) (hxV a) (fl' a) _ (hfl' a) y w
        (hy a))
  · exact GlobalTheory.T.flag_matrix_transport_fibre Bs Y (M a) (rk a) (hM a) π (fl a) (V a) (f a) (hf a) K (xb ≫ jB) (hxV a) (fl' a) _ (hfl' a) y'
      hy'.1 (hy'.2.2.2 a (V a) (f a) (hf a) (hxV a) (d a) (hc a))

end GlobalTheory.FlagCls.Lift

end
