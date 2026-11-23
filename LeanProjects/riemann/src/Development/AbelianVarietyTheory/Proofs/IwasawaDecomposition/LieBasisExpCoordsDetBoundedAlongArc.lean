import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArcStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPiStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chartLie_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U), ∃ v' : Fin M.n → (epsR (PowerSeries ℂ) ⟶ W.t.G), (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ i) ∧ IsLieBasis v' := by
  intro E _ _ _ H Dw l Xo c σ V Y a χ W M hM
  have cast : ∀ (p q : Sp (PowerSeries ℂ) ⟶ Y.X) (_ : p = q) (n : SABMap W.t Y.t p),
      ∃ n' : SABMap W.t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ (spMap (ev χ M.U hM) ≫ M.hU.fromSpec) (GlobalTheory.FlagMod.spMap_ev χ M.hU hM).symm W.m
  obtain ⟨v', hv', hb, -⟩ := M.lie (PowerSeries ℂ) (ev χ M.U hM) W.t m'
  refine ⟨v', fun j => ?_, hb⟩
  rw [← hm', hv' j]
  have e : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev χ M.U hM) = dualMap (ev χ M.U hM) := by
    ext x <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, dualMap]
  rw [e]

theorem exists_lieComb_matrix : ∀ (R : Type) [CommRing R] [Nontrivial R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n n' : ℕ) (v : Fin n → (epsR R ⟶ G)) (v' : Fin n' → (epsR R ⟶ G)), IsLieBasis v → IsLieBasis v' → ∃ h : n' = n, ∃ A : Matrix (Fin n) (Fin n) R, IsUnit A.det ∧ ∀ i, IsLieComb (A i) v (v' (Fin.cast h.symm i)) := by
  intro R _ _ G _ _ O _ act n n' v v' hv hv'
  let b := GlobalTheory.Serre.Lie.basis act hv
  let b' := GlobalTheory.Serre.Lie.basis act hv'
  have h : n' = n := by simpa using Fintype.card_congr (b'.indexEquiv b)
  subst h
  refine ⟨rfl, (b.toMatrix b').transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose]
    refine IsUnit.of_mul_eq_one (b'.toMatrix b).det ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · have hv_eq : v = fun k => (b k).hom := funext fun k => (GlobalTheory.Serre.Lie.hom_basis (a := act) hv k).symm
    rw [Fin.cast_eq_self, ← GlobalTheory.Serre.Lie.hom_basis (a := act) hv' i, hv_eq, GlobalTheory.Serre.Lie.isLieComb_iff]
    congr 1
    conv_lhs => rw [← b.sum_repr (b' i)]
    rfl

theorem lieCoord_det_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M h1 h2 h3 h4 h5 h6
  obtain ⟨e, v, z, hev, hv, hz⟩ := GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc E H Dw l Xo c σ V Y a χ W g ty Fu Ha
  obtain ⟨v', hv'1, hv'2⟩ := exists_chartLie_along E H Dw l Xo c σ V Y a χ W M h6
  obtain ⟨hn, A, hA, hAc⟩ := exists_lieComb_matrix (PowerSeries ℂ) W.t.G (𝓞 E) W.t.act g M.n v v' hv hv'2
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum E H Dw l Xo c σ V Y a χ W g ty Fu Ha M h6 e v z hn (fun i => v' (Fin.cast hn.symm i)) A
    h1 h2 h3 h4 h5 hev hv hz (fun i => hv'1 _) hAc
  by_cases hex : ∃ w : ℂ, T₀ < w.im ∧ ∀ i k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)
  swap
  · refine ⟨T₀, 1, one_pos, ?_⟩
    intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
    exact (hex ⟨w, hw, fun i k => (hT₀ w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf i).1 k⟩).elim
  obtain ⟨w₀, -, hs⟩ := hex
  obtain ⟨T', C, hC, hb⟩ := GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi g A w₀ hA hs
  have hd : 0 < ‖(Matrix.of z).det‖ := norm_pos_iff.2 hz
  refine ⟨max T₀ T', C * (‖(Matrix.of z).det‖ + ‖(Matrix.of z).det‖⁻¹), by positivity, ?_⟩
  intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
  have hM : (Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j) =
      (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m) * Matrix.of z := by
    ext i j
    rw [Matrix.of_apply, ((hT₀ w (lt_of_le_of_lt (le_max_left _ _) hw) yF e1 e2 hz' x φ hk hg u Wv hf hdf i).2 j),
      Matrix.mul_apply]
    rfl
  rw [hM, Matrix.det_mul, norm_mul]
  obtain ⟨b1, b2⟩ := hb w (lt_of_le_of_lt (le_max_right _ _) hw)
  set d := ‖(Matrix.of z).det‖
  set t := ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖
  constructor
  · rw [mul_inv, ← div_eq_mul_inv]
    calc C⁻¹ / (d + d⁻¹) ≤ C⁻¹ * d := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ d * (d + d⁻¹) := by rw [mul_add, mul_inv_cancel₀ hd.ne']; nlinarith
          nlinarith [inv_pos.2 hC]
      _ ≤ t * d := mul_le_mul_of_nonneg_right b1 hd.le
  · calc t * d ≤ C * d := mul_le_mul_of_nonneg_right b2 hd.le
      _ ≤ C * (d + d⁻¹) := by nlinarith [inv_pos.2 hd]

end GlobalTheory.ArcNormal
