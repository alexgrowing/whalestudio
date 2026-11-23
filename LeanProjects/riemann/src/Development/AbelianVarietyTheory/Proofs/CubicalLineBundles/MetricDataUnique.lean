import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAppellHumbertUniformisationOfKeyDatumIsoStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaSectionNormAndHermitianFormIndepUniformisatStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.MetUniq

theorem uniq_cast (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g)
    (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ))
    (h : u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume)
    (h' : u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume) :
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal =
      (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧
    ∀ (v w : epsR ℂ ⟶ x.P.A) (V W : Fin g → ℂ) (V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v →
      u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  subst hg
  exact GlobalTheory.T.thetaSection_norm_and_hermitianForm_indep_uniformisation x u Hm χ θ Fd u' Hm' χ' θ' Fd' h h'

theorem spMap_dualMap_id (S : Type) [CommRing S] :
    spMap (Formalism.L2.Pj.dualMap (RingHom.id S)) = 𝟙 (Sp (DualNumber S)) := by
  have : Formalism.L2.Pj.dualMap (RingHom.id S) = RingHom.id _ := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap]
  rw [this]
  exact Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem isMetricAt_unique (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (ht : ∀ τ i, IsTanAt x (uu τ i))
    (N N' : ℝ) (Gr Gr' : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (h : IsMetricAt x s uu N Gr) (h' : IsMetricAt x s uu N' Gr') : N = N' ∧ Gr = Gr' := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, tie, a1, a2, a3, a4, hN, hw, hG⟩ := h
  obtain ⟨Φ', u', Hm', χ', θ', Fd', w', W', tie', b1, b2, b3, b4, hN', hw', hG'⟩ := h'
  have hx : x = spMap (RingHom.id ℂ) ≫ x := by
    have : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
    rw [this, Category.id_comp]
  have sc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x x x hx hx
  have hbc : SecBC (RingHom.id ℂ) 1 x x s s := (sc.2.1 1 s s).2 fun i => by
    rw [(sc.2.2.2 1 1 i).2.2, _root_.one_mul]
  obtain ⟨hg, v', hv', kp, hv⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (RingHom.id ℂ) x x Φ Φ' s s hx tie tie' hbc
  simp only [spMap_dualMap_id, Category.id_comp] at hv
  obtain ⟨u₁, χ₁, θ₁, Fd₁, c1, c2, c3, c4, hN₁, hD⟩ := GlobalTheory.T.exists_appellHumbert_uniformisation_of_keyDatumIso Φ.key _ kp hg _ u Hm χ θ Fd ⟨a1, a2, a3, a4⟩
  have hm : Hm.map (RingHom.id ℂ) = Hm := rfl
  rw [hm] at c1 hN₁
  obtain ⟨e1, e2⟩ := uniq_cast ({ Φ' with v := v', basis := hv' } : FibKey Xo ℂ x).key _ hg u₁ Hm χ₁ θ₁ Fd₁
    u' Hm' χ' θ' Fd' ⟨c1, c2, c3, c4⟩ ⟨b1, b2, b3, b4⟩
  have tan : ∀ b i, IsTangent (G := Φ.T.t.G) (w b i) := fun b i =>
    (Chart.tan_push Φ.m.cart _).2 (((congrArg (_ ≫ ·) (hw b i).1)).trans (ht b i).2)
  have tan' : ∀ b i, IsTangent (G := Φ'.T.t.G) (w' b i) := fun b i =>
    (Chart.tan_push Φ'.m.cart _).2 (((congrArg (_ ≫ ·) (hw' b i).1)).trans (ht b i).2)
  have key : ∀ b i, u₁.IsDiff (W b i) (w' b i) := fun b i => by
    obtain ⟨cf, hcf, -⟩ := Φ.basis.2 (w b i) (tan b i)
    refine hD cf (w b i) (w' b i) (W b i) hcf ?_ (hw b i).2
    obtain ⟨p, hp, hq⟩ := (Chart.comb_push Φ.m.cart _ _ _).1 hcf
    refine (Chart.comb_push Φ'.m.cart _ v' (w' b i)).2 ⟨fun j => p (j.cast hg), fun j => ?_, ?_⟩
    · exact (hp _).trans (congrArg (_ ≫ ·) (hv j).symm)
    · have : List.ofFn (fun j : Fin Φ'.T.g => p (j.cast hg)) = List.ofFn p := (List.ofFn_congr hg.symm p).symm
      exact (congrArg (fun L => (List.prod L).left) this).trans (hq.trans ((hw b i).1.trans (hw' b i).1.symm))
  refine ⟨hN.trans (hN₁.symm.trans (e1.trans hN'.symm)), ?_⟩
  funext b
  ext i k
  rw [hG, hG', e2 (w' b k) (w' b i) _ _ _ _ (tan' b k) (tan' b i) (key b k) (key b i) (hw' b k).2 (hw' b i).2]

theorem isMetric_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N N' : ℝ) (Gr Gr' : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), IsMetric y N Gr → IsMetric y N' Gr' → N = N' ∧ Gr = Gr' :=
  fun _ _ _ _ _ _ _ _ _ _ y N N' Gr Gr' h h' => isMetricAt_unique y.x y.s y.u y.tan N N' Gr Gr' h h'

end GlobalTheory.LamT.MetUniq
