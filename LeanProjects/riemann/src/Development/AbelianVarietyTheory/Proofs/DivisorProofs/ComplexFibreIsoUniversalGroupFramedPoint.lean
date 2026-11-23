import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormEqDot
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
noncomputable section

namespace GlobalTheory.PtDeg

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem fibre_iso_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)), GlobalTheory.IsPolFibre σ F.P₀ Q ψ → (∀ i, GlobalTheory.IsVecOver σ ψ (F.v i) (v' i)) → ∀ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x), ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧ ∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (fun k => σ (v i k)) v' q → ∀ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i → q ≫ f = w' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ v hFC σ φ hφ z hz Q ψ v' hQ hv' T m

  have hφσ : (φ.toRingHom : K →+* ℂ) = σ := RingHom.ext hφ
  have hbase : z.x = spMap σ ≫ y.x := by rw [hz.1, hφσ]; rfl

  have hcomp := hQ.2.1.comp F.fib.2.1
  have w0 : (ψ ≫ F.φ) ≫ B.t.G.hom = (Q.A.hom ≫ spMap σ) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hcomp.1.w, Category.assoc]
  let χ₀ : Q.A.left ⟶ t₀.G.left := m2.cart.1.lift (ψ ≫ F.φ) (Q.A.hom ≫ spMap σ) w0
  have hχ₀2 : χ₀ ≫ m2.φ = ψ ≫ F.φ := m2.cart.1.lift_fst _ _ w0
  have hχ₀b : χ₀ ≫ t₀.G.hom = Q.A.hom ≫ spMap σ := m2.cart.1.lift_snd _ _ w0
  have hχ₀ : IsGrpPullback Q.A t₀.G (spMap σ) χ₀ := m2.cart.cancel (by rw [hχ₀2]; exact hcomp) hχ₀b
  have hχ := hχ₀.comp m1.cart
  have w1 : (χ₀ ≫ m1.φ) ≫ Xo.univ.t.G.hom = Q.A.hom ≫ z.x := by rw [hχ.1.w, hbase]
  let fl : Q.A.left ⟶ T.t.G.left := m.cart.1.lift (χ₀ ≫ m1.φ) Q.A.hom w1
  have hfl : fl ≫ m.φ = χ₀ ≫ m1.φ := m.cart.1.lift_fst _ _ w1
  have hflb : fl ≫ T.t.G.hom = Q.A.hom := m.cart.1.lift_snd _ _ w1
  let f : Q.A ⟶ T.pol.A := Over.homMk fl hflb
  refine ⟨f, ?_, ?_, ?_⟩
  ·
    refine GlobalTheory.DivisibleHom.isMonHom_of_mul_points f fun S x y => ?_
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · have e1 := hχ.2 S x y (pushPt hχ.1.w x) (pushPt hχ.1.w y) rfl rfl
      have e2 := m.cart.2 S (x ≫ f) (y ≫ f) (pushPt m.cart.1.w (x ≫ f)) (pushPt m.cart.1.w (y ≫ f)) rfl rfl
      rw [Over.comp_left, Category.assoc]
      change _ ≫ fl ≫ m.φ = _
      rw [hfl, ← e1, ← e2]
      refine mul_left_congr (by rw [hbase]) _ _ _ _ ?_ ?_
      · show x.left ≫ χ₀ ≫ m1.φ = (x.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
      · show y.left ≫ χ₀ ≫ m1.φ = (y.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
    · exact (Over.w ((x * y) ≫ f)).trans (Over.w ((x ≫ f) * (y ≫ f))).symm
  ·
    obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    obtain ⟨w2', hw2', -⟩ := m2.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso t₀.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have h2 : LBIso t₀.PP.L (B.t.PP.L.pull m2.φ) := ⟨w2', hw2'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm fl
    rw [hfl] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm χ₀
    have h4 := GlobalTheory.CM.EllComp.lbIso_pull_comp h2.symm χ₀
    rw [hχ₀2] at h4
    have h5 : LBIso (B.t.PP.L.pull (ψ ≫ F.φ)) (F.P₀.L.pull ψ) := GlobalTheory.CM.EllComp.lbIso_pull_comp F.fib.2.2 ψ
    have e45 := LBIso.trans (pull_isLB B.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ) Q.isLB h5 hQ.2.2
    have e345 := LBIso.trans (pull_isLB t₀.PP.isLB χ₀) (pull_isLB B.t.PP.isLB _) Q.isLB h4.symm e45
    have e2345 := LBIso.trans (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB t₀.PP.isLB χ₀) Q.isLB h3 e345
    have main : LBIso (T.t.PP.L.pull fl) Q.L :=
      LBIso.trans (pull_isLB T.t.PP.isLB fl) (pull_isLB Xo.univ.t.PP.isLB _) Q.isLB hT2.symm e2345
    exact GlobalTheory.lbIso_lbPow main 1
  ·
    intro i q hq w' hw'
    obtain ⟨u, w, hu1, hu2, hw⟩ := hFC i
    haveI := GlobalTheory.ShFam.OpenReg.mono_spMap_algebraMap (𝓞 K) K
    have hFw : F.φ ≫ B.t.G.hom = F.P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K) := F.fib.2.1.1.w
    have hu3 : u ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
      rw [← cancel_mono (spMap (algebraMap (𝓞 K) K))]
      calc (u ≫ t₀.G.hom) ≫ spMap (algebraMap (𝓞 K) K) = (u ≫ m2.φ) ≫ B.t.G.hom := by
            rw [Category.assoc, Category.assoc, m2.cart.1.w]
        _ = (w.left ≫ F.P₀.A.hom) ≫ spMap (algebraMap (𝓞 K) K) := by
            rw [hu2, Category.assoc, hFw, Category.assoc]
        _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap (𝓞 K) K) := by rw [Over.w w]; rfl
    obtain ⟨q', hq', -⟩ := GlobalTheory.existsUnique_isVecOver hQ.2.1.1 w
    have hq'c : IsLieComb (fun k => σ (v i k)) v' q' :=
      GlobalTheory.ArcQ.NormalForm.isLieComb_baseChange hQ.2.1 (fun k => hv' k) hq' hw
    have hqq : q = q' := by
      obtain ⟨a, ha, rfl⟩ := hq
      obtain ⟨b, hb, rfl⟩ := hq'c
      have hab : a = b := funext fun k => Over.OverMorphism.ext ((ha k).trans (hb k).symm)
      rw [hab]
    subst hqq
    have key : q.left ≫ χ₀ = spMap (dualMap σ) ≫ u := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, hχ₀2, Category.assoc, hu2, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ F.φ) hq'
      · rw [Category.assoc, hχ₀b, Category.assoc, hu3, ← Category.assoc, Over.w q]
        show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ = _
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hw', hz.2.1, ← hu1, hφσ]
      change (q.left ≫ fl) ≫ m.φ = _
      rw [Category.assoc, hfl, ← Category.assoc, key, Category.assoc]
      rfl
    · exact (Over.w (q ≫ f)).trans (Over.w w').symm

end GlobalTheory.PtDeg
