import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonvaStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_frPt_of_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g) (U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K) (w : Fin Φ.T.g → (epsR K ⟶ Φ.T.t.G)), x ≫ Xo.s = sOf c K → U.det ≠ 0 → (∀ k, IsLieComb (U k) Φ.v (w k)) → (∀ τ i, IsEigAt c τ ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ)) → ∃ y : FrPt Xo c K, y.x = x ∧ SecTie Φ.m Φ.th y.s ∧ ∀ τ i, y.u τ i = (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo c K _ _ x Φ e U w hx hU hw heig
  have hb : IsLieBasis w :=
    ((GlobalTheory.LieComb.lieComb_algebra K Φ.T.t.G Φ.T.g Φ.v Φ.basis.1).2.2.2.2 U w Φ.basis hw).2 hU.isUnit
  have ht : TanBasis x (fun i => (w i).left ≫ Φ.m.φ) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo K x Φ.T.t.G Φ.m.φ Φ.m.cart).2 _ w).1 hb
  have htan : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsTanAt x ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) :=
    fun τ i => ht.1 (e ⟨τ, i⟩)
  have hbas := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c K x
    (fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) Φ.T.g e.symm htan heig).2 (by
      have : (fun j => (w (e ⟨(e.symm j).1, (e.symm j).2⟩)).left ≫ Φ.m.φ) = fun i => (w i).left ≫ Φ.m.φ :=
        funext fun j => congrArg (fun k => (w k).left ≫ Φ.m.φ) (e.apply_symm_apply j)
      exact this ▸ ht)
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing E H Dw l Xo K x Φ.T.t Φ.m
  obtain ⟨s, hs⟩ := h1 Φ.th
  have hgen : SecGen x s := GlobalTheory.Frames.secGen_of_secNZ GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo K x s
    ((h3 Φ.th s hs).2.2 Φ.th_ne)
  exact ⟨⟨x, hx, fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ, htan, heig, hbas, s, hgen⟩, rfl, hs, fun _ _ => rfl⟩

end GlobalTheory.LamT
