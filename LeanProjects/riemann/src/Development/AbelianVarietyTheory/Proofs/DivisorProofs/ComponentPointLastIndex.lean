import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationCaseFiniteComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSubStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LawsCore
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjectDefiniteLieEigenLatticeDegreeDifferenceStatement
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FlatCore

namespace GlobalTheory.DefCoreLie

theorem frameDeg_def (hCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) [NeZero H.d] (χ : DirichletCharacter ℂ H.d) (hχ : GlobalTheory.IsKroneckerChar χ)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (hL : Laws U x) (hq : Dw.q = 0) : FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  intro Z τ s ρ hρ
  obtain ⟨K, iF, iN, iA, y, ρ₀, σ₁, X, t₀, hy, hm₁, hm₂, hρ₀⟩ := GlobalTheory.T.exists_cm_goodReduction_point_on_component E H Dw l Xo c r U x hL Z
  obtain ⟨F⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K X.B.pol
  obtain ⟨⟨h, hh⟩, -⟩ :=
    GlobalTheory.CM.LieMetric.exists_unique_isHerm GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 K X.B.pol F
  let f : 𝓞 E →+* K := (algebraMap c.F K).comp (embK c τ.1)
  have hf : ∀ a, IsIntegral ℤ (f a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map f.toIntAlgHom
  let t : 𝓞 E →+* 𝓞 K := f.codRestrict (integralClosure ℤ K).toSubring hf
  have ht : ∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a) := fun a => rfl
  obtain ⟨hfin, hdeg⟩ := GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy X.B t₀ hm₁ hm₂ F h hh t ht
  have htρ : t H.rt = ρ₀ := by
    apply RingOfIntegers.ext
    rw [ht, hρ₀ τ]
  exact ⟨hfin, hdeg.trans (hCM E H hH χ hχ K ρ₀ σ₁ Dw.p Dw.q X F h hh hq t htρ)⟩

end GlobalTheory.DefCoreLie

namespace GlobalTheory.DefCoreLie

theorem degLie_core : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hm hG hW hN hF Z P τ
  obtain ⟨hDC, -, -, -⟩ := GlobalTheory.T.deformation_case_finite_components p i PP A M hR hm hG hW hN hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  have hL : Laws (p.T.U ((i : ℕ) + 1)) (xiR D) := GlobalTheory.LawsCore.laws_core D p.T hJ _ hj hF
  obtain ⟨_, χ, hχ, hOm, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q hJ.pins.1 p.Del p.h0
  have hFr := frameDeg_def GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference D.host.E p.T.Q.H hH χ hχ _ _ _ _ _ _ _ hL hDC.q
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec (p.T.U ((i : ℕ) + 1)) (xiR D) hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ
  have h := (hFr Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
  rw [(GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s, s.deg_eq_toFrame, flatDegVal, ← hOm, ← h]
  rfl

end GlobalTheory.DefCoreLie
