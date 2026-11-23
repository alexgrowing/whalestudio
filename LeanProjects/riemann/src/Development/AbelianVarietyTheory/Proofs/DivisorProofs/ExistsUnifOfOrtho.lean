import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticePrimeToPBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatLogEqLogStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

namespace GlobalTheory.OrthoFibreUnif

section General

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G

theorem exists_unif_of_ortho (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r)
    (ξ : ℝ) (hpq : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom)
    (hξ : ∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ) (hx : (U.X k).IsOrtho x.1) :
    ∃ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t (U.un k x).x) (n : ℕ)
      (e : Fin n ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) (u' : HolUnif T.pol.A T.pol.L n) (χ' : u'.Λ → ℂ),
      u'.IsAH (((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) χ' ∧
      ∀ (τ : E →+* ℂ) (C : Fin (Dw.mult τ) → CAt σ),
        ∃ (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left) (w' : epsR ℂ ⟶ T.pol.A),
          IsCombAt (U.un k x).x ((U.un k x).u τ) C v ∧ w'.left ≫ m.φ = v ∧
            u'.IsDiff (∑ l, toC (C l) • Pi.single (e.symm ⟨τ, l⟩) (1 : ℂ)) w' := by
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := GlobalTheory.OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨Φ₀⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : GlobalTheory.LamT.FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, -, hA, -, -, -, hD⟩ := GlobalTheory.OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos
    Wu.c2 Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  rw [hH] at hA
  refine ⟨Φ.T, Φ.m, W.g, W.e, u, χ, hA, fun τ C => ?_⟩
  obtain ⟨t1, t2, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per
  obtain ⟨v, hv, -⟩ := t2 (∑ l, toC (C l) • Pi.single (W.e.symm ⟨τ, l⟩) (1 : ℂ))
  have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per (Dw.mult τ)
    ((U.un k x).u τ) (fun l => Pi.single (W.e.symm ⟨τ, l⟩) 1) (W.der τ) (fun l => toC (C l)) v).2 hv
  have htan := t1 _ _ hv
  rw [← W.pt] at hc htan
  obtain ⟨w', h1, h2⟩ := hD _ _ htan hv
  exact ⟨v, w', hc, h1, h2⟩

end General

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead
open AlgebraicGeometry CategoryTheory IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

end GlobalTheory.OrthoFibreUnif
