import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_prime_comparison : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ a, inC a → ∀ i, (eigA O c T R i).lg v e y =
      Real.log (e.w (valAt y.1 (genAt (eigA O c T R i).D (below y.1) * (dgOf O c (below y.1) i : (O.Φ.C c).Y.Fn)))) +
        Real.log (colMinor e.w (M a) (blkLe (fun l : Fin (D.R.f * O.N) => letterEmb O l) i)) -
          Real.log (colMinor e.w (M a) (blkLt (fun l : Fin (D.R.f * O.N) => letterEmb O l) i)) +
            (if letterEmb O i ∈ cmSet O then vDiff D.host.E p else 0) * Real.log (e.w (p : AlgebraicClosure D.what₂.LL)) := by
  first | exact @GlobalTheory.EqHalf.EigNorm.lg_eigA | exact GlobalTheory.EqHalf.EigNorm.lg_eigA | (intros; apply GlobalTheory.EqHalf.EigNorm.lg_eigA <;> assumption)
