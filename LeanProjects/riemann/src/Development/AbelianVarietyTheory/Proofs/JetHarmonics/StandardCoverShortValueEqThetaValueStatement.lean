import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StandardCoverShortValueEqThetaValue
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardCover_shortValue_eq_thetaValue : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → IsNab Xo c nab → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ (m N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (x : Fin m → Dw.La) (P : MvPolynomial (LtN Dw m) c.F) (q₀ : Fin m → LevQ Dw d.l₂), GenLat.LevOK (⟨stdLat E m⟩ : GenLat E m) N d.l₂.M → P ∈ harmA c a m → (∀ b, levRep (q₀ b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧ levRep (q₀ b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) → ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∀ v v' : k, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q : Fin m → LevQ Dw d.l₂ => if q = q₀ then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) (⟨stdLat E m⟩ : GenLat E m) 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) y₂ v → ThValAt Xo c nab y x P v' → v = v' := by
  first | exact @GlobalTheory.shortValAt_std_cover_eq_thValAt | exact GlobalTheory.shortValAt_std_cover_eq_thValAt | (intros; apply GlobalTheory.shortValAt_std_cover_eq_thValAt <;> assumption)
