import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLift
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMove
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelMapsRankZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.EquivariantLiftInvariance

theorem cover_product_indep_of_lift : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (β : d.c₂.F) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  intro hC E _ _ _ H Dw l Xo c n d hLev hA hnab ψ htie w hw Λ N hU hT hOK a P hP β r' m' hE' k _ _ _ _
    hk y y₂ y₂' ho ho' v v' hv hv'
  obtain ⟨_, hnab⟩ := hnab
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hN := GlobalTheory.LevelMapsAnyRank.levelMaps Dw
  obtain ⟨hdvd, hM, hcop, hb, hI, hE, -⟩ := hLev
  obtain ⟨g, ρ, ν, hg, hρ, hmv, hfr⟩ := GlobalTheory.exists_levMove_of_frOver hL E H Dw l Xo c n d hN hdvd hM hE
    r' m' hE' k hk y y₂ y₂' ho ho'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := by
    refine (Ideal.mul_le_inf.trans inf_le_left : d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ _) ?_
    rw [d.l₂.prod]; exact Ideal.mem_span_singleton_self _
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  obtain ⟨kI, hkI⟩ := GlobalTheory.DatumInverseCharacter.exists_quot_equiv Dw (hbI hmb) _ g' hg'
  obtain ⟨σ, hσ⟩ := GlobalTheory.DatumInverseCharacter.exists_quot_equiv Dw hmb _ g' hg'
  have hw' := hw g hg kI σ.toEquiv (fun a => (hkI a).symm) hσ
  have hgA : ∀ a, Dw.ModN d.l₂.A (g.f d.l₂.A a - a) := by rw [hA]; exact hg.2.2
  have hc := htie kI g ρ hg hgA hρ (fun a => (hkI a).symm) k y₂ y₂' hfr.1
  have h1 := GlobalTheory.ShortValMove.shortValAt_move hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k ρ.hom ν _ _ y₂ y₂' hmv hfr
    σ.toEquiv hσ n a P hP (fun q => d.eF (w q)) Λ β N v' hv'
  have h2 := GlobalTheory.ShortLiftInvariance.shortValAt_smul d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q))
    (fun q => d.eF (w (fun b => σ.toEquiv.symm (q b)))) (d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F))
    (fun q => by rw [hw', map_mul]) Λ β N P y₂ v hv
  have h3 := ((GlobalTheory.shortThetaValue_existsUnique_natural hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hOK a P
    hP _ β).1 k y₂).unique h1 h2
  rw [hc, h3, _root_.mul_mul_mul_comm, ← map_mul, ← map_mul]
  simp

end GlobalTheory.EquivariantLiftInvariance
