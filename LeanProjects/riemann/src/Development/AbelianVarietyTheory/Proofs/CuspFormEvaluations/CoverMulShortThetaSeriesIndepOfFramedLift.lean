import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLawsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMoveStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortLiftInvariance

theorem shortValAt_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) {n : ℕ}
    (w w' : (Fin n → LevQ Dw l) → c.F) (t : c.F) (hw : ∀ q, w' q = t * w q)
    (Λ : GenLat E n) (β : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (h : ShortValAt Xo c nab w Λ β N P y v) :
    ShortValAt Xo c nab w' Λ β N P y (algebraMap c.F S t * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, AlgHom.commutes, h7]
  simp only [hw, map_mul, _root_.mul_assoc]
  by_cases hf : Finite (Fin n → LevQ Dw l)
  · have := Fintype.ofFinite (Fin n → LevQ Dw l)
    simp only [finsum_eq_sum_of_fintype]
    rw [← Finset.mul_sum]
    ring
  · have := not_finite_iff_infinite.mp hf
    simp [Nat.card_eq_zero_of_infinite]

theorem cover_product_indep_of_lift : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  intro hL hC E _ _ _ H Dw l Xo c n d hN1 hLev hA _ hNab hex Λ N hU hT hO a P hP x0 β r' m' hE k _ _ _ _ hk y y₂ y₂' hF hF' v v' hv hv'
  obtain ⟨ph, ψ, x₀, hph, hpsi⟩ := hex
  obtain ⟨hDvd, hM, hcop, hMb, hI, hEta, -, -, -⟩ := hLev
  obtain ⟨g, ρ, ν, hg, hρ, hmv, hfm⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL E H Dw l Xo c n d hN1 hDvd hM hEta r' m' hE k hk y y₂ y₂' hF hF'
  obtain ⟨kI, σq, hk1, hk2, hk3⟩ :=
    GlobalTheory.DatumInverseCharacter.datum_inv_char E H Dw l Xo c n d hM hcop hMb hI hDvd ph ψ x₀ hph g hg
  have hx : y₂'.x = y₂.x ≫ ρ.hom := by
    unfold FrMove at hfm
    exact hfm.1
  have hmod : ∀ a : Dw.La, Dw.ModN d.l₂.A ((g.f d.l₂.A) a - a) := by
    intro a
    rw [hA]
    unfold Sim.InGam at hg
    exact hg.2.2 a
  unfold DeltaDat.PsiTie at hpsi
  have hev := hpsi kI g ρ hg hmod hρ hk1 k y₂ y₂' hx
  have h1 := GlobalTheory.T.shortThetaValue_under_levelMove hL hC E H Dw d.l₂ d.Xo₂ d.c₂ _ hNab k ρ.hom ν (g.f d.l₂.M) (g.f d.l₂.A)
    y₂ y₂' hmv hfm σq hk2 n a P hP (d.w x0) Λ β N v' hv'
  have hw : ∀ q, d.w x0 q = d.eF ↑(ψ kI) * d.w x0 (fun b => σq.symm (q b)) := by
    intro q
    rw [hk3, ← _root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.one_mul]
  have h2 := shortValAt_smul d.Xo₂ d.c₂ _ _ (d.w x0) (d.eF ↑(ψ kI)) hw Λ β N P y₂ v' h1
  have hu := (GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ _ hNab n Λ N hU hT hO a P hP (d.w x0) β).1 k y₂
  rw [hu.unique hv h2, hev]
  ring

end GlobalTheory.ShortLiftInvariance
