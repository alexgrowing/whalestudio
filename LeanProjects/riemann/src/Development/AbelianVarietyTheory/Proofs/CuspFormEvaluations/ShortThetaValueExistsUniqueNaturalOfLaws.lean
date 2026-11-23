import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverShortThetaValueDataStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValue

theorem finite_levelQuotient {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted_finsum {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q
  simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

end GlobalTheory.ShortValue

namespace GlobalTheory

theorem shortThetaValue_existsUnique_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hN a P hP w β
  haveI := ShortValue.finite_levelQuotient Dw l
  have cmp := GlobalTheory.T.shortThetaSum_eq_of_witnesses_common_algebra hL hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hP
  have nat : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 →
      ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
    intro S T _ _ _ _ φ y0 y hφ v0 v h0 h1
    obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := h0
    obtain ⟨S2, _, _, φ2, y2, z2, tp2, F2, hf2, hm2, hz2, hg2, ht2, hu2, e2⟩ := h1
    obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ :=
      exists_faithfullyFlat_pushout c.F S S2 S1 (φ2.comp φ) φ1 hf1
    have key := cmp S y0 S1 φ1 y1 z1 tp1 F1 S2 (φ2.comp φ) y2 z2 tp2 F2 hm1
      (FramedBaseChange.trans φ φ2 hφ hm2) hz1 hg1 ht1 hu1 hz2 hg2 ht2 hu2 U ψ1 ψ2 hc.symm
    have hinj2 : Function.Injective φ2 := hf2.injective
    apply hinj2
    apply hinj
    have e0 : ψ2 (φ2 (φ v0)) = ψ1 (φ1 v0) := AlgHom.congr_fun hc v0
    rw [e0, e1, e2]
    exact ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _ key
  refine ⟨fun S _ _ y => ?_, nat⟩
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1⟩ :=
    GlobalTheory.T.exists_faithfullyFlat_cover_shortThetaValue_data hL E H Dw l Xo c n Λ N hU hT hN S y
  obtain ⟨v, hv, -⟩ := existsUnique_preimage_of_faithfullyFlat c.F S S1 φ1 hf1
    (algebraMap c.F S1 (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S1 (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) *
          ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b))
    (fun T _ _ ψ1 ψ2 hc => ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _
      (cmp S y S1 φ1 y1 z1 tp1 F1 S1 φ1 y1 z1 tp1 F1 hm1 hm1 hz1 hg1 ht1 hu1 hz1 hg1 ht1 hu1 T ψ1 ψ2 hc))
  have hv' : ShortValAt Xo c nab w Λ β N P y v :=
    ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, hv⟩
  exact ⟨v, hv', fun v' h' => nat S S (AlgHom.id c.F S) y y (FramedBaseChange.refl y) v' v h' hv'⟩

end GlobalTheory
