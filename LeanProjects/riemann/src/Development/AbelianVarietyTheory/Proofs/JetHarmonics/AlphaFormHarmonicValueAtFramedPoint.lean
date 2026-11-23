import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRuleStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateLStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelPointEqOfKilledByHalfLevelStatement
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.AlphaForm

theorem totalDegree_harm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  simp only [harmA, HaO, HHa, RowDeg, Set.mem_setOf_eq] at hP
  obtain ⟨⟨-, -, hD⟩, -⟩ := hP
  have hR : ∀ m ∈ P.support, (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    refine (Fintype.sum_sigma (fun ℓ => m ℓ)).trans ?_
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hD m hm τ i
  apply le_antisymm
  · exact Finset.sup_le fun m hm => (hR m hm).le
  · obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
    rw [← hR m hm]
    exact MvPolynomial.le_totalDegree hm

theorem nrm_mul_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {l : Level H}
    (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α β : 𝓞 E) (N : ℕ) (h : α * β = (N : 𝓞 E)) :
    nrm Dw c a α * nrm Dw c a β = (N : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) := by
  simp only [nrm]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← mul_pow, ← map_mul, h, map_natCast]

theorem alphaForm_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (α : 𝓞 E), α * star α = (l.M : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (n : ℕ) (b : Fin n → (ptO Xo yF.x ⟶ Xo.univ.t.G)) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) (ptO Xo yF.x))), (∀ i, b i ≫ Xo.univ.t.act.act (star α) = 1) → (∀ i, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) l.M yF.s (b i) (hh i)) → ∃ (xx : Fin n → Dw.La) (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x))), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (l.M : ℤ) (hh i) (colOf m i) = algebraMap c.F F (nrm Dw c a α) * thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c nab hnab F _ _ _ yF α hα hMb n b hh hb hT
  letI := H.starRing
  have hI := fun i => GlobalTheory.T.normalizedPullback_conjugate_translate_eq_translate_level E H Dw l Xo c F yF.x α hα hMb yF.s (b i) (hh i) (hb i) (hT i)
  choose Fs hN hV using hI
  have hK : ∀ i, KilledBy Xo l.Mb (b i ≫ Xo.univ.t.act.act α) := by
    intro i
    unfold KilledBy
    intro x hx
    rw [hMb, Ideal.mem_span_singleton'] at hx
    obtain ⟨r, rfl⟩ := hx
    have e : α * (r * star α) = star α * (α * r) := by ring
    rw [Category.assoc, ← Xo.univ.t.act.mul, e, Xo.univ.t.act.mul, ← Category.assoc, hb i]
    haveI := Xo.univ.t.act.hom (α * r)
    simp
  choose xx hxx using fun i => GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel E H Dw l Xo c F yF (b i ≫ Xo.univ.t.act.act α) (hK i)
  refine ⟨xx, Fs, fun i => by rw [hxx i]; exact hV i, ?_⟩
  intro a Pp hPp
  have hs : star α * star (star α) = ((l.M : ℕ) : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hα
  have hz : ((l.M : ℤ) ^ 2) = ((l.M * l.M : ℕ) : ℤ) := by push_cast; ring
  have h := GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab F yF (star α) l.M l.M ((l.M : ℤ) ^ 2) hs hz n hh Fs hN a Pp hPp
  have hM : ((l.M : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  unfold thExpr
  rw [h]
  by_cases h0 : Pp = 0
  · subst h0
    simp
  have key : nrm Dw c a α * ((l.M : c.F) ^ Pp.totalDegree)⁻¹ * nrm Dw c a (star α) = 1 := by
    rw [totalDegree_harm c hPp h0, _root_.mul_right_comm, nrm_mul_nrm Dw c a α (star α) l.M hα]
    exact mul_inv_cancel₀ (pow_ne_zero _ hM)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← map_mul, ← map_mul, key, map_one, _root_.one_mul]

end GlobalTheory.AlphaForm
