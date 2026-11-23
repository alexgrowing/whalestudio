import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueCompatibleSectionExpansionIntegralFrStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

namespace GlobalTheory.PlaceInt

theorem zero_le_val_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (hu : u ^ m = 1) : ((0 : ℚ) : WithTop ℚ) ≤ v u := by
  have h : m • v u = 0 := by rw [← v.map_pow, hu, v.map_one]
  cases hc : v u with
  | top => exact le_top
  | coe q =>
    rw [hc, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h
    rcases h with h | h
    · omega
    · rw [h]

theorem nuGe_zero_of_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k : ℕ) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh hh' : SecN Xo xF k), 1 ≤ k → Moves Xo b hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k σ hh' → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl k b hh hh' hk hmv hν σ' s' hσ' hs'
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have h3 : FiniteOrderValuationInvariance := (GlobalTheory.twisting_statements_of_laws hL GlobalTheory.twistBaseChange).2.1
  have hx := hσ'.base
  obtain ⟨⟨σ, hσ, -⟩, hex⟩ := GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl k hk hh
  obtain ⟨s, hs, -⟩ := hex σ hσ
  obtain ⟨s₁, -, hu'⟩ := (GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl k hk hh').2 σ' hσ'
  obtain ⟨e, he, -⟩ := GlobalTheory.PtTie.exists_mulEquiv_ptTieF E H Dw l Xo c T io y.1 I P F xF hx
  have hxk : (e.symm b) ^ k = 1 := by rw [← map_pow, hmv.1, map_one]
  obtain ⟨f, hf, hsurj, -⟩ := hT F k hk
  obtain ⟨p, hp⟩ := hsurj _ hxk
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen :=
    ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := ReciprocityTheory.ChartRestriction.G.H1.finOrdExists_of_laws hL T.V P.D F k hk p w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V (maximalIdeal T.V) P.D F k hk p w hw
  have h1 : PhiRel P.D.toPre F k p w s (Φ s) := (hΦ _ _).2 rfl
  have h2 : Fam.IsSmul P.D.toPre F ζ (Φ s) (ζ • Φ s) := (ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl
  obtain ⟨u, t', ⟨m, hm, hum⟩, hut, ht'⟩ := GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions E H Dw l Xo c T io y.1 I P F xF hx k hk σ σ' hh hh' s (Φ s) (ζ • Φ s)
    (e.symm b) b p w ζ hσ hσ' hs hmv ((he _ _).2 (e.apply_symm_apply b).symm) ((hf _ _).2 hp.symm) hw hfin h1 h2
  have h4 := (h3 T.V ϖ hϖ P.D Q hQ F v hv k hk p w hw ζ hζ hfin s _ _ h1 h2 0).1 (hν σ s hσ hs)
  have h5 := NuGe.smul Q (zero_le_val_of_pow_eq_one v hm hum) hut h4
  rw [add_zero] at h5
  rw [hu' s' hs', ← hu' t' ht']
  exact h5

end GlobalTheory.PlaceInt
