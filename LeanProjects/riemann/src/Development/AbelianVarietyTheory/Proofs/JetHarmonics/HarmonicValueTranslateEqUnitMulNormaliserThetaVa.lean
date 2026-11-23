import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFramesEL
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlphaFormHarmonicValueAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueConnectionIntegralChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateThetaFrameGermEqUnitMulBoxProduct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OneColumnTranslateSectionRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem addVal_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (u : F) (m : ℕ) (hm : 0 < m)
    (hu : u ^ m = 1) : v u = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hu
    exact zero_ne_one hu
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, hu, AddValuation.map_one]
  have ht : v u ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  lift v u to ℚ using ht with q hq
  have h3 : m • q = 0 := by exact_mod_cast h1
  rw [nsmul_eq_mul] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h (by exact_mod_cast hm.ne')
  · rw [h]; rfl

theorem addVal_prod_eq_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {K : Type} (s : Finset K) (u : K → F)
    (hu : ∀ i, v (u i) = 0) : v (∏ i ∈ s, u i) = 0 := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, AddValuation.map_mul, hu, ih, add_zero]

theorem boxSer_smul {k : Type} [CommRing k] {n d : ℕ} (u : Fin n → k) (f : Fin n → PS k 1 d) :
    boxSer (fun i => u i • f i) = (∏ i, u i) • boxSer f := by
  simp only [boxSer, map_smul]
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

set_option maxHeartbeats 1600000 in

theorem harmonicValue_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N = l.M → α * star α = (N : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∃ (xx : Fin n → Dw.La) (u : F), v u = 0 ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (io (nrm Dw c a α) * evI y f) := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y C hFT P hTors hAlg ϖ hϖ Q hQ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG
    U' PU _ oD' hxe hoD α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t q e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm hx
  letI := H.starRing
  letI := io.toAlgebra
  subst hN
  obtain rfl : q = l.M := by rw [← e, Nat.one_mul]
  have hodd : Odd l.M := l.odd
  have h1 : 1 ≤ l.M := le_trans (by norm_num) l.three_le

  obtain ⟨τ, hτG, hτEL, hτT⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.15 C.17 C.18
  have hUJ : IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT := GlobalTheory.T.universal_statement E H Dw l Xo c T io y C
  have hAG := GlobalTheory.GermBasic.main T.V _ _ _ P.U _ C.xT hUJ τ hτG F l.M

  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨yF, hyF⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr F φ y.1

  obtain ⟨θ₁, θα₁, hθ₁, hθα₁, hcol⟩ := GlobalTheory.OneColTranslate.oneColumn_translate E H Dw l Xo c T io y.1 C.I P ϖ hϖ F φ rfl
    yF hyF α l.M hodd hα

  obtain ⟨u₀, p₁, w₁, ζ₁, r₀, r, σ₁, f, hu₀, hhf, hcols⟩ := GlobalTheory.ColumnSplit.main E H Dw l Xo c T io y C hFT P hTors hAlg
    ϖ hϖ Q hQ F v hv n D' A' G' pD pA pG U' PU oD' hxe hoD τ hτG hτEL α l.M h1 hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀
    t l.M e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm
  have hall := fun i => hcol (p₁ i) (w₁ i) (ζ₁ i) (x ≫ pA.pr i) (r₀ i) (r i) (σ₁ i) (hcols i).1 (hcols i).2.1
    (hcols i).2.2.1 ((Category.assoc _ _ _).trans (hx i)) (hcols i).2.2.2.1 (hcols i).2.2.2.2.1 (hcols i).2.2.2.2.2.1
  choose U B HH S0 hU hB hTP hTie hσ using hall

  have hex : ∀ i, ∃ g, GermA P.U.toUnifPre C.xT τ F l.M (S0 i) g := fun i => hAG.2.2 (hτT hFT) (S0 i)
  choose f' hf' using hex
  have hff : ∀ i, f i = U i • f' i := by
    intro i
    have hlin := hAG.2.1 1 (fun _ => U i) (fun _ => S0 i) (fun _ => f' i) (σ₁ i) (fun _ => hf' i)
      (by intro jj; rw [Fin.sum_univ_one]; exact hσ i jj)
    have := hAG.1 (σ₁ i) _ _ (hcols i).2.2.2.2.2.2 hlin
    rw [Fin.sum_univ_one] at this
    exact this
  have hh2 : h = (u₀ * ∏ i, U i) • boxSer f' := by
    rw [hhf, show f = fun i => U i • f' i from funext hff, boxSer_smul, smul_smul]
  have hv0 : v (u₀ * ∏ i, U i) = 0 := by
    rw [AddValuation.map_mul, hu₀, zero_add]
    refine addVal_prod_eq_zero v Finset.univ U (fun i => ?_)
    obtain ⟨m, hm, hum⟩ := hU i
    exact addVal_eq_zero_of_pow_eq_one v (U i) m hm hum

  have hT := GlobalTheory.harmonic_value_of_tied_sections E H Dw l Xo c nab hnab T io y C P τ hτG hτEL F φ rfl yF hyF l.M n S0
    HH f' hTie hf'
  obtain ⟨xx, Fs, hFs, hA⟩ := GlobalTheory.AlphaForm.alphaForm_at_point E H Dw l Xo c nab hnab F yF α hα hMb n B HH hB hTP
  refine ⟨xx, u₀ * ∏ i, U i, hv0, ?_⟩
  intro a Pp hP fth hth
  have h9918 := GlobalTheory.PtTie.evI_eq_thExpr_ext E H Dw l Xo c nab hnab T io y F φ rfl yF hyF a n xx Pp hP Fs hFs fth hth
  have key : ∀ (g : PS F n (chD C.ch)) (s : F),
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M (s • g) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) =
      s * nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M g (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) := by
    intro g s
    have := (GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M n (LtN Dw n)
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))).2.1
      (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) (Fin 1) (fun _ => s) (fun _ => g)
    simp only [Fin.sum_univ_one] at this
    exact this
  have hT' := hT a Pp hP
  rw [hA a Pp hP] at hT'
  rw [hh2, key, map_mul, h9918]
  exact congrArg (fun z => (u₀ * ∏ i, U i) * z) hT'.symm

end GlobalTheory.PtTie
