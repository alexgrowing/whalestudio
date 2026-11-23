import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CombLineHEqExp
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SupMetricCombinationBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformLawsRootModelBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFormValuationEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormOffVarietyMulStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GoodTwistGoodTwist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspLatticeMulComponentSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointValuesInValueSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelLawsSectionVolumeBoundStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.OS

section Vals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hasVal_add {a : K → ℤ} {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y a s z w)
    (h' : Small.HasVal y a s' z w') : Small.HasVal y a (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hz0', ez'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have h1 := hd k
    have h2 := hd' k
    simp only [Pi.add_apply]
    omega
  refine ⟨dg + dh', dh + dh', g * f' + g' * f, f * f',
    FinRd.ValSub.mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hf') ?_,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg' hf
  · have h1 := hd k
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_add, map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul, ez, ez']
    ring

theorem hasVal_zsmul {a : K → ℤ} {s : Ω} {w : 𝕜} (n : ℤ) (h : Small.HasVal y a s z w) :
    Small.HasVal y a (n • s) z (n • w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, MvPolynomial.C n * g, f, ?_, hf, hd, ?_, hz0, ?_⟩
  · intro m hm k
    rw [MvPolynomial.C_mul'] at hm
    exact hg m (MvPolynomial.support_smul hm) k
  · rw [map_mul, e, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]
  · rw [map_mul, ez, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]

theorem hasVal_zero_of {a : K → ℤ} {s : Ω} {w : 𝕜} (h : Small.HasVal y a s z w) :
    Small.HasVal y a (0 : Ω) z (0 : 𝕜) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  exact ⟨dg, dh, 0, f, FinRd.ValSub.mh_zero dg, hf, hd, by simp, hz0, by simp⟩

theorem hasVal_comb {I : Type} [Fintype I] (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {a : K → ℤ} {s : Ω} {v₀ : 𝕜}
    (h₀ : Small.HasVal y a s z v₀) (u : I → Ω) (v : I → 𝕜) (nn : I → ℤ) (hu : ∀ i, Small.HasVal y a (u i) z (v i))
    (hs : s = ∑ i, nn i • u i) : v₀ = ∑ i, nn i • v i := by
  classical
  have key : ∀ S : Finset I, Small.HasVal y a (∑ i ∈ S, nn i • u i) z (∑ i ∈ S, nn i • v i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hasVal_zero_of h₀
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact hasVal_add (hasVal_zsmul _ (hu i)) ih
  exact Small.ReadFinTest.hasVal_unique hz h₀ (hs ▸ key Finset.univ)

end Vals

theorem mem_ptsOver_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P := by
  refine ⟨h.1, fun f hf => ?_⟩
  have := h.2 f hf
  rw [MvPolynomial.eval_map] at this
  rw [MvPolynomial.aeval_def]
  exact this

theorem prod_rel {J : Type} [Fintype J] (s : J → ℝ) (hs : ∀ j, 0 < s j) (a b c d : J → ℤ) (q m₁ m₂ : ℕ)
    (h : ∀ j, (q : ℤ) * a j = q * b j + m₁ * c j + m₂ * d j) :
    (∏ j, s j ^ a j) ^ q = (∏ j, s j ^ b j) ^ q * (∏ j, s j ^ c j) ^ m₁ * (∏ j, s j ^ d j) ^ m₂ := by
  simp only [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hs' := (hs j).ne'
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    ← zpow_add₀ hs', ← zpow_add₀ hs']
  congr 1
  have := h j
  linarith

theorem mul_eq_mul_conj_alt (A B C D P₁ P₂ : ℝ) (q m₁ m₂ : ℕ) (h : A ^ q = B ^ q * C ^ m₁ * D ^ m₂)
    (e : P₁ ^ q * P₂ ^ m₁ = 1) : A ^ q = (P₁ * B) ^ q * (P₂ * C) ^ m₁ * D ^ m₂ := by
  rw [mul_pow, mul_pow, h]
  linear_combination (-(B ^ q * C ^ m₁ * D ^ m₂)) * e

section Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def zc (Dw : Datum H) (a : WZ E) : Option (RootIx Dw) → ℤ
  | none => 0
  | some r => if (r.2 : ℕ) < Dw.p then -a (r.1.1, r.2) else a (conjEmb r.1.1, Dw.p + Dw.q - 1 - r.2)

theorem zc_coef (Dw : Datum H) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (a : WZ E) (j : Option (RootIx Dw)) :
    ((zc Dw a j : ℤ) : ℝ) = RM.coef (towerWt Dw a) 0 j := by
  rcases j with _ | r
  · simp [zc, Top.RootModel.coef]
  · simp only [zc, Top.RootModel.coef, towerWt]
    split_ifs <;> simp

theorem zc_lin (Dw : Datum H) (a₁ a' aτ b : WZ E) (μ m : ℕ)
    (hWE : WEq Dw ((8 * μ) • a₁) ((8 * μ) • a' + (3 * μ) • aτ + m • b)) (j : Option (RootIx Dw)) :
    ((8 * μ : ℕ) : ℤ) * zc Dw a₁ j = ((8 * μ : ℕ) : ℤ) * zc Dw a' j + ((3 * μ : ℕ) : ℤ) * zc Dw aτ j + (m : ℤ) * zc Dw b j := by
  rcases j with _ | r
  · simp [zc]
  · simp only [zc]
    split_ifs with hr
    · have hm : Dw.mult r.1.1 = Dw.p := Small.mult_labelC Dw (.inl r.1)
      have := hWE r.1.1 r.2 (by rw [hm]; exact hr)
      simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at this
      push_cast at this ⊢
      linear_combination -this
    · have hm : Dw.mult (conjEmb r.1.1) = Dw.q := Small.mult_labelC Dw (.inr r.1)
      have h2 := r.2.2
      have := hWE (conjEmb r.1.1) (Dw.p + Dw.q - 1 - r.2) (by rw [hm]; omega)
      simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at this
      push_cast at this ⊢
      linear_combination this

end Coef

section Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_real_of_le {v : EReal} {X : ℝ} (hb : v ≠ ⊥) (h : v ≤ (X : EReal)) : ∃ x : ℝ, v = x ∧ x ≤ X := by
  have ht : v ≠ ⊤ := (lt_of_le_of_lt h (EReal.coe_lt_top X)).ne
  refine ⟨v.toReal, (EReal.coe_toReal ht hb).symm, ?_⟩
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]
  exact h

theorem exists_real_of_ge {v : EReal} {X : ℝ} (ht : v ≠ ⊤) (h : (X : EReal) ≤ v) : ∃ x : ℝ, v = x ∧ X ≤ x := by
  have hb : v ≠ ⊥ := (lt_of_lt_of_le (EReal.bot_lt_coe X) h).ne'
  refine ⟨v.toReal, (EReal.coe_toReal ht hb).symm, ?_⟩
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]
  exact h

theorem fin_bounds (hG : Top.Given) [IsGalois ℚ E] (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c)
    (e : Comp Xo c → Rul Xo c) (hL : CompLaws U h e) (hU : Ref.UnifAll Xo c)
    {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (SS : Finset ℕ)
    (RM : Top.RootModel (CMType H) (Dw.p + Dw.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys)
    (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z)
    (hOm : Or.𝔐.OmVB) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS)
    (a₁ a' aτ : WZ E) (w : CMType H → ℤ) {x : ℝ} (F : FlatSec U x (e Z) (flatZ H w)) (μ m : ℕ)
    (τ : Rul Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (n₁ n' nτ nσ : Option (RootIx Dw) → ℤ)
    (Λ : ℝ) (G : Small.GenModel RM Λ) (ei : G.I ≃ Fin n) (ep bτ b : ℕ → ℝ) (c₀ ρ : ℝ)
    (hn₁ : ∀ j, (n₁ j : ℝ) = RM.coef (towerWt Dw a₁) 0 j) (hn' : ∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a') 0 j)
    (hnτ : ∀ j, (nτ j : ℝ) = RM.coef (towerWt Dw aτ) 0 j)
    (hnσ : ∀ j, (nσ j : ℝ) = RM.coef (towerWt Dw (flatZ H w)) 0 j)
    (hrel : ∀ j, ((8 * μ : ℕ) : ℤ) * n₁ j = ((8 * μ : ℕ) : ℤ) * n' j + ((3 * μ : ℕ) : ℤ) * nτ j + (m : ℤ) * nσ j)
    (hτsec : τ ∈ secZ Xo c aτ)
    (hspanZ : Submodule.span ℤ (Set.range ω) = (latOn U h a₁ Z).restrictScalars ℤ)
    (hGw : ∀ j, G.w j = Fr.rd (ω (ei j)) * ∏ r', Or.e r' ^ (-n₁ (some r')))
    (hc₀ : c₀ ≤ 3 * ρ)
    (hfin : ∀ (p : ℕ), p.Prime → ∀ la : HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ la.asIdeal →
      (Ref.pjSys Xo c).RefBound (cuspZ Xo c U a₁) la (ramOverZ la * ep p) c₀ (Ref.phU Xo c la) ∧
      -F.cFin la ≤ ramOverZ la * b p ∧
      ∀ y : (Ref.pjSys Xo c).Pt la, 0 ≤ Ref.phU Xo c la y ∧
        ((8 * ρ * Ref.phU Xo c la y - ramOverZ la * bτ p : ℝ) : EReal) ≤ (Ref.pjSys Xo c).val y τ) :
    ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (p : ℕ) [Fact p.Prime],
      Small.FinBounds RM.y G.w (Top.combLine (RM.line 1) n₁).a (Top.combLine (RM.line 1) n').a
        (Top.combLine (RM.line 1) nτ).a (Top.combLine (RM.line 1) nσ).a
        (Fr.rd τ * ∏ r', Or.e r' ^ (-nτ (some r'))) (Fr.rd F.s * ∏ r', Or.e r' ^ (-nσ (some r')))
        (8 * μ) (3 * μ) m u p (ep p)
        ((if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) +
            (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Top.l1 (towerWt Dw a') + 3 * bτ p / 8)
        (b p) := by
  obtain ⟨u, hoff, hu⟩ := GlobalTheory.T.uniform_laws_root_model_bound hG E H Dw l Xo c r U h e hL hU O β Y SS RM Sys Fx Or Fr Z Rd hOm hdisc
  refine ⟨u, hoff, fun p _ z hz hzu => ?_⟩
  obtain ⟨la, y, rec, hpla, hye, hrec, hrd⟩ := hu p z hz hzu
  have hpP : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨hRB, hcF, hτv⟩ := hfin p hpP la hpla
  obtain ⟨ht0, hτy⟩ := hτv y
  have hram : (0 : ℝ) < ramOverZ la := by
    exact_mod_cast Nat.pos_of_ne_zero (Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero la)
  have hNpos : ∀ nn : Option (RootIx Dw) → ℤ, 0 < ∏ r', rec r' ^ nn (some r') := fun nn =>
    Finset.prod_pos fun r' _ => zpow_pos (hrec r').1 _
  have hzp : z ∈ Small.ptsOver (PadicAlgCl p) (mCoordIdeal RM.y) := hz.1
  have hprel := prod_rel rec (fun r' => (hrec r').1) (fun r' => n₁ (some r')) (fun r' => n' (some r'))
    (fun r' => nτ (some r')) (fun r' => nσ (some r')) (8 * μ) (3 * μ) m (fun r' => hrel (some r'))
  have e1 : ((p : ℝ) ^ (-(3 * bτ p / 8))) ^ (8 * μ) * ((p : ℝ) ^ (bτ p)) ^ (3 * μ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le,
      ← Real.rpow_add hp0]
    have : -(3 * bτ p / 8) * ((8 * μ : ℕ) : ℝ) + bτ p * ((3 * μ : ℕ) : ℝ) = 0 := by
      push_cast
      ring
    rw [this, Real.rpow_zero]
  refine ⟨∏ r', rec r' ^ n₁ (some r'), (p : ℝ) ^ (-(3 * bτ p / 8)) * ∏ r', rec r' ^ n' (some r'),
    (p : ℝ) ^ (bτ p) * ∏ r', rec r' ^ nτ (some r'), ∏ r', rec r' ^ nσ (some r'),
    ρ * Ref.phU Xo c la y / ramOverZ la, c₀ * Ref.phU Xo c la y / ramOverZ la,
    hNpos _, mul_pos (Real.rpow_pos_of_pos hp0 _) (hNpos _), mul_pos (Real.rpow_pos_of_pos hp0 _) (hNpos _), hNpos _,
    mul_eq_mul_conj_alt _ _ _ _ _ _ _ _ _ hprel e1, ?_, ?_, ?_, ?_, ?_⟩
  · have : c₀ * Ref.phU Xo c la y ≤ 3 * ρ * Ref.phU Xo c la y := mul_le_mul_of_nonneg_right hc₀ ht0
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hram]
    linarith
  · intro v hv
    obtain ⟨w₀, hw₀, hval⟩ := hRB y
    have hf : e Z * w₀ ∈ latOn U h a₁ Z := GlobalTheory.T.cusp_lattice_mul_component_section E H Dw l Xo c r U h e hL hU a₁ Z w₀ hw₀
    have hfsec : e Z * w₀ ∈ secZ Xo c a₁ := ((mem_latIn _ _ _ _).1 hf).1.1.1
    have hfmem : e Z * w₀ ∈ Submodule.span ℤ (Set.range ω) := by
      rw [hspanZ]
      exact hf
    obtain ⟨nn, hnn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hfmem
    obtain ⟨v₀, hv₀, -, hnorm⟩ := hrd a₁ n₁ hn₁ _ hfsec
    have hvalf : (Ref.pjSys Xo c).val y (e Z * w₀) = (Ref.pjSys Xo c).val y w₀ := by
      rw [(Ref.pjSys Xo c).val_mul, hye, zero_add]
    obtain ⟨X, hX, hXle⟩ := exists_real_of_le ((Ref.pjSys Xo c).val_ne_bot y w₀) hval
    have hsv : (Ref.pjSys Xo c).val y (e Z * w₀) = ((ramOverZ la * (X / ramOverZ la) : ℝ) : EReal) := by
      rw [hvalf, hX, mul_div_cancel₀ _ hram.ne']
    have hn := hnorm _ hsv
    have hsum : Fr.rd (e Z * w₀) * ∏ r', Or.e r' ^ (-n₁ (some r')) = ∑ i, nn (ei i) • G.w i := by
      rw [← hnn, Small.GenFrame.rd, ← Small.GenFrame.rd, ← Small.GenFrame.rdHom_apply, map_sum, Finset.sum_mul,
        ← Equiv.sum_comp ei]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hGw i, map_zsmul, Small.GenFrame.rdHom_apply, smul_mul_assoc]
    have hcomb := hasVal_comb hzp hv₀ G.w v (fun i => nn (ei i)) hv hsum
    have hle : ‖v₀‖ ≤ ‖v‖ := by
      rw [hcomb]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
      rw [zsmul_eq_mul, norm_mul]
      calc _ ≤ 1 * ‖v i‖ := mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _)
        _ = ‖v i‖ := one_mul _
        _ ≤ ‖v‖ := norm_le_pi_norm v i
    refine le_trans ?_ hle
    rw [hn]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp1.le ?_) (hNpos _).le
    have : X / ramOverZ la ≤ ep p + c₀ * Ref.phU Xo c la y / ramOverZ la := by
      rw [div_le_iff₀ hram, add_mul, div_mul_cancel₀ _ hram.ne']
      linarith
    linarith
  · intro wv hw
    obtain ⟨v, hv, htop, hnorm⟩ := hrd aτ nτ hnτ τ hτsec
    have hwv : wv = v := Small.ReadFinTest.hasVal_unique hzp hw hv
    rw [hwv]
    by_cases hT : (Ref.pjSys Xo c).val y τ = ⊤
    · rw [htop hT, norm_zero]
      exact mul_nonneg (Real.rpow_pos_of_pos hp0 _).le (mul_pos (Real.rpow_pos_of_pos hp0 _) (hNpos _)).le
    · obtain ⟨X, hX, hXle⟩ := exists_real_of_ge hT hτy
      have hsv : (Ref.pjSys Xo c).val y τ = ((ramOverZ la * (X / ramOverZ la) : ℝ) : EReal) := by
        rw [hX, mul_div_cancel₀ _ hram.ne']
      rw [hnorm _ hsv, ← mul_assoc, ← Real.rpow_add hp0]
      refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp1.le ?_) (hNpos _).le
      have : 8 * (ρ * Ref.phU Xo c la y / ramOverZ la) - bτ p ≤ X / ramOverZ la := by
        rw [le_div_iff₀ hram, sub_mul, mul_assoc, div_mul_cancel₀ _ hram.ne']
        linarith
      linarith
  · intro wv hw
    obtain ⟨v, hv, -, hnorm⟩ := hrd (flatZ H w) nσ hnσ F.s F.s_sec
    have hwv : wv = v := Small.ReadFinTest.hasVal_unique hzp hw hv
    have hmem := GlobalTheory.T.point_values_in_value_set E H Dw l Xo c la y
    have hcf : (Ref.pjSys Xo c).val y F.s = ((F.cFin la : ℝ) : EReal) := F.fin_eq la _ hmem hye
    have hsv : (Ref.pjSys Xo c).val y F.s = ((ramOverZ la * (F.cFin la / ramOverZ la) : ℝ) : EReal) := by
      rw [hcf, mul_div_cancel₀ _ hram.ne']
    rw [hwv, hnorm _ hsv]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp1.le ?_) (hNpos _).le
    have : -b p ≤ F.cFin la / ramOverZ la := by
      rw [le_div_iff₀ hram]
      linarith
    linarith
  · have hs := GlobalTheory.T.sup_metric_combination_bound (CMType H) (Dw.p + Dw.q) RM (towerWt Dw a') n' p z rec _ hz.1.1 hn'
      (fun r' => (hrec r').1) (fun r' => (hrec r').2)
    refine le_trans hs (le_of_eq ?_)
    rw [← mul_assoc, ← Real.rpow_add hp0]
    congr 2
    ring

end Fin

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def linAt (σ : c.F →+* ℂ) (U₀ : Unf Xo c (goodOf c σ) r) (k : U₀.Comp) (y : Frame (U₀.X k).Ψ r) :
    Rul Xo c →ₛₗ[σ] ℂ where
  toFun f := Small.goodTwist c σ (rdU U₀ f k y)
  map_add' f g := by
    rw [map_add]
    exact map_add (Small.goodTwist c σ) _ _
  map_smul' a f := by
    rw [map_smulₛₗ]
    change Small.goodTwist c σ (goodOf c σ a * rdU U₀ f k y) = σ a * _
    rw [map_mul, Small.goodOf_apply, Small.goodTwist_goodTwist]

theorem pnorm_eq_mul {X : Data E r} (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    X.pnorm la P y = ‖P y‖ * X.pnorm la (fun _ => 1) y := by
  simp [Data.pnorm]

theorem not_good_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := fun h' => by
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := (congrArg (starRingEnd ℂ) h).symm.trans h'
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, him, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem goodOf_conj' (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
  by_cases h : GoodEmb c σ
  · rw [goodOf, goodOf, if_pos h, if_neg (not_good_conj h), e]
  · have h' := goodEmb_goodOf c σ
    rw [goodOf, if_neg h] at h'
    rw [goodOf, goodOf, if_neg h, if_pos h']

theorem lieFacZ_pos (Dw : Datum H) (x : ℝ) (a : WZ E) : 0 < lieFacZ Dw x a := Real.exp_pos _

end Arch

section ArchD

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

theorem arch_bounds (hG : Top.Given) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c)
    (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r)
    (hL : CompLaws U h e) (hLv : abelian₂.LevelLaws U W dict) (hFV : FinVol W)
    {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (SS : Finset ℕ)
    (RM : Top.RootModel (CMType H) (Dw.p + Dw.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys)
    (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z)
    (a₁ aτ : WZ D.host.E) (w : CMType H → ℤ) (F : FlatSec U (xiR D) (e Z) (flatZ H w))
    (τ : Rul Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (n₁ nτ nσ : Option (RootIx Dw) → ℤ)
    (Λ : ℝ) (G : Small.GenModel RM Λ) (ei : G.I ≃ Fin n) (A P R₀ : ℝ)
    (rh : ∀ σ k, Frame ((U σ).X k).Ψ D.R.r → ℝ)
    (hn₁ : ∀ j, (n₁ j : ℝ) = RM.coef (towerWt Dw a₁) 0 j)
    (hnτ : ∀ j, (nτ j : ℝ) = RM.coef (towerWt Dw aτ) 0 j)
    (hnσ : ∀ j, (nσ j : ℝ) = RM.coef (towerWt Dw (flatZ H w)) 0 j)
    (hτsec : τ ∈ secZ Xo c aτ) (hOnto : OntoZ U h e a₁ Z)
    (hspanF : Submodule.span c.F (Set.range ω) = cuspOn U h a₁ Z)
    (hGw : ∀ j, G.w j = Fr.rd (ω (ei j)) * ∏ r', Or.e r' ^ (-n₁ (some r')))
    (hmet : ∀ (σ : c.F →+* ℂ) (lin : Rul Xo c →ₛₗ[σ] ℂ) (as : Fin n → ℂ),
      ‖∑ j, as j * lin (ω j)‖ ^ 2 ≤
        (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re *
          G.L.h (fun y => lin (ω (ei y.2))) ^ 2)
    (harch : ∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∃ (x0 : Frame ((U σ).X k).Ψ D.R.r)
      (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), IsOrth ((U σ).X k) x0 ∧ IsFundSet ((U σ).X k) x0 FF ∧
      ∀ y ∈ ((U σ).X k).dom, ThA.BergLB ((U σ).X k) x0 FF (laZ (U σ) a₁ k) y (Real.exp (-(A + 3 * rh σ k y))) ∧
        lieFacZ Dw (xiR D) aτ * ((U σ).X k).pnorm (laZ (U σ) aτ k) (rdU (U σ) τ k) y ≤
          Real.exp (4 * (2 * P - rh σ k y) + R₀)) :
    ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y),
      (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 →
      ∃ ρz : ℝ,
        (∀ v : G.I → ℂ, (∀ i, Small.HasVal RM.y (Top.combLine (RM.line 1) n₁).a (G.w i) z (v i)) →
          v ≠ 0 ∧ Real.exp (-(A + 3 * ρz) / 2) * ∏ r', (Or.sing r').h z ^ n₁ (some r') ≤ G.L.h fun x => v x.2) ∧
        Small.ValLe RM.y (Top.combLine (RM.line 1) nτ).a (Fr.rd τ * ∏ r', Or.e r' ^ (-nτ (some r'))) z
          (Real.exp (4 * (2 * P - ρz) + R₀) * ∏ r', (Or.sing r').h z ^ nτ (some r')) ∧
        Small.ValLe RM.y (Top.combLine (RM.line 1) nσ).a (Fr.rd F.s * ∏ r', Or.e r' ^ (-nσ (some r'))) z
          (Real.exp (Real.log (F.cInf σ)) * ∏ r', (Or.sing r').h z ^ nσ (some r')) := by
  obtain ⟨u, hoff, hA⟩ := GlobalTheory.T.component_norm_constant_models hG D.host.E H Dw l Xo c D.R.r U h e hL (xiR D) hLv.xiAbs O β Y SS RM Sys Fx
    Or Fr Z Rd
  refine ⟨u, hoff, fun σ z hz hcst huz => ?_⟩
  obtain ⟨k, hOv, y, hy, hθ⟩ := hA σ z hz hcst huz
  have hgood := goodEmb_goodOf c σ
  obtain ⟨x0, FF, hO, hFS, hB⟩ := harch (goodOf c σ) hgood k hOv
  obtain ⟨hberg, hτle⟩ := hB y hy
  have hzp : z ∈ Small.ptsOver ℂ (mCoordIdeal RM.y) := mem_ptsOver_of_mem_mcPts hz
  set lin : Rul Xo c →ₛₗ[σ] ℂ := linAt σ (U (goodOf c σ)) k y with hlin
  have hlinf : ∀ f, lin f = Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y) := fun f => rfl
  have hread : ∀ (a : WZ D.host.E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) →
      ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw (xiR D) a *
          ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧
        ∀ f ∈ secZ Xo c a, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a
          (Fr.rd f * ∏ r', Or.e r' ^ (-n' (some r'))) z (θ * lin f) := by
    intro a n' hn'
    obtain ⟨θ, h1, h2⟩ := hθ a n' hn'
    refine ⟨θ, h1, fun f hf => ?_⟩
    rw [hlinf]
    by_cases hg : GoodEmb c σ
    · have : Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y) = rdU (U (goodOf c σ)) f k y := by
        simp [Small.goodTwist, hg]
      rw [this]
      exact (h2 f hf).1 hg
    · have : Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y) = starRingEnd ℂ (rdU (U (goodOf c σ)) f k y) := by
        simp [Small.goodTwist, hg]
      rw [this]
      exact (h2 f hf).2 hg
  have hhpos : ∀ nn : Option (RootIx Dw) → ℤ, 0 < ∏ r', (Or.sing r').h z ^ nn (some r') := fun nn =>
    Finset.prod_pos fun r' _ => zpow_pos ((Or.sing r').pos z hz.1) _
  have hωsec : ∀ j, ω j ∈ secZ Xo c a₁ := fun j => by
    have : ω j ∈ cuspOn U h a₁ Z := hspanF ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this.1.1
  refine ⟨rh (goodOf c σ) k y, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨θ, hθn, hf⟩ := hread a₁ n₁ hn₁
    have hvi : ∀ i, v i = θ * lin (ω (ei i)) := fun i =>
      Small.ReadFinTest.hasVal_unique hzp (hv i) (by rw [hGw i]; exact hf _ (hωsec _))
    obtain ⟨hne, hν, hsq⟩ := GlobalTheory.T.sqrt_bergman_lower_bound_le_pnorm_mul_height D H Dw l Xo c U h e W dict hL hLv hFV a₁ Z n ω G.I G.L ei hOnto hspanF σ k y
      lin hlinf (hmet σ lin) hOv hy x0 FF _ hO hFS (Real.exp_pos _) hberg
    have hθpos : 0 < ‖θ‖ := by
      rw [hθn]
      exact mul_pos (mul_pos (hhpos _) (lieFacZ_pos _ _ _)) hν
    have hθ0 : θ ≠ 0 := norm_pos_iff.1 hθpos
    refine ⟨?_, ?_⟩
    · intro h0
      obtain ⟨j, hj⟩ := hne
      have h1 := congrFun h0 (ei.symm j)
      rw [hvi, Pi.zero_apply, Equiv.apply_symm_apply] at h1
      exact (mul_ne_zero hθ0 hj) h1
    · have hLh : G.L.h (fun x => v x.2) = ‖θ‖ * G.L.h (fun x => lin (ω (ei x.2))) := by
        have h1 := G.L.smul (fun _ => θ) (fun x => lin (ω (ei x.2))) (fun _ => hθ0)
        simp only [G.L_deg, zpow_one, Finset.univ_unique, Finset.prod_singleton] at h1
        rw [← h1]
        congr 1
        funext x
        exact hvi x.2
      rw [hLh, hθn, Real.exp_half]
      calc _ ≤ (lieFacZ Dw (xiR D) a₁ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y *
            G.L.h (fun x => lin (ω (ei x.2)))) * ∏ r', (Or.sing r').h z ^ n₁ (some r') :=
            mul_le_mul_of_nonneg_right hsq (hhpos _).le
        _ = _ := by ring
  · intro wv hw
    obtain ⟨θ, hθn, hf⟩ := hread aτ nτ hnτ
    have hwv : wv = θ * lin τ := Small.ReadFinTest.hasVal_unique hzp hw (hf τ hτsec)
    rw [hwv, norm_mul, hθn, hlinf, Small.norm_goodTwist]
    rw [pnorm_eq_mul] at hτle
    calc _ = (∏ r', (Or.sing r').h z ^ nτ (some r')) * (lieFacZ Dw (xiR D) aτ *
          (‖rdU (U (goodOf c σ)) τ k y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) aτ k) (fun _ => 1) y)) := by ring
      _ ≤ (∏ r', (Or.sing r').h z ^ nτ (some r')) * Real.exp (4 * (2 * P - rh (goodOf c σ) k y) + R₀) :=
          mul_le_mul_of_nonneg_left hτle (hhpos _).le
      _ = _ := mul_comm _ _
  · intro wv hw
    obtain ⟨θ, hθn, hf⟩ := hread (flatZ H w) nσ hnσ
    have hwv : wv = θ * lin F.s := Small.ReadFinTest.hasVal_unique hzp hw (hf F.s F.s_sec)
    have hinf := F.inf_eq (goodOf c σ) hgood k hOv y hy
    rw [pnorm_eq_mul, ← F.cInf_good σ] at hinf
    rw [hwv, norm_mul, hθn, hlinf, Small.norm_goodTwist, Real.exp_log (F.cInf_pos σ), ← hinf]
    exact le_of_eq (by ring)

end ArchD

section Emb

theorem embMean_comp {F₁ F₂ : Type} [Field F₁] [NumberField F₁] [Field F₂] [NumberField F₂] (ψ : F₁ ≃+* F₂)
    (g : (F₁ →+* ℂ) → ℝ) :
    Small.embMean (fun sg : F₂ →+* ℂ => g (sg.comp (ψ : F₁ →+* F₂))) = (∑ σ, g σ) / Module.finrank ℚ F₁ := by
  let eq : (F₂ →+* ℂ) ≃ (F₁ →+* ℂ) :=
    { toFun := fun sg => sg.comp (ψ : F₁ →+* F₂)
      invFun := fun σ => σ.comp (ψ.symm : F₂ →+* F₁)
      left_inv := fun sg => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have hc : Fintype.card (F₂ →+* ℂ) = Module.finrank ℚ F₁ := by
    rw [Fintype.card_congr eq, NumberField.Embeddings.card F₁ ℂ]
  unfold Small.embMean
  rw [hc]
  congr 1
  exact Equiv.sum_comp eq g

end Emb

end GlobalTheory.CompanionTheory.Ar.Rec.OS

namespace GlobalTheory.CompanionTheory.Ar.Rec

open OS in

theorem origin_small : Top.Given → ∀ (D : D7), IsGalois ℚ D.host.E → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → Ref.UnifAll Xo c → ∀ [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b₀)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (a₁ a' aτ : WZ D.host.E) (w : CMType H → ℤ) (F : FlatSec U (xiR D) (e Z) (flatZ H w)) (μ m : ℕ) (τ : Rul Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (n₁ : Option (RootIx Dw) → ℤ) (Λ : ℝ) (G : Small.GenModel (T.M B b₀) Λ) (ei : G.I ≃ Fin n) (ψ : c.F ≃+* G.F) (S : Finset ℕ) (ep bτ b cp : ℕ → ℝ) (c₀ ρ A P R₀ cinf cc : ℝ) (rh : ∀ σ k, Frame ((U σ).X k).Ψ D.R.r → ℝ), 0 < μ → Top.RegDominant (towerWt Dw a') → WEq Dw ((8 * μ) • a₁) ((8 * μ) • a' + (3 * μ) • aτ + m • flatZ H w) → τ ∈ secZ Xo c aτ → evC h Z τ ≠ 0 → OntoZ U h e a₁ Z → Submodule.span ℤ (Set.range ω) = (latOn U h a₁ Z).restrictScalars ℤ → Submodule.span c.F (Set.range ω) = cuspOn U h a₁ Z → (∀ j, (n₁ j : ℝ) = (T.M B b₀).coef (towerWt Dw a₁) 0 j) → (∀ t, algebraMap G.F (T.M B b₀).Ω (ψ t) = (o.toTowerOrigin.Or B b₀).𝔐.cst t) → (∀ j, G.w j = Fr.rd (ω (ei j)) * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-n₁ (some r'))) → (∀ (σ : c.F →+* ℂ) (lin : Rul Xo c →ₛₗ[σ] ℂ) (as : Fin n → ℂ), ‖∑ j, as j * lin (ω j)‖ ^ 2 ≤ (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re * G.L.h (fun y => lin (ω (ei y.2))) ^ 2) → c₀ ≤ 3 * ρ → (∀ (p : ℕ), p.Prime → ∀ la : HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ la.asIdeal → (Ref.pjSys Xo c).RefBound (cuspZ Xo c U a₁) la (ramOverZ la * ep p) c₀ (Ref.phU Xo c la) ∧ -F.cFin la ≤ ramOverZ la * b p ∧ ∀ y : (Ref.pjSys Xo c).Pt la, 0 ≤ Ref.phU Xo c la y ∧ ((8 * ρ * Ref.phU Xo c la y - ramOverZ la * bτ p : ℝ) : EReal) ≤ (Ref.pjSys Xo c).val y τ) → (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ cp p) → (∀ p, p ∉ S → cp p = 0) → (∀ p : ℕ, p.Prime → (((8 * μ : ℕ) : ℝ) * (ep p + (if p ∈ o.toTowerOrigin.S B then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr D.host.E) : ℝ) / Module.finrank ℚ D.host.E else 0) * Top.l1 (towerWt Dw a')) + ((3 * μ : ℕ) : ℝ) * bτ p + m * b p) * Real.log p ≤ ((8 * μ : ℕ) : ℝ) * cp p) → (∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∃ (x0 : Frame ((U σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), IsOrth ((U σ).X k) x0 ∧ IsFundSet ((U σ).X k) x0 FF ∧ ∀ y ∈ ((U σ).X k).dom, ThA.BergLB ((U σ).X k) x0 FF (laZ (U σ) a₁ k) y (Real.exp (-(A + 3 * rh σ k y))) ∧ lieFacZ Dw (xiR D) aτ * ((U σ).X k).pnorm (laZ (U σ) aτ k) (rdU (U σ) τ k) y ≤ Real.exp (4 * (2 * P - rh σ k y) + R₀)) → ((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ + m * ((∑ σ : c.F →+* ℂ, Real.log (F.cInf σ)) / Module.finrank ℚ c.F) ≤ ((8 * μ : ℕ) : ℝ) * cinf → ∑ p ∈ S, cp p + cinf ≤ cc → G.HasInputs (T.lamS (towerWt Dw a')) cc := by
  intro hG D hGal H Dw l Xo c U h e W dict hL hLv hFV hU _ Y T o B b₀ Fr Z Rd a₁ a' aτ w F μ m τ n ω n₁ Λ G ei ψ S ep bτ b cp
    c₀ ρ A P R₀ cinf cc rh hμ hreg hWE hτsec hτne hOnto hspanZ hspanF hn₁ hψ hGw hmet hc₀ hfin hSp hcp0 hcpS hcpge harch
    hcinf hcc
  have hn₁z : n₁ = zc Dw a₁ := funext fun j => by
    have h1 := hn₁ j
    rw [← zc_coef Dw (T.M B b₀) a₁ j] at h1
    exact_mod_cast h1
  subst hn₁z
  have hrel := zc_lin Dw a₁ a' aτ (flatZ H w) μ m hWE
  have hc1 := zc_coef Dw (T.M B b₀) a₁
  have hc' := zc_coef Dw (T.M B b₀) a'
  have hcτ := zc_coef Dw (T.M B b₀) aτ
  have hcσ := zc_coef Dw (T.M B b₀) (flatZ H w)
  obtain ⟨q₀, n₀, ε, u₄, C, s₀, hq₀, hn₀, hε0, hεint, hu₄, hC, hs₀, hA5⟩ :=
    GlobalTheory.T.good_origin_root_weight_bound D.host.E H Dw l Xo c Y T o B b₀ (towerWt Dw a') (zc Dw a') hc' hreg
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr D.host.E → p ∈ o.toTowerOrigin.S B := by
    intro p hp hd
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ?_⟩
    rw [o.toTowerOrigin.bad_iff]
    exact ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  haveI := hGal
  obtain ⟨uF, huF, hFB⟩ := fin_bounds hG U h e hL hU Y (o.toTowerOrigin.S B) (T.M B b₀) (o.toTowerOrigin.Sys b₀)
    (o.toTowerOrigin.Fx b₀) (o.toTowerOrigin.Or B b₀) Fr Z Rd (o.omVB B b₀) hdisc a₁ a' aτ w F μ m τ n ω (zc Dw a₁)
    (zc Dw a') (zc Dw aτ) (zc Dw (flatZ H w)) Λ G ei ep bτ b c₀ ρ hc1 hc' hcτ hcσ hrel hτsec hspanZ hGw hc₀ hfin
  obtain ⟨uA, huA, hAB⟩ := arch_bounds hG U h e W dict hL hLv hFV Y (o.toTowerOrigin.S B) (T.M B b₀)
    (o.toTowerOrigin.Sys b₀) (o.toTowerOrigin.Fx b₀) (o.toTowerOrigin.Or B b₀) Fr Z Rd a₁ aτ w F τ n ω (zc Dw a₁)
    (zc Dw aτ) (zc Dw (flatZ H w)) Λ G ei A P R₀ rh hc1 hcτ hcσ hτsec hOnto hspanF hGw hmet harch
  obtain ⟨uC, huC, hCst⟩ := GlobalTheory.T.generic_form_valuation_embedding (T.M B b₀).K (T.M B b₀).ι (T.M B b₀).Ω (T.M B b₀).y G.F
    (T.M B b₀).birational (T.M B b₀).arith.2.1.2.2
  have hmulOff : ∀ u v : MRing (T.M B b₀).ι, Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u →
      Small.IsFormOff (mCoordIdeal (T.M B b₀).y) v → Small.IsFormOff (mCoordIdeal (T.M B b₀).y) (u * v) :=
    fun u v hu hv => GlobalTheory.T.form_off_variety_mul _ _ _ _ _ _ _ (T.M B b₀).arith hu hv
  have hu : Small.IsFormOff (mCoordIdeal (T.M B b₀).y) (u₄ * (uF * (uA * uC))) :=
    hmulOff _ _ hu₄ (hmulOff _ _ huF (hmulOff _ _ huA huC))
  have huz : ∀ z : (Σ k, (T.M B b₀).ι k) → ℂ, MvPolynomial.aeval z (u₄ * (uF * (uA * uC))) ≠ 0 →
      MvPolynomial.aeval z u₄ ≠ 0 ∧ MvPolynomial.aeval z uF ≠ 0 ∧ MvPolynomial.aeval z uA ≠ 0 ∧
        MvPolynomial.aeval z uC ≠ 0 := by
    intro z hz
    simp only [map_mul, mul_ne_zero_iff] at hz
    exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩
  have hτne' : Fr.rd τ * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-zc Dw aτ (some r')) ≠ 0 := by
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun r' _ => zpow_ne_zero _ ((o.toTowerOrigin.Or B b₀).lines r').1)
    rw [Rd.rd_eq aτ τ hτsec]
    exact mul_ne_zero (Units.ne_zero _) ((map_ne_zero Rd.φ).2 hτne)
  have hσne' : Fr.rd F.s * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-zc Dw (flatZ H w) (some r')) ≠ 0 := by
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun r' _ => zpow_ne_zero _ ((o.toTowerOrigin.Or B b₀).lines r').1)
    intro h0
    have h1 : Fr.rd (e Z) = Fr.rd F.s * Fr.rd F.s' := by
      have h9 := Fr.rd_mul F.s F.s'
      rw [F.mul_eq] at h9
      exact h9
    rw [h0, zero_mul] at h1
    have h2 : e Z ∈ secZ Xo c (0 : WZ D.host.E) := by
      have := (hL.e_sec Z)
      rw [← secZ_nat Xo c 0] at this
      exact this
    have h3 := Rd.rd_eq 0 (e Z) h2
    rw [h1, (hL.e_val Z).1, map_one, mul_one] at h3
    exact Units.ne_zero _ h3.symm
  let κ : (G.F →+* ℂ) → ℝ := fun sg => Real.log (F.cInf (sg.comp (ψ : c.F →+* G.F)))
  have hκ : ∀ sg, κ (NumberField.ComplexEmbedding.conjugate sg) = κ sg := by
    intro sg
    have e1 : (NumberField.ComplexEmbedding.conjugate sg).comp (ψ : c.F →+* G.F) =
        (starRingEnd ℂ).comp (sg.comp (ψ : c.F →+* G.F)) := by
      ext x
      simp
    show Real.log _ = Real.log _
    rw [e1, F.cInf_good, goodOf_conj', ← F.cInf_good]
  let hN : (Option (RootIx Dw) → ℤ) → ((Σ k, (T.M B b₀).ι k) → ℂ) → ℝ := fun nn z =>
    ∏ r', ((o.toTowerOrigin.Or B b₀).sing r').h z ^ nn (some r')
  have hρ : ∀ z : (Σ k, (T.M B b₀).ι k) → ℂ, ∃ ρz : ℝ, ∀ sg : G.F →+* ℂ, z ∈ mcPts (mCoordIdeal (T.M B b₀).y) →
      LiesOver (T.M B b₀).y sg z → MvPolynomial.aeval z (u₄ * (uF * (uA * uC))) ≠ 0 →
      (∀ v : G.I → ℂ, (∀ i, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) (zc Dw a₁)).a (G.w i) z (v i)) →
        v ≠ 0 ∧ Real.exp (-(A + 3 * ρz) / 2) * hN (zc Dw a₁) z ≤ G.L.h fun x => v x.2) ∧
      Small.ValLe (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) (zc Dw aτ)).a
        (Fr.rd τ * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-zc Dw aτ (some r'))) z
        (Real.exp (4 * (2 * P - ρz) + R₀) * hN (zc Dw aτ) z) ∧
      Small.ValLe (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) (zc Dw (flatZ H w))).a
        (Fr.rd F.s * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-zc Dw (flatZ H w) (some r'))) z
        (Real.exp (κ sg) * hN (zc Dw (flatZ H w)) z) := by
    intro z
    by_cases hex : ∃ sg : G.F →+* ℂ, z ∈ mcPts (mCoordIdeal (T.M B b₀).y) ∧ LiesOver (T.M B b₀).y sg z ∧
        MvPolynomial.aeval z (u₄ * (uF * (uA * uC))) ≠ 0
    · obtain ⟨sg₀, hz, hl₀, hu₀⟩ := hex
      obtain ⟨-, -, hA0, hC0⟩ := huz z hu₀
      have hzp := mem_ptsOver_of_mem_mcPts hz
      obtain ⟨φ, hφ⟩ := hCst ℂ z hzp hC0
      have hφeq : ∀ sg : G.F →+* ℂ, LiesOver (T.M B b₀).y sg z → sg = φ := fun sg hl => by
        ext θ
        exact (Small.hasVal_const hl (hφ θ)).symm
      have hcst : ∀ t : c.F, Small.HasVal (T.M B b₀).y 0 ((o.toTowerOrigin.Or B b₀).𝔐.cst t) z
          ((sg₀.comp (ψ : c.F →+* G.F)) t) := by
        intro t
        have := hφ (ψ t)
        rw [hψ t, ← hφeq sg₀ hl₀] at this
        exact this
      obtain ⟨ρz, h1, h2, h3⟩ := hAB (sg₀.comp (ψ : c.F →+* G.F)) z hz hcst hA0
      refine ⟨ρz, fun sg _ hl _ => ?_⟩
      obtain rfl : sg = sg₀ := (hφeq sg hl).trans (hφeq sg₀ hl₀).symm
      exact ⟨h1, h2, h3⟩
    · refine ⟨0, fun sg hz hl hu' => absurd ⟨sg, hz, hl, hu'⟩ hex⟩
  choose ρf hρf using hρ
  have hNpos : ∀ (nn : Option (RootIx Dw) → ℤ) (z : (Σ k, (T.M B b₀).ι k) → ℂ), z ∈ mcPts (mCoordIdeal (T.M B b₀).y) →
      0 < hN nn z := fun nn z hz =>
    Finset.prod_pos fun r' _ => zpow_pos (((o.toTowerOrigin.Or B b₀).sing r').pos z hz.1) _
  refine Small.hasInputs_of_data (CMType H) (Dw.p + Dw.q) (T.M B b₀) Λ G (towerWt Dw a') T.nu (zc Dw a') n₀ q₀ μ m
    (Top.combLine ((T.M B b₀).line 1) (zc Dw a₁)).a (Top.combLine ((T.M B b₀).line 1) (zc Dw aτ)).a
    (Top.combLine ((T.M B b₀).line 1) (zc Dw (flatZ H w))).a
    (Fr.rd τ * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-zc Dw aτ (some r')))
    (Fr.rd F.s * ∏ r', (o.toTowerOrigin.Or B b₀).e r' ^ (-zc Dw (flatZ H w) (some r')))
    ε (u₄ * (uF * (uA * uC))) S ep
    (fun p => (if p ∈ o.toTowerOrigin.S B then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) +
      (padicValInt p (discr D.host.E) : ℝ) / Module.finrank ℚ D.host.E else 0) * Top.l1 (towerWt Dw a') + 3 * bτ p / 8)
    b cp A P R₀ cinf cc C s₀ κ (hN (zc Dw a₁)) (hN (zc Dw a')) (hN (zc Dw aτ)) (hN (zc Dw (flatZ H w))) ρf
    hq₀ hμ hc' hn₀ ?_ hτne' hσne' hε0 hεint hu hSp hcp0 hcpS ?_ ?_ hκ ?_ hC hs₀ ?_ ?_ hcc
  · intro x
    simp only [Small.combLine_line_a (T.M B b₀) 1, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hrel j]
    ring
  · intro p hp
    refine le_trans (le_of_eq ?_) (hcpge p hp)
    push_cast
    ring
  · intro p _ z hz hzu
    refine hFB p z hz ?_
    simp only [map_mul, mul_ne_zero_iff] at hzu
    exact hzu.2.1
  · intro sg z hz hl hu'
    obtain ⟨h1, h2, h3⟩ := hρf z sg hz hl hu'
    refine ⟨hNpos _ z hz, hNpos _ z hz, hNpos _ z hz, hNpos _ z hz, ?_, h1, h2, h3⟩
    exact prod_rel _ (fun r' => ((o.toTowerOrigin.Or B b₀).sing r').pos z hz.1) (fun r' => zc Dw a₁ (some r'))
      (fun r' => zc Dw a' (some r')) (fun r' => zc Dw aτ (some r')) (fun r' => zc Dw (flatZ H w) (some r'))
      (8 * μ) (3 * μ) m (fun r' => hrel (some r'))
  · intro s hs hss z hz hzu x hx hx0
    exact hA5 s hs hss z hz (huz z hzu).1 x hx hx0
  · have hm : Small.embMean κ = (∑ σ : c.F →+* ℂ, Real.log (F.cInf σ)) / Module.finrank ℚ c.F :=
      embMean_comp ψ (fun σ => Real.log (F.cInf σ))
    rw [hm]
    exact hcinf

end GlobalTheory.CompanionTheory.Ar.Rec
