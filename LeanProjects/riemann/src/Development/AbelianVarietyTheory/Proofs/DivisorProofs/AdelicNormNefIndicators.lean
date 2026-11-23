import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalImpliesGeometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringPrintsAnyLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStatementHoldsStatement

set_option autoImplicit false

noncomputable section

section Moduli

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel

namespace GlobalTheory.DetHT

theorem detConst_of (hT : TestPtSt) (hX : ExFrameSt) (hP : PointSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [IsGalois ℚ E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hpq : 1 ≤ Dw.p + Dw.q) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (Zc : Formalism.L2.Pj.Comp Xo c)
    (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (h : ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal)) : DetConst Z Zc τ.1 f := by
  intro la p _
  obtain ⟨ρ, hρ⟩ := h la
  obtain ⟨K, hK⟩ := hP E H Dw τ p
  refine ⟨ρ * Real.log ((Valued.v : Valuation ℂ_[p] ℝ≥0) (p : ℂ_[p])) / (vLa la (p : c.F) : ℝ) + K, fun hla P hA hZ => ?_⟩
  obtain ⟨yb, hyb⟩ := hT E H Dw l Xo c Z p P hA
  obtain ⟨y, hy, hyP, Q, π, ψ, z, hQ, hz⟩ := hX E H Dw l Xo c hpq Z Zc la p hla P yb hyb hZ
  have h1 : val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y) = (ρ : EReal) := hρ _ hy
  have h0 : evR Xo c f y ≠ 0 := fun e => by
    rw [e, val_vw_zero] at h1
    exact EReal.coe_ne_top ρ h1.symm
  obtain ⟨h2, h3⟩ := hK l Xo c Z f hf P y z yb hyP Q π ψ hQ hz h0
  refine ⟨h2, h3.trans (congrArg (· + K) ?_)⟩
  rw [val_vw_of_ne la p _ h0, EReal.coe_eq_coe_iff, coe_valued, coe_valued] at h1
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← coe_valued]
    exact_mod_cast lt_one_of_not_isUnit (PadicComplexInt.integers p) (PadicComplexHost.not_isUnit_p p)
  have hl : Real.log ‖(p : ℂ_[p])‖ ≠ 0 := (Real.log_neg (norm_pos_iff.2 hp0) hp1).ne
  have hv : (vLa la (p : c.F) : ℝ) ≠ 0 := by
    have hc : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hne : la.valuation c.F (p : c.F) ≠ 1 := fun e => by
      have := (hla (p : c.F)⁻¹).2 (by rw [map_inv₀, e, inv_one])
      rw [map_inv₀, map_natCast, norm_inv] at this
      exact absurd (one_lt_inv₀ (norm_pos_iff.2 hp0) |>.2 hp1) this.not_gt
    have h0' : la.valuation c.F (p : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    rw [Int.cast_ne_zero, vLa, neg_ne_zero]
    intro e
    exact hne (by rw [← WithZero.exp_log h0', e, WithZero.exp_zero])
  rw [coe_valued, ← h1]
  field_simp

end GlobalTheory.DetHT

end Moduli

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

namespace GlobalTheory.DetHT

theorem valAt_stalk {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : GlobalTheory.Cartier.RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [GlobalTheory.TrueGeo.valAt, dif_pos h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

theorem valAt_inv_of_unit {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {g : Z.functionField}
    (h : GlobalTheory.Cartier.UnitAt (below y) g) : valAt y g⁻¹ = (valAt y g)⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨u, rfl⟩ := ha
  rw [← map_units_inv, valAt_stalk, valAt_stalk, map_units_inv]

theorem log_w_valAt_inv {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (y : AlgPt Y) {g : Y.Fn} (h : GlobalTheory.Cartier.UnitAt (below y.1) g) :
    Real.log (e.w (valAt y.1 g⁻¹)) = -Real.log (e.w (valAt y.1 g)) := by
  rw [valAt_inv_of_unit y.1 h, map_inv₀, Real.log_inv]

theorem nefOver_det_of (hG : GeoSt) (hA : AnyLevSt) (hT : TestPtSt) (hX : ExFrameSt) (hP : PointSt) (hF : FlagSt) :
    OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l := by
  intro D O _ _ _ _ _ _ c Q l hlQ hl V M hM τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hpq : 1 ≤ O.S.Dw.p + O.S.Dw.q := (one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D O.A O.N O.j O.S O.κ O.s O.Φ
  let τ' : Psi O.A.H := ⟨DV.tauEmb D τ, O.A.cm τ⟩
  obtain ⟨f, hf, hc⟩ := hA _ O.A.H O.S.Dw O.κ.l O.s.Xo O.κ.c hpq O.κ.good
    (GlobalTheory.RankOneDatum.exists_datum_of_rt D O.A.H O.A.rt_eq O.A.cmHost_rootComplex_eq_pm_sqrt) O.κ.curve (q c) τ'
  have hD := detConst_of hT hX hP hpq O.s.T.Z (q c) τ' hf hc
  have key := hF _ O.A.H O.S.Dw O.κ.l O.s.Xo O.κ.c O.s.T.Z _ O.κ.e (O.Φ.C c) (q c) τ' f hf (hq c) hD O.N O.S.rank_eq
    (GlobalTheory.ShFam.Pad.ArIn.ind Q) none
  let W : (O.var c).X.Opens := (O.Φ.C c).π ⁻¹ᵁ (GlobalTheory.Toroidal.genBd O.s.T.Z).compl
  have hW : (W : Set (O.var c).X).Nonempty := by
    letI := (GlobalTheory.ShFam.constF O.κ.e (O.Φ.C c).Y).toAlgebra
    refine ⟨genericPoint _, fun h => h ⟨GlobalTheory.AllWt.ptF (O.Φ.C c).y0 (IsLocalRing.closedPoint _), ?_⟩⟩
    have := congrArg (fun g : Sp (O.var c).Fn ⟶ _ => g (IsLocalRing.closedPoint (O.var c).Fn)) (O.Φ.C c).y0_x
    simp only [Scheme.Hom.comp_apply] at this
    refine this.trans (congrArg (O.Φ.C c).π ?_)
    exact Scheme.fromSpecStalk_closedPoint
  have hv : ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (l : 𝓞 D.what₂.LL) ∈ v.asIdeal →
      GlobalTheory.ShFam.Pad.ArIn.ind Q (resP v) = true := fun v hv => by
    simp [GlobalTheory.ShFam.Pad.ArIn.ind, (GlobalTheory.PlaceSum.residueCharacteristic_eq_iff v hl).2 hv, hlQ]
  have e₁ (n : ℤ) (z : (O.var c).X) : ∏ x : DV.Rt D.what₂.Tau O.N, genAt (O.root0 c Q x).D z ^ (if x.1 = τ then n else 0) =
      (∏ i : Fin O.N, genAt (divOf (O.Φ.C c) (expo O.S.Dw (rootSym O.S.Dw (GlobalTheory.ShFam.Pad.ArIn.ind Q) none τ'.1 i))) z) ^ n := by
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), ← Finset.prod_zpow]
    simp only [if_true]
    rfl
  have e₂ (n : ℤ) (v e y) : ∑ x : DV.Rt D.what₂.Tau O.N, ((if x.1 = τ then n else 0 : ℤ) : ℝ) * (O.root0 c Q x).lg v e y =
      n * ∑ i : Fin O.N, lgOf (O.Φ.C c) (rootSym O.S.Dw (GlobalTheory.ShFam.Pad.ArIn.ind Q) none τ'.1 i) v e y := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), Finset.mul_sum]
    simp only [if_true]
    rfl
  constructor
  · refine hG _ _ V _ _ _ _ (norms_comb hM _) ((O.Φ.C c).val f) W hW l hl fun v h => ?_
    obtain ⟨ρ, hρ⟩ := key v (hv v h)
    refine ⟨ρ, fun e y hy => ?_⟩
    rw [e₁, e₂, zpow_one, Int.cast_one, one_mul]
    exact hρ e y hy
  · refine hG _ _ V _ _ _ _ (norms_comb hM _) ((O.Φ.C c).val f)⁻¹ W hW l hl fun v h => ?_
    obtain ⟨ρ, hρ⟩ := key v (hv v h)
    refine ⟨-ρ, fun e y hy => ?_⟩
    obtain ⟨h₁, h₂⟩ := hρ e y hy
    rw [e₁, e₂, zpow_neg_one, inv_div_inv, ← inv_div, Int.cast_neg, Int.cast_one, neg_one_mul]
    refine ⟨h₁.inv, ?_⟩
    rw [log_w_valAt_inv e y h₁]
    linarith

theorem nefOver_det :
    Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l :=
  fun hP _ => nefOver_det_of (GlobalTheory.T.regular_local_implies_geometric GlobalTheory.T.RegularLocalStatement) (GlobalTheory.T.anyLevSt_of_covering hP) GlobalTheory.T.TestPointStatement GlobalTheory.T.ExistsFrameStatement
    (GlobalTheory.T.point_count_of_eigen_covolume_hypotheses GlobalTheory.T.ConnectingStatement GlobalTheory.T.EigenvalueStatement GlobalTheory.T.CovolumeStatement) GlobalTheory.T.flag_statement_holds

end GlobalTheory.DetHT

end
