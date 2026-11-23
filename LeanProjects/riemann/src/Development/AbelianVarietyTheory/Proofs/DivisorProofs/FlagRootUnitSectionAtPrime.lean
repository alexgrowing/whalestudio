import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeLinearRootSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringPrintsAnyLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfCoverUnitAtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
import Development.AbelianVarietyTheory.BlockTheory.GoodPlaces.RamifiedPlaceAnyLevel
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarmonicValueIntegrality

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ArDegIndep.TieOther

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTConstRoot

theorem extend {F : Type} [Field F] [NumberField F] {Y : Var F} (V : GlobalTheory.Mean4O.Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, TrueGeo.Pts Y σ → ℝ) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    (hN : Norms V L f a lg) (s : Y.Fn) (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    (hp : p.Prime) (hpv : (p : 𝓞 F) ∈ v.asIdeal) (ρ₀ : ℝ)
    (H : ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W → UnitAt (below y.1) (s / f (below y.1)) ∧
      Real.log (e.w (TrueGeo.valAt y.1 (s / f (below y.1)))) + lg v e y = ρ₀) :
    (∀ x : Y.X, UnitAt x (s / f x)) ∧ ∀ (e : TrueGeo.Ext v) (y : AlgPt Y),
      Real.log (e.w (TrueGeo.valAt y.1 (s / f (below y.1)))) + lg v e y = ρ₀ := by
  obtain ⟨r, -, hu, -, hf⟩ := hN
  have := CoverHt.isPreimmersion_j V
  have hP : IsProper V.p := by
    obtain ⟨N, j, hj, he⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← he]; infer_instance
  have hη := GlobalTheory.CoverNorm.Isom.j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), TrueGeo.valAt (y ≫ V.j) g = TrueGeo.valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hreg : ∀ (x : V.G) (g : V.X.functionField), RegAt x (ρ g) ↔ RegAt (V.j x) g :=
    fun x g => SmallSec.regAt_fnMap_iff V.j hη
  have hun : ∀ (x : V.G) (g : V.X.functionField), UnitAt x (ρ g) ↔ UnitAt (V.j x) g := by
    intro x g
    by_cases h0 : g = 0
    · subst h0
      exact ⟨fun h => absurd (map_zero ρ) h.ne_zero, fun h => absurd rfl h.ne_zero⟩
    · rw [unitAt_iff h0, unitAt_iff ((map_ne_zero ρ).2 h0), ← map_inv₀, hreg, hreg]
  obtain ⟨t, ht, htW⟩ := V.j.isEmbedding.isInducing.isOpen_iff.1 (V.π ⁻¹ᵁ W).isOpen
  obtain ⟨w, hw⟩ := V.π.surjective (genericPoint Y.X)
  have hmemt : ∀ x : V.G, V.j x ∈ t ↔ V.π x ∈ W := fun x => Set.ext_iff.1 htW x

  have key : ∀ (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (i : L.B.ι),
      z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U i → UnitAt (below y.1) (s / f (below y.1)) →
      UnitAt (below z) (V.φ s * (r fun _ => i : V.G.functionFieldˣ)) ∧
      Real.log (e.w (TrueGeo.valAt z (V.φ s * (r fun _ => i : V.G.functionFieldˣ)))) =
        Real.log (e.w (TrueGeo.valAt y.1 (s / f (below y.1)))) + lg v e y := by
    intro e y z yt i hz hyt hU hs
    have h1 : (spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ yt ⁻¹ᵁ L.B.U i := hU trivial
    have h2 : (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ L.B.U i := by
      rw [← hyt]; exact h1
    have hb : V.π (below z) = below y.1 := by rw [← hz]; rfl
    have u₁ := hu (fun _ => i) (below z) (Set.mem_iInter.2 fun _ => h2)
    rw [hb] at u₁
    have hs' : UnitAt (V.π (below z)) (s / f (below y.1)) := hb ▸ hs
    have u₂ := V.unitAt_φ hs'
    have h0 : V.φ (f (below y.1)) ≠ 0 := left_ne_zero_of_mul u₁.ne_zero
    have e₁ : V.φ s * (r fun _ => i : V.G.functionFieldˣ) =
        V.φ (s / f (below y.1)) * (V.φ (f (below y.1)) * (r fun _ => i : V.G.functionFieldˣ)) := by
      rw [map_div₀, ← mul_assoc, div_mul_cancel₀ _ h0]
    refine ⟨e₁ ▸ u₂.mul u₁, ?_⟩
    rw [e₁, SmallSec.valAt_mul u₂.regAt u₁.regAt, map_mul,
      Real.log_mul (e.w.ne_zero (SmallSec.valAt_ne_zero u₂)) (e.w.ne_zero (SmallSec.valAt_ne_zero u₁)),
      V.valAt_φ z hs'.regAt, hz, hf v e y z yt (fun _ => i) hz hyt hU]
  have K := fun i : L.B.ι => GlobalTheory.T.unit_at_points_over_prime_bound GlobalTheory.T.RegularLocalStatement F Y V (L.B.U i) ⟨t, ht⟩ ⟨V.j w, (hmemt w).2 (hw ▸ hW)⟩ v p hp hpv
    (ρ.symm (V.φ s * (r fun _ => i : V.G.functionFieldˣ))) ρ₀ (by
      intro e z yt hz hyt hU hzW
      let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
      obtain ⟨a₁, a₂⟩ := H e y ((hmemt (below z)).1 hzW)
      obtain ⟨b₁, b₂⟩ := key e y z yt i rfl hyt hU a₁
      refine ⟨(hun (below z) _).1 (by rwa [ρ.apply_symm_apply]), ?_⟩
      rw [hv, ρ.apply_symm_apply, b₂, a₂])
  have chart (x : V.X) : ∃ i, x ∈ L.B.U i := TopologicalSpace.Opens.mem_iSup.1 (L.isLB.cover.ge (Set.mem_univ _))
  have hall : ∀ x : Y.X, UnitAt x (s / f x) := by
    intro x
    refine GlobalTheory.T.unitAt_of_cover_unitAt F Y V _ x fun x' hx' => ?_
    have hsp : V.p (V.j x') ⤳ (⟨v.asIdeal, v.isPrime⟩ : PrimeSpectrum (𝓞 F)) :=
      (PrimeSpectrum.le_iff_specializes _ _).1
        ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 ((GlobalTheory.CoverNorm.Isom.asIdeal_p_j V x').le.trans bot_le))
    obtain ⟨x₀, hx₀, hx₀'⟩ := V.p.isClosedMap.specializingMap hsp
    obtain ⟨i, hi⟩ := chart x₀
    have u₁ := (K i).1 x' x₀ hi (congrArg PrimeSpectrum.asIdeal hx₀') hx₀
    rw [← hun, ρ.apply_symm_apply] at u₁
    have hi' : V.j x' ∈ L.B.U i := Specializes.mem_open hx₀ (L.B.U i).isOpen hi
    have u₂ := hu (fun _ => i) x' (Set.mem_iInter.2 fun _ => hi')
    rw [hx'] at u₂
    have e₁ : V.φ (s / f x) = (V.φ s * (r fun _ => i : V.G.functionFieldˣ)) *
        (V.φ (f x) * (r fun _ => i : V.G.functionFieldˣ))⁻¹ := by
      rw [map_div₀, ← div_eq_mul_inv, mul_div_mul_right _ _ (Units.ne_zero _)]
    rw [e₁]
    exact u₁.mul u₂.inv
  refine ⟨hall, fun e y => ?_⟩
  obtain ⟨z, hz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1
  obtain ⟨yt, hyt, hU⟩ := V.exists_valuationRing_point e y z hz
  obtain ⟨i, hi⟩ := chart (yt (IsLocalRing.closedPoint e.O))
  have h₁ := ((K i).2 e z yt (by rw [← Category.assoc, hz]; exact y.2) hyt (hU _ hi)).2
  rw [hv, ρ.apply_symm_apply, (key e y z yt i hz hyt (hU _ hi) (hall _)).2] at h₁
  exact h₁

open GlobalTheory.DetHT in

theorem exists_detConst (hP : Hypotheses2) {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h1 : 1 ≤ Dw.p + Dw.q)
    (hg : ∀ q : ℕ, q.Prime → l.GoodAt q) (hD : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (hC : GlobalTheory.CompRat.CurveOver H c.F l.M')
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H) :
    ∃ f ∈ secZ Xo c (exOf Dw (GlobalTheory.FlatLine.flatWt Dw τ) 0), DetConst Z Zc τ.1 f := by
  obtain ⟨f, hf, hρ⟩ := GlobalTheory.T.anyLevSt_of_covering hP E H Dw l Xo c h1 hg hD hC Zc τ
  refine ⟨f, hf, fun la p _ => ?_⟩
  obtain ⟨ρ₀, hρ₀⟩ := hρ la
  obtain ⟨K, hK⟩ := GlobalTheory.T.point_count_of_eigen_covolume_hypotheses GlobalTheory.T.ConnectingStatement GlobalTheory.T.EigenvalueStatement GlobalTheory.DetHT.Covol.covol E H Dw τ p
  refine ⟨ρ₀ * Real.log ‖(p : ℂ_[p])‖ / (vLa la (p : c.F) : ℝ) + K, fun hla P hPa hPZ => ?_⟩
  obtain ⟨yb, hyb⟩ := GlobalTheory.T.TestPointStatement E H Dw l Xo c Z p P hPa
  obtain ⟨y, hy, hyP, Q, π, ψ, z, hpt, hch⟩ := exFrameSt_holds E H Dw l Xo c h1 Z Zc la p hla P yb hyb hPZ
  have h₀ := hρ₀ _ hy
  have hne : evR Xo c f y ≠ 0 := fun h => by
    rw [h, val_vw_zero] at h₀
    exact EReal.coe_ne_top _ h₀.symm
  obtain ⟨k₁, k₂⟩ := hK l Xo c Z f hf P y z yb hyP Q π ψ hpt hch hne
  refine ⟨k₁, ?_⟩
  rw [k₂]
  rw [val_vw_of_ne _ _ _ hne, EReal.coe_eq_coe_iff] at h₀
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hlog : Real.log ‖(p : ℂ_[p])‖ ≠ 0 := (Real.log_neg (norm_pos_iff.2 hp0) hp1).ne
  have hvl : (vLa la (p : c.F) : ℝ) ≠ 0 := by
    intro h
    have hq : la.valuation c.F (p : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
    have h₁ : (la.valuation c.F (p : c.F)).log = 0 := neg_eq_zero.1 (Int.cast_eq_zero.1 h)
    have h₂ : la.valuation c.F (p : c.F) = 1 := by rw [← WithZero.exp_log hq, h₁, WithZero.exp_zero]
    have h₃ := (hla (p : c.F)⁻¹).2 (by rw [map_inv₀, h₂, inv_one])
    rw [map_inv₀, map_natCast, norm_inv] at h₃
    exact absurd h₃ (not_le.2 ((one_lt_inv₀ (norm_pos_iff.2 hp0)).2 hp1))
  have e₁ : ∀ x : ℂ_[p], ((Valued.v x : NNReal) : ℝ) = ‖x‖ := fun x => by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]
  rw [e₁, e₁] at h₀
  rw [← h₀]
  field_simp

theorem exists_gen_const : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (τ : D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ), p.Prime →
    ((p : 𝓞 D.what₂.LL) ∈ v.asIdeal) → p ∈ GlobalTheory.FlagAr.setB O.Y B →
    ∃ σ : (O.var c).Fn, (∀ y : (O.var c).X, UnitAt y ((∏ x : D.what₂.Tau × Fin O.N,
        if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D y else 1) / σ)) ∧
      ∃ C : ℝ, ∀ (e : Ext v) (y : AlgPt (O.var c)),
        (∑ x : D.what₂.Tau × Fin O.N, if x.1 = τ then (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).lg v e y else 0) -
          Real.log (e.w (valAt y.1 ((∏ x : D.what₂.Tau × Fin O.N,
            if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D (below y.1) else 1) / σ))) = C := by
  intro hP _ _ D O hO _ B _ c τ v p hp hpv hpB
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨W⟩ := GlobalTheory.Mean4O.ReadsEx.nonempty_latModel hO (GlobalTheory.FlagAr.setB O.Y B) c
  have hN := norms_prod (fun x : D.what₂.Tau × Fin O.N => norms_of_induces
    (Setup.induces_root0 D O hO.dualRef (GlobalTheory.FlagAr.setB O.Y B) c W (GlobalTheory.FlagAr.setB O.Y B) le_rfl x))
    (fun x => if x.1 = τ then (1 : ℤ) else 0)
  have hN' := hN.congr
    (f' := fun y => ∏ x : D.what₂.Tau × Fin O.N, if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D y else 1)
    (a' := _) (l' := fun v e y => ∑ x : D.what₂.Tau × Fin O.N,
      if x.1 = τ then (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).lg v e y else 0)
    (fun y => Finset.prod_congr rfl fun x _ => by split_ifs <;> simp) (fun _ _ => rfl)
    (fun v e y => Finset.sum_congr rfl fun x _ => by split_ifs <;> simp)
  obtain ⟨q, hq⟩ := GlobalTheory.CovHt.Link.exists_equiv_over D O.A O.N O.j O.S O.κ O.s O.Φ
  have h1 : 1 ≤ O.S.Dw.p + O.S.Dw.q := (one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge
  obtain ⟨f, hf, hdet⟩ := exists_detConst hP h1 O.κ.good (O.A.exists_datum 1 0) O.κ.curve O.s.T.Z (q c)
    ⟨DV.tauEmb D τ, O.A.cm τ⟩
  have ha : GlobalTheory.ShFam.Pad.ArIn.ind (GlobalTheory.FlagAr.setB O.Y B) (GlobalTheory.ShFam.Pad.resP v) = true := by
    rw [GlobalTheory.Mean4O.Cover.RegOverP.residueCharacteristic_eq_of_mem hp hpv]
    exact decide_eq_true hpB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.flag_statement_holds _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) (q c) _ f hf (hq c) hdet O.N O.S.rank_eq _ none v ha
  have eP : ∀ y, (∏ x : D.what₂.Tau × Fin O.N, if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D y else 1) =
      ∏ i : Fin O.N, genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) (τ, i)).D y := by
    intro y
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have eS : ∀ e y, (∑ x : D.what₂.Tau × Fin O.N, if x.1 = τ then (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).lg v e y else 0) =
      ∑ i : Fin O.N, (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) (τ, i)).lg v e y := by
    intro e y
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hgen : genericPoint (O.var c).X ∈ (O.Φ.C c).π ⁻¹ᵁ (GlobalTheory.Toroidal.genBd O.s.T.Z).compl := by
    letI := (GlobalTheory.ShFam.constF O.κ.e (O.Φ.C c).Y).toAlgebra
    intro h
    refine GlobalTheory.Toroidal.mem_genBd.1 h ⟨GlobalTheory.AllWt.ptF (O.Φ.C c).y0 (IsLocalRing.closedPoint _), ?_⟩
    have hx : (GlobalTheory.AllWt.ptF (O.Φ.C c).y0 ≫ O.s.T.Z.jQ) (IsLocalRing.closedPoint (O.Φ.C c).Y.Fn) =
        (O.Φ.C c).π (GlobalTheory.ShFam.genericPt (O.Φ.C c).Y (IsLocalRing.closedPoint (O.Φ.C c).Y.Fn)) := by
      rw [(O.Φ.C c).y0_x]; rfl
    exact hx.trans (congrArg (O.Φ.C c).π Scheme.fromSpecStalk_closedPoint)
  obtain ⟨k₁, k₂⟩ := extend W.V _ _ _ _ hN' ((O.Φ.C c).val f) _ hgen v p hp hpv ρ (fun e y hy => by
    rw [eP, eS]
    exact hρ e y hy)
  refine ⟨(O.Φ.C c).val f, fun y => by simpa only [inv_div] using (k₁ y).inv, ρ, fun e y => ?_⟩
  rw [← inv_div, GlobalTheory.LineNorm.Neg.valAt_inv (k₁ _), map_inv₀, Real.log_inv, ← k₂ e y]
  ring

end GlobalTheory.HTConstRoot
