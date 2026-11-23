import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsTanIff
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.DualMapRComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrExtM
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open AlgebraicGeometry CategoryTheory ModelDimension.Near

set_option maxHeartbeats 1000000 in
theorem ModelDimension.integral_frame_over_cdvr : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  intro hG E _ _ _ H Dw l Xo c hI Y la T io e₀ ho hfin y
  letI := io.toAlgebra
  intro S _ _ w ψ z₀ t₀ hz₀ hb₀
  classical
  have hExt : GlobalTheory.Published.SemiAbelianHomExtension := hG.2.2.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨b, hb⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T.V T.Fr) hinj (io.comp (algebraMap (𝓞 c.F) c.F))
    (fun o => GlobalTheory.Reg.GenInt.int_mem_range io o)
  obtain ⟨yt, -, hyt⟩ := valCrit_proj Y.s Y.proj T.V T.Fr b (Small.ptY Y y.1) (by
    rw [Small.ptY_over, ← Tor.spMap_comp, hb])
  have := Y.t.semi.smooth
  have := projProper _ _ _ Y.proj
  obtain ⟨U, hU, hxU, -, n, v₀, hC⟩ :=
    GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G (yt (IsLocalRing.closedPoint T.V)) ⊤ trivial
  replace hC : IsChart Y hU v₀ := hC
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom hU T.V yt hxU
  obtain ⟨α, hα, hαf⟩ := GlobalTheory.ModelPoints.exists_chart_finiteType Y.s hU
  obtain ⟨gens, hgens⟩ := fin_gen hαf
  have hy : Small.ptY Y y.1 = Tor.spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec := by
    rw [← hyt, ← hf₀, Tor.spMap_comp f₀, Category.assoc]
  have hz₀Y : Small.ptY Y z₀ = Tor.spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec :=
    (ptY_bor Y hb₀).symm.trans hy
  obtain ⟨h, hh, fh, hfh⟩ := exists_spread hU (Small.ptY Y w) ψ.toRingHom _
    ((Small.ptY_map Y hz₀).symm.trans hz₀Y)
  have hg : ∀ τ i, ∃ cv, Crd Y hU v₀ fh cv
      (Tor.spMap (Chart.dualMapR (algebraMap S (Localization.Away h))) ≫ Small.tanY Y w τ i) := fun τ i =>
    (hC.isBas fh).exists (hfh ▸ gt_bc _ (tanY_gt Y w τ i))
  choose cv hcv using hg
  let g : ∀ τ : E →+* ℂ, Matrix (Fin n) (Fin (Dw.mult τ)) (Localization.Away h) :=
    fun τ => Matrix.of fun j i => cv τ i j
  have key : ∀ (ψ' : S →ₐ[c.F] T.Fr) (z' : FrPt Xo c T.Fr), FrMap ψ' w z' → ∀ χ : Localization.Away h →+* T.Fr,
      χ.comp (algebraMap S _) = ψ'.toRingHom → Small.ptY Y z' = Tor.spMap (χ.comp fh) ≫ hU.fromSpec ∧
        ∀ τ i, Crd Y hU v₀ (χ.comp fh) (fun j => ((g τ).map χ) j i) (Small.tanY Y z' τ i) := by
    intro ψ' z' hz' χ hχ
    refine ⟨?_, fun τ i => ?_⟩
    · rw [Small.ptY_map Y hz', ← hχ, Tor.spMap_comp _ χ, Tor.spMap_comp fh χ, Category.assoc, Category.assoc, hfh]
    · have h1 := (hcv τ i).bc χ
      rw [← Category.assoc, ← Tor.spMap_comp, ← dualMapR_comp, hχ] at h1
      rw [Small.tanY_map Y hz']
      exact h1
  let χ₀ : Localization.Away h →+* T.Fr := IsLocalization.Away.lift h (Ne.isUnit hh)
  have hχ₀ : χ₀.comp (algebraMap S _) = ψ.toRingHom := IsLocalization.Away.lift_comp h _
  obtain ⟨k1, k2⟩ := key ψ z₀ hz₀ χ₀ hχ₀
  have hf : χ₀.comp fh = (algebraMap T.V T.Fr).comp f₀ := chart_inj hU (k1.symm.trans hz₀Y)
  choose C hC1 hC2 hC3 using fun τ => hC.crd_bor hb₀ τ
  choose u hu1 hu2 using fun τ => hC.integral hExt y f₀ hy τ
  have e0 : ∀ τ, (g τ).map χ₀ * C τ = (u τ).map (algebraMap T.V T.Fr) := fun τ =>
    hC3 τ _ k1 _ _ (k2 τ) (by rw [hf]; exact hu2 τ)
  have ev1 : ∀ᶠ ψ' in closeF T.V ψ.toRingHom, ∀ s ∈ gens, ModelDimension.Near.ext h χ₀ ψ' (fh s) ∈ (algebraMap T.V T.Fr).range := by
    rw [Filter.eventually_all_finset]
    intro s _
    have h1 := tend_ext (V := T.V) hh hχ₀ (fh s)
    rw [show χ₀ (fh s) = algebraMap T.V T.Fr (f₀ s) from RingHom.congr_fun hf s] at h1
    filter_upwards [h1.cong] with ψ' ⟨b', h2, _⟩
    exact ⟨b', h2⟩
  have ev2 : ∀ᶠ ψ' in closeF T.V ψ.toRingHom, ∀ τ j i, ∃ b' : T.V,
      algebraMap T.V T.Fr b' = ((g τ).map (ModelDimension.Near.ext h χ₀ ψ') * C τ) j i ∧
        b' - u τ j i ∈ IsLocalRing.maximalIdeal T.V := by
    simp only [Filter.eventually_all]
    intro τ j i
    have h1 := Tend.sum Finset.univ fun k => (tend_ext (V := T.V) hh hχ₀ (g τ j k)).mul_const (C τ k i)
    rw [show ∑ k, χ₀ (g τ j k) * C τ k i = algebraMap T.V T.Fr (u τ j i) from congrFun (congrFun (e0 τ) j) i] at h1
    exact h1.cong
  obtain ⟨F, N, hFN⟩ : ∃ (F : Finset S) (N : ℕ), ∀ ψ' : S →+* T.Fr,
      (∀ s ∈ F, ψ' s = ψ.toRingHom s ∨ (N : ℤ) ≤ vV T.V (ψ' s - ψ.toRingHom s)) → _ :=
    (eventually_ne (V := T.V) hh).and (ev1.and ev2)
  refine ⟨F, N, fun ψ' hψ' z' hz' => ?_⟩
  obtain ⟨q1, q2, q3⟩ := hFN ψ'.toRingHom hψ'
  generalize hχ : ModelDimension.Near.ext h χ₀ ψ'.toRingHom = χ at q2 q3
  have hχ' : χ.comp (algebraMap S _) = ψ'.toRingHom := hχ ▸ ext_comp χ₀ q1
  obtain ⟨k3, k4⟩ := key ψ' z' hz' χ hχ'
  have hα' : (χ.comp fh).comp α = (algebraMap T.V T.Fr).comp b := by
    apply spMap_inj
    rw [Tor.spMap_comp, ← hα, ← Category.assoc, ← k3, Small.ptY_over, hb]
  obtain ⟨f', hf'⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T.V T.Fr) hinj (χ.comp fh)
    (hgens ((algebraMap T.V T.Fr).range.comap (χ.comp fh)) (fun o => ⟨b o, (RingHom.congr_fun hα' o).symm⟩) q2)
  choose W hW1 hW2 using q3
  obtain ⟨T', io', e', y', ho', halg, hrest⟩ := hI la T io e₀ ho hfin z'
  refine ⟨T', io', e', y', ho', halg, ?_⟩
  letI := io'.toAlgebra
  obtain ⟨φ, z'', t', hφ, hz'', hb''⟩ := hrest
  obtain ⟨r, -, her, hr, -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  have hval : ∀ x : T.Fr, vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x := fun x => by
    rw [show vV T'.V (φ x) = _ from hr x, her]
    push_cast
    ring
  refine ⟨φ, z'', t', hz'', hb'', fun x _ => hval x, fun τ i => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T'.V T'.Fr) (IsFractionRing.injective _ _)
    (φ.toRingHom.comp (algebraMap T.V T.Fr)) hφ
  have hF : φ.toRingHom.comp (χ.comp fh) = (algebraMap T'.V T'.Fr).comp (φ₀.comp f') := by
    rw [← hf', ← RingHom.comp_assoc, ← hφ₀, RingHom.comp_assoc]
  have k5 : Small.ptY Y z'' = Tor.spMap (φ.toRingHom.comp (χ.comp fh)) ≫ hU.fromSpec := by
    rw [Small.ptY_map Y hz'', k3, Tor.spMap_comp (χ.comp fh), Category.assoc]
  obtain ⟨C', hC1', hC2', hC3'⟩ := hC.crd_bor hb'' τ
  obtain ⟨u', hu1', hu2'⟩ := hC.integral hExt y' (φ₀.comp f') (by rw [ptY_bor Y hb'', k5, hF]) τ
  have e1 : ((g τ).map χ).map φ.toRingHom * C' = u'.map (algebraMap T'.V T'.Fr) :=
    hC3' _ k5 _ _ (fun i => by rw [Small.tanY_map Y hz'']; exact (k4 τ i).bc φ.toRingHom) (by rw [hF]; exact hu2')
  obtain ⟨B, hB⟩ := exists_left_inv (u' := Matrix.of (W τ)) (hu1 τ) (hW2 τ)
  have e2 : ((g τ).map χ).map φ.toRingHom * (C τ).map φ.toRingHom =
      ((Matrix.of (W τ)).map φ₀).map (algebraMap T'.V T'.Fr) := by
    rw [← Matrix.map_mul]
    ext j k
    rw [Matrix.map_apply, ← hW1]
    exact (RingHom.congr_fun hφ₀ _).symm
  have hB' : B.map φ₀ * (Matrix.of (W τ)).map φ₀ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 := vV_diag_eq (C := (C τ).map φ.toRingHom)
    (fun j k hjk => by rw [Matrix.map_apply, hC1 τ hjk, map_zero]) hC1'
    (fun j => by rw [Matrix.map_apply, hC2]; exact (map_ne_zero _).2 (Units.ne_zero _))
    (fun j => by rw [hC2']; exact Units.ne_zero _) hB' hu1' e2 e1 i
  rw [hC2', Matrix.map_apply, hC2] at e3
  rw [e3]
  exact hval _
