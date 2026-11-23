import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphicStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotentialStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOnLogResolutionCorrStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeCompositionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPushStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirstStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentSecondStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentThirdStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourthStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeReindexedCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFifthStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem root_model_on_cover : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), o.Fl.deg = 1 → Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift → Function.Bijective o.Re.π → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i → 𝔐.f = h ≫ o.𝔐.f → 𝔐.cst = i.comp o.𝔐.cst → (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) → (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) → Fl.RootLines xdeg e → 𝔐.OmVB → SmoothGenericFibreM y → ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧ o'.𝔐.R = 𝔐.R ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  intro hG E _ _ _ H D l Xo c Y Sys Fx R o S Ω _ _ K _ J _ y bk bx i 𝔐 h Fl xdeg e hdeg1 hemb hbij hbk hy hd hf hcst
    hfl hfin hlines hom hsm
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hv := isBlockMap_blkV bx hbk
  haveI : Nonempty K := ⟨bk o.k₀⟩
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl hβ
  have harith' : IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) := harith
  obtain ⟨R'⟩ := GlobalTheory.T.exists_analytic_log_resolution K J Ω y _ harith' hsm
  have hP₀ : ¬ (⊤ : Ideal (MRing R.ι)) ≤ mCoordIdeal R.y := fun h' =>
    R.arith.2.1.1.ne_top (top_le_iff.1 h')
  have hle : mCoordIdeal R.y ≤ imageZ (blkV bk bx) (mCoordIdeal y) := mCoordIdeal_le_imageZ i bx hy
  let R₀ : AnLogRes (mCoordIdeal R.y) ⊤ (Top.dimFl (CMType H) (D.p + D.q)) := withTop o.Re.R hP₀ hemb
  obtain ⟨hh, hholo, horb⟩ := GlobalTheory.T.log_resolution_functorial_holomorphic R.K R.ι K J bk (blkV bk bx) (mCoordIdeal R.y) (mCoordIdeal y) ⊤ _ _ R₀ R' hv hle
  have hdpos : 0 < Fl.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, -⟩ := Fl.generic
    exact h0
  obtain ⟨br₀, hdeg₀⟩ := GlobalTheory.T.log_resolution_reindexed R.K K R.ι J R.Ω Ω R.y y bk bx i _ Fl.deg R₀ R' hh hbk hy R.arith harith'
    R.birational hbir hholo horb hfin hdpos
  obtain ⟨hholoπ, hdeg⟩ := GlobalTheory.T.holomorphic_degree_composition _ Fl.deg Sys.X o.Re.R.X R'.X Sys.A o.Re.R.A R'.A o.Re.π hh br₀ o.Re.holo hbij
    hholo hdeg₀
  obtain ⟨hreg, hrefl, hval⟩ := GlobalTheory.T.dominating_regular_push 𝔐.X o.𝔐.X Ω R.Ω 𝔐.ξ o.𝔐.ξ h i hd 𝔐.tie.gen
  have hval' : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : R.Ω) (r : ℂ), ValAt o.𝔐.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r :=
    fun z a r => hval z a r (𝔐.all _)
  have hco := GlobalTheory.T.dominating_coords_reindexed 𝔐.X o.𝔐.X Ω R.Ω 𝔐.ξ o.𝔐.ξ h i R.K K R.ι J R.y y bk bx hd o.𝔐.tie 𝔐.all hy hval'
  have hcov : IsCovOf o.𝔐 𝔐 i h := ⟨hd, hf, hcst⟩
  obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := GlobalTheory.T.hodge_comp_descent_first E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl hβ hcov hfl
  have hgen : GenPull o.Fl Fl i hd :=
    GlobalTheory.T.hodge_comp_descent_second E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl j hreg hj1 hj2 hj3 hj4
  have hnorm : NormPull o.Fl Fl i h :=
    GlobalTheory.T.hodge_comp_descent_third E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl j inferInstance hreg hj1 hj2 hj3 hj4 hj5
  have hab := mem_abLocus_iff o.𝔐 𝔐 h hf
  have hT : ∀ r : RootIx D, ∃ T : HermLine J, T.a = xdeg r - pullDeg bk (R.xdeg r) ∧ IsSmoothHerm T ∧
      IsConjInvariantH T ∧ IsFlatOn R' T ∧ IsRatio 𝔐.ξ y R.y bk bx i (xdeg r) (R.xdeg r) (e r) (o.e r) T.h := by
    intro r
    have hu := GlobalTheory.T.hodge_comp_descent_fourth E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl bk bx (xdeg r) (R.xdeg r)
      (e r) (o.e r) r hβ inferInstance hy hgen (o.lines r) (hlines r) hrefl hreg hco
    obtain ⟨φ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.degree_reindexed_coords 𝔐.X Ω R.Ω 𝔐.ξ i R.K K R.ι J R.y y bk bx (xdeg r) (R.xdeg r) (e r) (o.e r)
      𝔐.tie 𝔐.all hbk hy hu
    obtain ⟨T, t1, t2, t3, t4, t5⟩ := GlobalTheory.T.positive_homogeneous_potential K J _ _ R' _ φ h1 h2 h3 h4
    refine ⟨T, t1, t2, t3, t5, fun z w hw c c₀ hc hc₀ => ?_⟩
    have hm : w ∈ mcPts (mCoordIdeal y) := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).2 ⟨z, 𝔐.all _, hw⟩
    rw [t4 w hm]
    exact h5 z w hw c c₀ hc hc₀
  choose T hTa hTs hTc hTf hTr using hT
  have hmem : ∀ z ∈ mcPts (mCoordIdeal y), (fun p => z (blkV bk bx p)) ∈ mcPts (mCoordIdeal R.y) :=
    fun z hz => mem_mcPts_restr hv hle hz
  have hlift : ∀ x, ∀ k, ∃ a, R'.lift x x ⟨k, a⟩ ≠ 0 := fun x => (R'.mem x x (R'.mem_U x)).1
  have hlift₀ : ∀ x k, ∃ a, R'.lift x x (blkV bk bx ⟨k, a⟩) ≠ 0 := fun x => restr_ne hv (hlift x)
  have horb' : ∀ x, SameOrbit (o.Re.R.lift (hh x) (hh x)) (fun p => R'.lift x x (blkV bk bx p)) := horb
  let RM : Top.RootModel (CMType H) (D.p + D.q) :=
    { K := K, «ι» := J, Ω := Ω, y := y, arith := harith', birational := hbir, xdeg := xdeg
      x := fun t r => (pullHerm hv (R.x t r)).tensor (T r)
      x_deg := fun t r => by
        show pullDeg bk (R.x t r).a + (T r).a = xdeg r
        rw [R.x_deg, hTa]
        abel
      x_smooth := fun t r => isSmoothHerm_tensor (isSmoothHerm_pull hv (R.x_smooth t r)) (hTs r)
      x_conj := fun t r => isConj_tensor (isConj_pull hv (R.x_conj t r)) (hTc r)
      kA := R.kA, kA_pos := R.kA_pos
      A := pullHerm hv R.A
      A_smooth := isSmoothHerm_pull hv R.A_smooth
      A_conj := isConj_pull hv R.A_conj
      δ := Module.finrank ℚ c.F * Fl.deg
      δ_pos := Nat.mul_pos (Nat.pos_of_ne_zero fun h0 => by
        have h1 := R.δ_pos
        rw [o.δ_eq, h0, zero_mul] at h1
        exact lt_irrefl _ h1) hdpos }
  let Re' : PB.Realis Sys (mCoordIdeal y) :=
    { arith := harith', J := ⊤, R := R', π := o.Re.π ∘ hh, holo := hholoπ, deg := Fl.deg, deg_pos := hdpos
      br := o.Re.π '' br₀, degree := hdeg
      ref := fun a => (pullHerm hv (o.Re.ref a)).tensor (corr T a)
      ref_smooth := fun a => isSmoothHerm_tensor (isSmoothHerm_pull hv (o.Re.ref_smooth a)) (isSmoothHerm_corr hTs a)
      ref_pot := fun a => GlobalTheory.T.log_resolution_potential_pullback R.K K R.ι J bk (blkV bk bx) _ _ _ _ _ o.Re.R R' Sys.X Sys.A (Sys.th a) (o.Re.ref a)
        (corr T a) o.Re.π o.Re.holo hh hv hholoπ.1 hholo horb' (o.Re.ref_pot a) (GlobalTheory.T.flat_on_log_resolution_corr K J _ _ _ R' _ _ T hTf a)
      line := fun a t => (pullHerm hv (o.Re.line a t)).tensor (corr T a)
      line_deg := fun a t => by
        show pullDeg bk (o.Re.line a t).a + (corr T a).a = pullDeg bk (o.Re.ref a).a + (corr T a).a
        rw [o.Re.line_deg]
      line_smooth := fun a t h0 h1 => isSmoothHerm_tensor (isSmoothHerm_pull hv (o.Re.line_smooth a t h0 h1))
        (isSmoothHerm_corr hTs a)
      line_eq := fun a t h0 h1 x => by
        have e1 := o.Re.line_eq a t h0 h1 (hh x)
        have e2 := log_sub_orbit (o.Re.line_deg a t) (horb' x) (hlift₀ x)
        rw [log_tensor_pull hv _ _ (hlift x), log_tensor_pull hv _ _ (hlift x)]
        show _ = _ + Sys.phT a t (o.Re.π (hh x))
        linarith }
  have hsing : ∀ r, ((pullHerm hv (o.sing r)).tensor (T r)).a = xdeg r := fun r => by
    show pullDeg bk (o.sing r).a + (T r).a = xdeg r
    rw [o.sing_deg, hTa]
    abel
  have hInt : ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z ↔ o.𝔐.Interior (z ≫ h) := fun z => hab (centre z)
  let o' : RootOrigin Y S RM Fx :=
    { 𝔐 := 𝔐, Fl := Fl, g := i.comp o.g
      g_over := by
        have hd' : 𝔐.ξ ≫ h = spMap i ≫ o.𝔐.ξ := hd
        rw [hf, ← Category.assoc, hd', Category.assoc, o.g_over, spMap_comp', Category.assoc]
      g_flag := fun s a => by
        rw [hfl s a, o.g_flag s a, dualMap_comp', spMap_comp', Category.assoc]
      g_deg := by
        have e1 := finrank_comp' o.g i
        have e2 := o.g_deg
        rw [hdeg1] at e2
        rw [e2, _root_.one_mul] at e1
        exact e1.trans hfin
      g_const := fun a ha => by
        obtain ⟨b, hb⟩ := o.g_const a ha
        exact ⟨b, by rw [hcst]; simp [hb]⟩
      δ_eq := rfl
      e := e, lines := hlines
      sing := fun r => (pullHerm hv (o.sing r)).tensor (T r)
      sing_deg := hsing
      hodge := fun r => GlobalTheory.T.hodge_comp_descent_fifth E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl bk bx hv r (xdeg r)
        (R.xdeg r) (e r) (o.e r) (o.sing r) (T r) hβ inferInstance hy hgen hnorm hval' hco (fun z => (hInt z).1) (hlines r).1
        (o.sing_deg r) (hTa r) (hTr r) (o.hodge r)
      k₀ := bk o.k₀
      ix := o.ix.trans (bx o.k₀)
      y_eq := fun a => by
        show y ⟨bk o.k₀, bx o.k₀ (o.ix a)⟩ = i (o.g (Fx.yf a))
        rw [hy, o.y_eq]
      kA_eq := o.kA_eq
      A_deg := by
        constructor
        · show pullDeg bk R.A.a (bk o.k₀) = 1
          rw [pullDeg, hbk.extend_apply]
          exact o.A_deg.1
        · intro k hk
          show pullDeg bk R.A.a k = 0
          by_cases h' : ∃ a, bk a = k
          · obtain ⟨a, rfl⟩ := h'
            rw [pullDeg, hbk.extend_apply]
            exact o.A_deg.2 a fun e' => hk (by rw [e'])
          · rw [pullDeg, Function.extend_apply' _ _ _ h']
            rfl
      A_h := fun z hz => o.A_h _ (hmem z hz)
      eff := GlobalTheory.T.root_origin_coord_field E H D l Xo c _ _ Y Sys Fx R ∅ S o Ω K J y bk bx 𝔐 i h hd Fl xdeg e hy hgen hlines hrefl hreg hab
      Re := Re', Re_deg := rfl
      π_pt := fun x => by
        obtain ⟨a₀, ha₀⟩ := o.π_pt (hh x)
        obtain ⟨c', hc', hw⟩ := horb' x
        refine ⟨(c' o.k₀)⁻¹ * a₀, funext fun i' => ?_⟩
        have e1 := congrFun ha₀ i'
        simp only [Pi.smul_apply, smul_eq_mul] at e1
        rw [hw] at e1
        have e2 : c' o.k₀ * R'.lift x x ⟨bk o.k₀, bx o.k₀ (o.ix i')⟩ = a₀ * Fx.pt (o.Re.π (hh x)) i' := e1
        show R'.lift x x ⟨bk o.k₀, bx o.k₀ (o.ix i')⟩ = (c' o.k₀)⁻¹ * a₀ * Fx.pt (o.Re.π (hh x)) i'
        rw [_root_.mul_assoc, ← e2, inv_mul_cancel_left₀ (hc' o.k₀)]
      interior := fun x z hz => by
        have h1 : CoordsAt o.𝔐.ξ R.y (z ≫ h) (o.Re.R.lift (hh x) (hh x)) := coordsAt_orbit (hco z _ hz) (horb' x)
        exact (hInt z).trans (o.interior (hh x) (z ≫ h) h1)
      fund_deg := fun τ a => by
        show pullDeg bk (o.Re.ref (some (τ, a))).a + (stepLine (fun k => T (τ, k)) a).a = -∑ k ∈ Finset.Iic a, xdeg (τ, k)
        rw [o.fund_deg, pullDeg_neg_sum hbk]
        funext k
        simp only [stepLine, hTa, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib]
        show _ = -∑ k' ∈ Finset.Iic a, xdeg (τ, k') k
        ring
      fund_sing := fun τ a x hx => by
        have e1 := o.fund_sing τ a (hh x) hx
        have hab' : (o.Re.ref (some (τ, a))).a = -∑ k ∈ Finset.Iic a, (o.sing (τ, k)).a := by
          rw [o.fund_deg]
          simp only [o.sing_deg]
        have e2 := log_sum_orbit (Finset.Iic a) hab' (horb' x) (hlift₀ x)
        show Real.log (((pullHerm hv (o.Re.ref (some (τ, a)))).tensor (stepLine (fun k => T (τ, k)) a)).h (R'.lift x x)) +
            Sys.ph (some (τ, a)) (o.Re.π (hh x)) =
          -∑ k ∈ Finset.Iic a, Real.log (((pullHerm hv (o.sing (τ, k))).tensor (T (τ, k))).h (R'.lift x x))
        rw [log_tensor_pull hv _ _ (hlift x), log_stepLine _ _ (hlift x)]
        simp only [log_tensor_pull hv _ _ (hlift x), Finset.sum_add_distrib]
        linarith
      fund_reg := fun τ a t h0 h1 z hz => by
        have hz' : z ∈ mcPts (mCoordIdeal y) := hz
        have e1 := o.fund_reg τ a t h0 h1 _ (hmem z hz')
        show Real.log (((pullHerm hv (o.Re.line (some (τ, a)) t)).tensor (stepLine (fun k => T (τ, k)) a)).h z) =
          -∑ k ∈ Finset.Iic a, Real.log (((pullHerm hv (R.x t (τ, k))).tensor (T (τ, k))).h z)
        rw [log_tensor_pull hv _ _ hz'.1, log_stepLine _ _ hz'.1]
        simp only [log_tensor_pull hv _ _ hz'.1, Finset.sum_add_distrib]
        linarith
      ref_none := by
        refine ⟨?_, fun z hz => ?_⟩
        · show pullDeg bk (o.Re.ref none).a + 0 = pullDeg bk R.A.a
          rw [o.ref_none.1, add_zero]
        · show (o.Re.ref none).h (fun p => z (blkV bk bx p)) * 1 = R.A.h fun p => z (blkV bk bx p)
          rw [_root_.mul_one]
          exact o.ref_none.2 _ (hmem z hz) }
  exact ⟨RM, o', hom, rfl, rfl, inferInstance, hsm⟩

end GlobalTheory.CompanionTheory.Ar
