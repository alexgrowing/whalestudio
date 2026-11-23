import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RationalRelationInChartIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseElementFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTorusTranslatesCoverStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBis
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.SncCpt

open ReciprocityTheory.AnForm.R (locRing locPt ptIdeal renPt renC renR zeroSet)

theorem exists_ev {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ) (hI : ∀ g ∈ I, eval p g = 0) :
    ∃ π : locRing I p →+* ℂ, ∀ g, π (algebraMap _ _ g) = eval p g := by
  let π0 : locPt p →+* ℂ := IsLocalization.lift (M := (ptIdeal p).primeCompl)
    (g := (eval p : MvPolynomial (Fin m) ℂ →+* ℂ))
    (fun s => isUnit_iff_ne_zero.2 (fun h => s.2 (RingHom.mem_ker.2 h)))
  have h0 : ∀ g, π0 (algebraMap _ _ g) = eval p g := fun g => IsLocalization.lift_eq _ g
  have hk : ∀ a ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) I, π0 a = 0 := by
    have : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) I ≤ RingHom.ker π0 := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp only [Ideal.mem_comap, RingHom.mem_ker, h0, hI g hg]
    exact fun a ha => this ha
  refine ⟨Ideal.Quotient.lift _ π0 hk, fun g => ?_⟩
  exact (Ideal.Quotient.lift_mk _ π0 hk).trans (h0 g)

theorem isUnit_loc {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ)
    (g : MvPolynomial (Fin m) ℂ) (hg : eval p g ≠ 0) : IsUnit (algebraMap _ (locRing I p) g) := by
  have := (IsLocalization.map_units (locPt p)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ptIdeal p).primeCompl)).map
    (algebraMap (locPt p) (locRing I p))
  rwa [← IsScalarTower.algebraMap_apply] at this

theorem span_eq_of_unit {B ι' : Type*} [CommRing B] (a b : ι' → B) (u : ι' → B) (hu : ∀ i, IsUnit (u i))
    (h : ∀ i, a i = b i * u i) : Ideal.span (Set.range a) = Ideal.span (Set.range b) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [h i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := (hu i).exists_right_inv
    have : b i = a i * v := by rw [h i, _root_.mul_assoc, hv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_perm (n a : ℕ) (G : Finset (Fin n)) (hG : G.card = a) :
    ∃ τ : Equiv.Perm (Fin n), ∀ j : Fin n, (j : ℕ) < a ↔ τ j ∈ G :=
  _root_.UpperTheory.Reformulated.B.DYdc4.main n a G hG

end GlobalTheory.CompanionTheory.Ar.SncCpt

namespace GlobalTheory.CompanionTheory.Ar.SncCpt

open ReciprocityTheory.AnForm.R (locRing locPt ptIdeal renPt renC renR zeroSet)

theorem snc_params : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)),
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) → Cmp.IsSncModel y n bd →
    ∀ (c : (k : K) → J k) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    [IsLocalRing (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c) (renPt (ReciprocityTheory.AnForm.R.affCoord c w)))] →
    [IsNoetherianRing (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c) (renPt (ReciprocityTheory.AnForm.R.affCoord c w)))] →
    ∃ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ), a ≤ n ∧
      Ideal.span (Set.range fun i => algebraMap _ (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c)
        (renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
        Ideal.map (algebraMap _ (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c) (renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
          (ptIdeal (renPt (ReciprocityTheory.AnForm.R.affCoord c w))) ∧
      (∀ i, eval (renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) ∧
      eval (renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 ∧
      ∀ v ∈ zeroSet (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c), eval v h ≠ 0 →
        ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ mcPts (mCoordIdeal y) ∩ mcPts bd ↔
          ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0) := by
  intro K _ J _ Ω _ _ y n bd hPh hS c w hw hwc _ _
  classical
  obtain ⟨u, hu⟩ : ∃ u : (Σ k, J k) → Ω, u = fun p => y p / y ⟨p.1, c p.1⟩ := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = Cmp.SncRes.ideal (pC (mCoordIdeal y)) c := ⟨_, rfl⟩
  obtain ⟨pt, hpt⟩ : ∃ pt, pt = renPt (ReciprocityTheory.AnForm.R.affCoord c w) := ⟨_, rfl⟩
  obtain ⟨CI, hCI⟩ : ∃ CI, CI = ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := ⟨_, rfl⟩
  rw [← hI, ← hpt]
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    have hmem : (X ⟨k, c k⟩ : MRing J) ∈ mCoordIdeal y := by
      apply RingHom.mem_ker.2
      simp [mConeMap, h0]
    have := hw.2 _ hmem
    simp only [map_X, eval_X] at this
    exact hwc k this
  have hz0 : ∀ g ∈ CI, eval (ReciprocityTheory.AnForm.R.affCoord c w) g = 0 := by
    rw [hCI]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh c w hwc).1 ((mem_mcPts_iff_conePts_pC _ _).1 hw)
  have hrenI : ∀ g ∈ CI, renC (Σ k, J k) g ∈ I := by
    intro g hg
    rw [hI, Cmp.SncRes.ideal]
    rw [hCI] at hg
    have := (ReciprocityTheory.AnForm.R.mem_map_renR_iff (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c)
      (renR (Σ k, J k) g)).2 (by simpa using hg)
    exact this
  have hI0 : ∀ g ∈ I, eval pt g = 0 := by
    rw [hpt, hI]
    exact ReciprocityTheory.AnForm.R.renPt_zero _ _ (by rw [← hCI]; exact hz0)
  have hker : ∀ G : MvPolynomial (Σ k, J k) ℚ, aeval u G = (0 : Ω) → map (algebraMap ℚ ℂ) G ∈ CI := by
    rw [hu, hCI]
    exact GlobalTheory.T.rational_relation_in_chart_ideal K J Ω y c hc
  obtain ⟨m, f, aa, hf, ha, hsum, hl⟩ := hS c hc
  rw [← hu] at hf ha
  have hpoly : ∀ s ∈ Algebra.adjoin ℚ (Set.range u), ∃ G : MvPolynomial (Σ k, J k) ℚ, aeval u G = s := by
    intro s hs
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    exact hs
  choose F hF using fun l => hpoly (f l) (hf l)
  choose A hAa using fun l => hpoly (aa l) (ha l)
  obtain ⟨l, hl0⟩ : ∃ l, eval (ReciprocityTheory.AnForm.R.affCoord c w) (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : aeval u (∑ l, A l * F l - 1) = (0 : Ω) := by
      simp only [map_sub, map_sum, map_mul, hF, hAa, hsum, map_one, sub_self]
    have h2 := hz0 _ (hker _ h1)
    simp [map_sub, map_sum, map_mul, hcon] at h2
  have hf0 : f l ≠ 0 := by
    intro h0
    exact hl0 (hz0 _ (hker (F l) (by rw [hF]; exact h0)))
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range u)) := ⟨_, rfl⟩
  obtain ⟨-, z, nn, hnn, -, hsp, hiff⟩ := hl l hf0 S (by rw [hSdef, hu])
  rw [← hu] at hiff

  have hmemS : ∀ G : MvPolynomial (Σ k, J k) ℚ, aeval u G ∈ S := by
    intro G
    rw [hSdef]
    have h1 : aeval u G ∈ Algebra.adjoin ℚ (Set.range u) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨G, rfl⟩
    exact Algebra.adjoin_mono (Set.subset_insert _ _) h1
  have hS' : S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) (F l) : Ω)⁻¹
      (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) := by
    rw [← hu, hF, hSdef]
  have hnum := GlobalTheory.T.adjoin_inverse_element_form (Σ k, J k) Ω u (f l) S hSdef (F l) (hF l) hf0
  choose Z kk hZ using fun i => hnum (z i)
  let fS : S := ⟨f l, by rw [← hF l]; exact hmemS _⟩
  have hhom : ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R), (∀ g ∈ CI, θ g = 0) →
      IsUnit (θ (map (algebraMap ℚ ℂ) (F l))) → ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
        (s : Ω) = aeval u G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
    intro R _ θ h1 h2
    have := GlobalTheory.T.chart_ideal_localization_map K J Ω y c hc R θ (by rw [← hCI]; exact h1) (F l) h2 S hS'
    rwa [← hu] at this
  have hval : ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R) (ψ : S →+* R),
      (∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S), (s : Ω) = aeval u G → ψ s = θ (map (algebraMap ℚ ℂ) G)) →
      ∀ i, ψ (z i) * θ (map (algebraMap ℚ ℂ) (F l)) ^ kk i = θ (map (algebraMap ℚ ℂ) (Z i)) := by
    intro R _ θ ψ h i
    have h1 : ψ fS = θ (map (algebraMap ℚ ℂ) (F l)) := h _ _ (hF l).symm
    rw [← h1, ← map_pow, ← map_mul]
    exact h _ _ (by simpa [fS] using hZ i)
  haveI : IsLocalRing (locRing I pt) := by subst hI hpt; assumption
  haveI : IsNoetherianRing (locRing I pt) := by subst hI hpt; assumption
  have hev : ∀ g, eval pt (renR (Σ k, J k) g) = eval (ReciprocityTheory.AnForm.R.affCoord c w) g := by
    intro g
    rw [hpt]
    exact ReciprocityTheory.AnForm.R.eval_renC _ g
  let θB : MvPolynomial (Σ k, J k) ℂ →+* locRing I pt :=
    (algebraMap _ (locRing I pt)).comp (renR (Σ k, J k)).toRingHom
  have hθB : ∀ g, θB g = algebraMap _ (locRing I pt) (renR (Σ k, J k) g) := fun _ => rfl
  have hkillB : ∀ g ∈ I, algebraMap _ (locRing I pt) g = 0 := by
    intro g hg
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
  obtain ⟨ψ, hψ⟩ := hhom _ θB (fun g hg => hkillB _ (hrenI g hg)) (by
    rw [hθB]
    exact isUnit_loc _ _ _ (by rw [hev]; exact hl0))
  obtain ⟨π, hπ⟩ := exists_ev I pt hI0
  let φ0 : S →+* ℂ := π.comp ψ
  have hφ0 : ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S), (s : Ω) = aeval u G →
      φ0 s = eval (ReciprocityTheory.AnForm.R.affCoord c w) (map (algebraMap ℚ ℂ) G) := by
    intro G s hs
    show π (ψ s) = _
    rw [hψ G s hs, hθB, hπ, hev]
  have hιC : ∀ a : ℂ, algebraMap ℂ (locRing I pt) a = algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) (C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) a]
    rfl
  have hι : ∀ a : ℂ, π (algebraMap ℂ (locRing I pt) a) = a := by
    intro a
    rw [hιC, hπ, eval_C]
  have hmax : ∀ s, ψ s - algebraMap ℂ (locRing I pt) (φ0 s) ∈ IsLocalRing.maximalIdeal (locRing I pt) := by
    intro s
    by_contra hn
    have hu' : IsUnit (ψ s - algebraMap ℂ (locRing I pt) (φ0 s)) := by
      simpa using hn
    have := hu'.map π
    rw [map_sub, hι] at this
    simp [φ0] at this
  have hKp : I ≤ ptIdeal pt := fun g hg => RingHom.mem_ker.2 (hI0 g hg)
  have hm := ReciprocityTheory.AnForm.R.maximalIdeal_locRing hKp
  let sp : (Σ k, J k) → S := fun p => ⟨u p, by simpa using hmemS (X p)⟩
  have hsp1 : ∀ p, ψ (sp p) = algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) (X (Fintype.equivFin (Σ k, J k) p)) := by
    intro p
    rw [hψ (X p) (sp p) (by simp [sp]), hθB]
    simp
  have hsp2 : ∀ p, φ0 (sp p) = pt (Fintype.equivFin (Σ k, J k) p) := by
    intro p
    rw [hφ0 (X p) (sp p) (by simp [sp]), hpt]
    simp
  have hT : IsLocalRing.maximalIdeal (locRing I pt) =
      Ideal.span ((fun s => ψ s - algebraMap ℂ (locRing I pt) (φ0 s)) '' Set.range sp) := by
    refine hm.trans ((congrArg (fun L => Ideal.map (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt)) L) (ReciprocityTheory.AnForm.R.ptIdeal_eq_span pt)).trans ?_)
    simp only [Ideal.map_span]
    apply congrArg
    ext b
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨(Fintype.equivFin (Σ k, J k)).symm i, ?_⟩
      rw [hsp1, hsp2, hιC]
      simp
    · rintro ⟨p, rfl⟩
      refine ⟨Fintype.equivFin (Σ k, J k) p, ?_⟩
      rw [hsp1, hsp2, hιC]
      simp
  have hgen := GlobalTheory.T.kaehler_differentials_span_local S (locRing I pt) ψ φ0 hmax (Set.range sp) hT n z hsp

  let Fr := renR (Σ k, J k) (map (algebraMap ℚ ℂ) (F l))
  let Zr : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ :=
    fun i => renR (Σ k, J k) (map (algebraMap ℚ ℂ) (Z i))
  let r0 : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ :=
    fun i => Zr i - C (φ0 (z i)) * Fr ^ kk i
  have hvB := hval _ θB ψ hψ
  have hFu : IsUnit (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) Fr) :=
    isUnit_loc _ _ _ (by show eval pt (renR (Σ k, J k) _) ≠ 0; rw [hev]; exact hl0)
  have hr0B : ∀ i, algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) (r0 i) =
      (ψ (z i) - algebraMap ℂ (locRing I pt) (φ0 (z i))) *
        (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) Fr) ^ kk i := by
    intro i
    have h1 := hvB i
    rw [hθB, hθB] at h1
    simp only [r0, map_sub, map_mul, map_pow]
    rw [hιC, sub_mul, h1]
  have hspan0 : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (locRing I pt) (r0 i)) = IsLocalRing.maximalIdeal (locRing I pt) := by
    rw [hgen]
    exact span_eq_of_unit _ _ (fun i => (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (locRing I pt) Fr) ^ kk i) (fun i => hFu.pow _) hr0B
  have hvpt : ∀ i, φ0 (z i) * eval pt Fr ^ kk i = eval pt (Zr i) := by
    intro i
    have h1 := hval ℂ (eval (ReciprocityTheory.AnForm.R.affCoord c w)) φ0 hφ0 i
    simpa only [Fr, Zr, hev] using h1
  have hptF : eval pt Fr ≠ 0 := by
    show eval pt (renR (Σ k, J k) _) ≠ 0
    rw [hev]
    exact hl0
  let Gd : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < nn ∧ φ0 (z i) = 0
  let Bad : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < nn ∧ φ0 (z i) ≠ 0
  obtain ⟨τ, hτ⟩ := exists_perm n Gd.card Gd rfl
  refine ⟨Gd.card, fun i => r0 (τ i), Fr * ∏ i ∈ Bad, Zr i, by simpa using Gd.card_le_univ, ?_, ?_, ?_, ?_⟩
  · rw [← hm, ← hspan0]
    apply congrArg
    exact τ.surjective.range_comp (fun i => algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (locRing I pt) (r0 i))
  · intro i
    simp only [r0, map_sub, map_mul, map_pow, eval_C]
    rw [hvpt, sub_self]
  · rw [map_mul, map_prod]
    refine mul_ne_zero hptF (Finset.prod_ne_zero_iff.2 fun i hi => ?_)
    rw [← hvpt]
    have hi' : (i : ℕ) < nn ∧ φ0 (z i) ≠ 0 := by simpa [Bad] using hi
    exact mul_ne_zero hi'.2 (pow_ne_zero _ hptF)
  · intro v hv hvh
    rw [map_mul, map_prod] at hvh
    have hvF : eval v Fr ≠ 0 := left_ne_zero_of_mul hvh
    have hvZ : ∀ i ∈ Bad, eval v (Zr i) ≠ 0 := fun i hi =>
      Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hvh) i hi
    obtain ⟨v', hv'⟩ : ∃ v' : (Σ k, J k) → ℂ, v' = fun q => v (Fintype.equivFin (Σ k, J k) q) := ⟨_, rfl⟩
    rw [← hv']
    have hvv : renPt v' = v := by
      funext j
      simp [hv', renPt]
    have hev' : ∀ g, eval v (renR (Σ k, J k) g) = eval v' g := fun g => by
      have := ReciprocityTheory.AnForm.R.eval_renC v' g
      rw [hvv] at this
      exact this
    have hzc : ∀ g ∈ CI, eval v' g = 0 := fun g hg => by
      rw [← hev']
      exact hv _ (hrenI g hg)
    have hcone := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPh c v' (by rw [← hCI]; exact hzc)
    have hvP : v' ∈ mcPts (mCoordIdeal y) := (mem_mcPts_iff_conePts_pC _ _).2 hcone.1
    obtain ⟨φ, hφ⟩ := hhom ℂ (eval v') hzc (isUnit_iff_ne_zero.2 (by rw [← hev']; exact hvF))
    have hvφ : ∀ i, φ (z i) * eval v Fr ^ kk i = eval v (Zr i) := by
      intro i
      have h1 := hval ℂ (eval v') φ hφ i
      simpa only [Fr, Zr, hev'] using h1
    have hq := hiff (RingHom.ker φ) (RingHom.ker_isPrime φ)
    have haev : ∀ g : MRing J, aeval u g = aeval u (map (algebraMap ℤ ℚ) g) := fun g =>
      (MvPolynomial.aeval_map_algebraMap ℚ u g).symm
    have hgbd : ∀ (g : MRing J) (s : S), (s : Ω) = aeval u g →
        φ s = eval v' (map (Int.castRingHom ℂ) g) := by
      intro g s hs
      rw [hφ (map (algebraMap ℤ ℚ) g) s (hs.trans (haev g)), map_map]
      congr 2
    have hL : (∀ g ∈ bd, ∀ s : S, (s : Ω) = aeval u g → s ∈ RingHom.ker φ) ↔ v' ∈ mcPts bd := by
      constructor
      · intro H
        refine ⟨hvP.1, fun g hg => ?_⟩
        have hs : aeval u g ∈ S := by
          rw [haev]
          exact hmemS _
        rw [← hgbd g ⟨_, hs⟩ rfl]
        exact H g hg _ rfl
      · rintro ⟨-, H⟩ g hg s hs
        exact RingHom.mem_ker.2 ((hgbd g s hs).trans (H g hg))
    constructor
    · rintro ⟨-, hb⟩
      obtain ⟨i, hi, hzi⟩ := hq.1 (hL.2 hb)
      have hφz : φ (z i) = 0 := hzi
      have hZ0 : eval v (Zr i) = 0 := by
        rw [← hvφ, hφz, zero_mul]
      have hg0 : φ0 (z i) = 0 := by
        by_contra hne
        exact hvZ i (by simp [Bad, hi, hne]) hZ0
      refine ⟨τ.symm i, (hτ _).2 (by simpa [Gd] using ⟨hi, hg0⟩), ?_⟩
      show eval v (r0 (τ (τ.symm i))) = 0
      rw [τ.apply_symm_apply]
      simp only [r0, map_sub, map_mul, map_pow, eval_C, hZ0, hg0, zero_mul, sub_zero]
    · rintro ⟨j, hj, hj0⟩
      have hG := (hτ j).1 hj
      obtain ⟨hi, hg0⟩ : ((τ j : Fin n) : ℕ) < nn ∧ φ0 (z (τ j)) = 0 := by simpa [Gd] using hG
      have h1 : eval v (Zr (τ j)) = 0 := by
        have h2 : eval v (r0 (τ j)) = 0 := hj0
        simpa only [r0, map_sub, map_mul, map_pow, eval_C, hg0, zero_mul, sub_zero] using h2
      have h2 : φ (z (τ j)) = 0 := by
        have h3 := hvφ (τ j)
        rw [h1] at h3
        exact (mul_eq_zero.1 h3).resolve_right (pow_ne_zero _ hvF)
      exact ⟨hvP, hL.1 (hq.2 ⟨τ j, hi, h2⟩)⟩

end GlobalTheory.CompanionTheory.Ar.SncCpt

namespace GlobalTheory.CompanionTheory.Ar.SncCpt

theorem reg_at : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), IsArithVar (mCoordIdeal y) (n + 1) → Cmp.IsSncModel y n bd →
    ∀ (c : (k : K) → J k) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) ∧
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n := by
  intro K _ J _ Ω _ _ y n bd hA hS c w hw hwc
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have hwc' : w ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)) := (mem_mcPts_iff_conePts_pC _ _).1 hw
  let x : Cmp.SncRes.Pts (pC (mCoordIdeal y)) := ⟨Cmp.SncRes.proj w, w, hwc', rfl⟩
  have hso : ReciprocityTheory.AnForm.R.SameOrbit (Cmp.SncRes.rep x) w :=
    Cmp.SncRes.sameOrbit_of_proj_eq (Cmp.SncRes.rep_mem x).1 hwc'.1 (Cmp.SncRes.proj_rep x)
  have hco : Cmp.SncRes.coord (pC (mCoordIdeal y)) c x = ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w) := by
    unfold Cmp.SncRes.coord
    rw [ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit c hso]
  have hx : x ∈ Cmp.SncRes.src (pC (mCoordIdeal y)) c := by
    intro k
    obtain ⟨d, hd, he⟩ := hso
    rw [show Cmp.SncRes.rep x ⟨k, c k⟩ = d k * w ⟨k, c k⟩ from congrFun he _]
    exact mul_ne_zero (hd k) (hwc k)
  have := GlobalTheory.T.snc_resolution_regular_local_ring K J Ω y n bd hA hS c x hx
  rwa [hco] at this

theorem exists_sncCharts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y n bd → IsArithVar (mCoordIdeal y) (n + 1) → (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) → ∃ (nc : ℕ) (χ : Fin nc → SncChart (mCoordIdeal y) n (mcPts (mCoordIdeal y) ∩ mcPts bd)), ∀ z ∈ mcPts (mCoordIdeal y), ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((χ a).γ t) := by
  intro K _ J _ Ω _ _ y n bd hS hA _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have key : ∀ w : mcPts (mCoordIdeal y), ∃ (χ : SncChart (mCoordIdeal y) n (mcPts (mCoordIdeal y) ∩ mcPts bd))
      (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ (w : (Σ k, J k) → ℂ) ∈ O ∧
      ∀ z ∈ O ∩ mcPts (mCoordIdeal y), ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc, -⟩ := ReciprocityTheory.AnForm.R.exists_chart w hw.1
    obtain ⟨hreg, hdim⟩ := reg_at K J Ω y n bd hA hS c w hw hc
    have hzero : ∀ g ∈ Cmp.SncRes.ideal (pC (mCoordIdeal y)) c,
        eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) g = 0 := by
      refine ReciprocityTheory.AnForm.R.renPt_zero _ _ ?_
      exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh c w hc).1 ((mem_mcPts_iff_conePts_pC _ _).1 hw)
    obtain ⟨hl, hn⟩ := ReciprocityTheory.AnForm.R.locRing_isLocalRing_isNoetherian _ _ hzero
    obtain ⟨a, r, h, ha, hr, hr0, hh, hb⟩ := snc_params K J Ω y n bd hPh hS c w hw hc
    exact GlobalTheory.T.regular_local_chart_coords K J _ hPh n _ c w hw hc a r h hdim ha hr hr0 hh hb
  choose χ O hO hwO hcov using key
  obtain ⟨m, e, he⟩ := GlobalTheory.T.finite_torus_translates_cover K J _ hPh _ O hO (fun z hz => ⟨⟨z, hz⟩, hwO ⟨z, hz⟩⟩)
  refine ⟨m, fun a => χ (e a), fun z hz => ?_⟩
  obtain ⟨a, c, hc, h1, h2⟩ := he z hz
  obtain ⟨t, ht, c', hc', h3⟩ := hcov (e a) _ ⟨h1, h2⟩
  refine ⟨a, t, ht, fun k => (c k)⁻¹ * c' k, fun k => mul_ne_zero (inv_ne_zero (hc k)) (hc' k), ?_⟩
  funext q
  have := congrFun h3 q
  simp only [torusSmul] at this ⊢
  rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

end GlobalTheory.CompanionTheory.Ar.SncCpt
