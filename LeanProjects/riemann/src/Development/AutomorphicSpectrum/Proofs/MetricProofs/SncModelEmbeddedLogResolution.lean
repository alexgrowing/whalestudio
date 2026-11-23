import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Immersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbeddedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndConeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossingStatement

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isUnit_algebraMap_locRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (pt : Fin n → ℂ)
    (g : MvPolynomial (Fin n) ℂ) (hg : eval pt g ≠ 0) :
    IsUnit (algebraMap _ (ReciprocityTheory.AnForm.R.locRing I pt) g) := by
  have := (IsLocalization.map_units (ReciprocityTheory.AnForm.R.locPt pt)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ReciprocityTheory.AnForm.R.ptIdeal pt).primeCompl)).map
    (algebraMap (ReciprocityTheory.AnForm.R.locPt pt) (ReciprocityTheory.AnForm.R.locRing I pt))
  rwa [← IsScalarTower.algebraMap_apply] at this

theorem not_mem_conePts_top (z : (Σ k, ι k) → ℂ) :
    z ∉ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :=
  fun hz => by simpa using hz.2 1 Submodule.mem_top

theorem exists_isEmbedded_of_algRes {P J : Ideal (MRing ι)} {e : ℕ} (hJ : IsMultiHomogIdeal J)
    (hJP : ¬ J ≤ P) (hPC : ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e)
    (hsurj : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), ∃ i, ∃ x ∈ R.src i,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q)) z)
    (hinj : ∀ i j, ∀ x ∈ R.src i, ∀ x' ∈ R.src j,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q))
        (fun q => eval (R.coord j x') (R.lift j q)) → x = x')
    (hinv : ∀ i, ∀ x ∈ R.src i, ∀ p : (k : K) → ι k, (∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set R.M, IsOpen O ∧ x ∈ O ∧ O ⊆ R.src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (R.amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (R.coord i y) (R.lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q ≠ 0 ∧
          ∀ l, R.coord i y l * eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q =
            eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) (F l)) :
    ∃ R' : AnLogRes P J e, IsEmbedded R'.A P R'.U R'.lift := by
  classical
  let R0 : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) ⊤ e :=
    { M := R.M
      n := R.n
      amb := R.amb
      ideal := R.ideal
      src := R.src
      isOpen_alt_bis := R.isOpen_alt_bis
      cover := R.cover
      coord := R.coord
      isEmbedding := R.isEmbedding
      image := R.image
      trans := R.trans
      regular := R.regular
      dim := R.dim
      lift := R.lift
      lift_one := R.lift_one
      lift_mem := R.lift_mem
      compat := R.compat
      surj := fun z hz _ => hsurj z hz
      inj := fun i j x hx x' hx' _ h => hinj i j x hx x' hx' h
      inv := fun i x hx _ p hp => hinv i x hx p hp
      bd := fun _ => ⊤
      le_bd := fun _ => le_top
      zero_bd := fun i x hx =>
        ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp), fun h => absurd h (not_mem_conePts_top _)⟩
      rc := 0
      comp := Fin.elim0
      sncAt := fun i x hx =>
        { r := (R.sncAt i x hx).r
          J := ∅
          h := 1
          σ := fun _ => none
          σ_injOn := by simp
          σ_eq_none := by simp
          span_eq := (R.sncAt i x hx).span_eq
          eval_h := by simp
          mem_bd := Submodule.mem_top
          le_span := fun g _ => by simp }
      comp_eq := fun i x hx => ⟨R.src i, R.isOpen_alt_bis i, hx, subset_rfl, fun k => k.elim0⟩
      mult := fun f a hf hfP hz => ⟨Fin.elim0, fun i x hx =>
        ⟨_, isUnit_algebraMap_locRing _ _ _ (by
          rw [ReciprocityTheory.AnForm.R.eval_bind_one]
          intro h0
          exact not_mem_conePts_top _ (hz _ (R.lift_mem i x hx) h0)), by simp⟩⟩ }
  obtain ⟨A, hA⟩ := R0.exists_atlas
  have hA' : R.IsGoodAtlas A := hA
  choose idx hidx using R.cover
  let R' : AnLogRes P J e :=
    { homog := hJ
      nondeg := hJP
      X := R.M
      A := A
      U := fun x => R.src (idx x)
      isOpen_U := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      lift := fun x y q => eval (R.coord (idx x) y) (R.lift (idx x) q)
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := fun x y hy => by
        rw [mem_mcPts_iff_conePts_pC]
        exact R.lift_mem (idx x) y hy
      compat := fun x x' y hy => R.compat (idx x) (idx x') y hy
      surj := fun z hz _ => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' _ hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x _ p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj
      snc := fun f a hfP hf hz => by
        have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
          fun m hm k => hf m (support_map_subset _ _ hm) k
        have hfP' : map (Int.castRingHom ℂ) f ∉ pC P := fun h => hfP (hPC f h)
        have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), eval z (map (Int.castRingHom ℂ) f) = 0 →
            z ∈ ReciprocityTheory.AnForm.R.conePts (pC J) := by
          intro z hz1 hz2
          rw [← mem_mcPts_iff_conePts_pC] at hz1 ⊢
          exact hz z hz1 hz2
        obtain ⟨m, hm⟩ := R.isSNC_pullback A hA' idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
        exact ⟨R.rc, m, R.comp, hm⟩
      null := fun j => by
        refine MeasureTheory.measure_mono_null ?_ (R.volume_preimage_eq_zero A hA' j)
        rintro y ⟨hy1, hy2⟩
        refine ⟨hy1, idx _, hidx _, ?_⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy2 ⊢
        rw [← mem_mcPts_iff_conePts_pC]
        exact hy2 }
  refine ⟨R', ?_⟩
  exact
    { isOpen := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := R'.mem
      compat := R'.compat
      surj := fun z hz => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj }

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem isEmbedded_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∃ R : AnLogRes (mCoordIdeal y) J e, IsEmbedded R.A (mCoordIdeal y) R.U R.lift := by
  intro K _ ι _ Ω _ _ y e J hP hJ hJP hsnc
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hDh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  obtain ⟨hcpt, hsrc⟩ := GlobalTheory.T.snc_resolution_compact_embedded K ι _ hPh
  obtain ⟨himage, htrans⟩ := GlobalTheory.T.snc_resolution_transition_polynomial K ι _ hPh
  obtain ⟨hcover, hliftmem, hcompat, hsurj, hinj, hzero⟩ := GlobalTheory.T.snc_resolution_cover_and_cone K ι _ _ hPh hDh
  have hinv := GlobalTheory.T.snc_resolution_local_chart_polynomial K ι _ hPh
  have hreg := GlobalTheory.T.snc_resolution_regular_local_ring K ι Ω y e J hP hsnc
  have hsc := GlobalTheory.T.snc_resolution_boundary_normal_crossing K ι Ω y e J hP hJ hJP hsnc
  let E := Fintype.equivFin ((k : K) → ι k)
  let R : ReciprocityTheory.AnForm.R.AlgRes ι (pC (mCoordIdeal y)) (pC J) e :=
    { M := Pts (pC (mCoordIdeal y))
      compact := hcpt
      n := Fintype.card ((k : K) → ι k)
      amb := fun _ => Fintype.card (Σ k, ι k)
      ideal := fun i => ideal _ (E.symm i)
      src := fun i => src _ (E.symm i)
      isOpen_alt_bis := fun i => (hsrc _).1
      cover := fun x => by
        obtain ⟨p, hp⟩ := hcover x
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, hp⟩
      coord := fun i => coord _ (E.symm i)
      isEmbedding := fun i => (hsrc _).2
      image := fun i => himage _
      trans := fun i j => htrans _ _
      regular := fun i x hx => (hreg _ x hx).1
      dim := fun i x hx => (hreg _ x hx).2
      lift := fun i => lift (E.symm i)
      lift_one := fun i => ⟨E.symm i, fun k => by simp [lift]⟩
      lift_mem := fun i => hliftmem _
      compat := fun i j => hcompat _ _
      surj := fun z hz _ => by
        obtain ⟨p, x, hx, h⟩ := hsurj z hz
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, x, hx, h⟩
      inj := fun i j x hx x' hx' _ h => hinj _ _ x hx x' hx' h
      inv := fun i x hx _ p' hp' => hinv _ x hx p' hp'
      bd := fun i => bd _ (pC J) (E.symm i)
      le_bd := fun i => le_trans (Ideal.map_mono (sup_le_sup_right le_sup_left _)) Ideal.le_radical
      zero_bd := fun i => hzero _
      rc := rc _ (pC J)
      comp := comp _ (pC J)
      sncAt := fun i x hx => (hsc _ x hx).choose
      comp_eq := fun i x hx => (hsc _ x hx).choose_spec.1
      mult := fun f a hf hfP hz => ⟨fun k => ordAlong (compIdeal _ (pC J) k) _ f,
        fun i x hx => (hsc _ x hx).choose_spec.2 f a hf hfP hz⟩ }
  refine exists_isEmbedded_of_algRes hJ hJP (pcContract K ι _ e hP) R ?_ ?_ ?_
  · intro z hz
    obtain ⟨p, x, hx, h⟩ := hsurj z hz
    obtain ⟨i, rfl⟩ := E.symm.surjective p
    exact ⟨i, x, hx, h⟩
  · intro i j x hx x' hx' h
    exact hinj _ _ x hx x' hx' h
  · intro i x hx p' hp'
    exact hinv _ x hx p' hp'

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
