import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolyEqOfIsRowPar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfIota
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairsOfTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoinStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyJoinOfAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeStandardTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedRealizationPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceWeightPositiveStatement

noncomputable section

namespace GlobalTheory.ResLoc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

theorem continuous_qCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar p ≃+* ℂ) {Y : Type} [TopologicalSpace Y]
    {f : Y → Qbar q} (hf : Continuous f) : Continuous fun y => ι.symm (qCast h ι (f y)) := by
  subst h
  simpa [qCast] using hf

theorem nontrivial_V {D : D7} {M : MtFam D} (B : NLocBase D M) {j : ℕ} {w : D.what₂.places.Pl}
    (h : GlobalTheory.RowCopy.LamPos D (D.what₂.muTw w) j) {σ : D.what₂.FT} (hσ : D.what₂.isot j σ ≠ ⊥) : Nontrivial (B.V j w) := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have hne : D.what₂.thetaT (D.what₂.muTw w) j f ≠ 0 := fun e => by
    have h1 := (h σ).1 f hf
    have hl : ((D.what₂.lamP (D.what₂.muTw w) j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 hσ).ne'
    rw [e, map_zero] at h1
    exact hf0 ((smul_eq_zero.1 h1.symm).resolve_left hl)
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw w) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hne ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  exact ⟨⟨_, 0, (B.iV_basis j w b).1.ne_zero k⟩⟩

theorem exists_loc {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    {X : LocNd (lay0 D)} {T : LocTw X} (Sp : NdSpec Pl M C big X T) (hl : GlobalTheory.NRows.LamUsed D) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) {σ : D.what₂.FT} (hσ : D.what₂.isot j σ ≠ ⊥) {w : D.what₂.places.Pl} (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    ∃ i : X.nd.Loc, X.nd.j i = j ∧ X.nd.w i = w := by
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  haveI := nontrivial_V Sp.B (hl.at (Or.inr ⟨w, e⟩) h1 h2) hσ
  haveI : Nontrivial (Formalism.L2.heckeAlg Sp.B j w) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg Sp.B j w)
  obtain ⟨i, hi, -⟩ := Sp.mx_all j w h1 h2 hw I hI
  exact ⟨i, (X.nd.locs_mem _ _ _).1 hi⟩

theorem charpoly_lattice {D : D7} (hC : GlobalTheory.RowTie.ChebSplit D.nd) {Rw : RowSide D} (i : D.nd.Loc)
    (ι : Qbar (D.what₂.places.resChar (D.nd.w i)) ≃+* ℂ) (hι : D.naut.iotaQC i = qCast (D.nd.w_l i) ι)
    {σ : D.what₂.FT} (hW : ∀ w, D.naut.locW i σ w = Rw.locR σ w) {Sig : List (Formalism.BasicNotions.Part D.naut.CG)}
    {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)} (hP : HasParamW D.nd D.naut i σ Sig)
    (hR : IsRepOfSig D.nd D.naut i Sig ρ) {π : D.naut.CG D.R.r} (hπ : IsRowPar Rw σ π)
    {r : GalE D →* GL (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))} (hr : IsGaloisRepOf D π _ ι r) (g : GalE D) :
    ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)) =
      ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))).charpoly := by
  have hc : Continuous (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)) := by
    have := continuous_qCast (D.nd.w_l i) ι (GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i).1
    rw [← hι] at this
    exact this
  have hfin : (placesOver D.host.E (D.what₂.places.resChar (D.nd.w i)) ∪ ⋃ k, placesOver D.host.E (D.host.g k)).Finite :=
    (Formalism.L2.TwC.placesOver_finite' _ _ (D.what₂.places.resChar_prime _).ne_zero).union
      (Set.finite_iUnion fun k => Formalism.L2.TwC.placesOver_finite' _ _ (D.host.g_prime k).ne_zero)
  have hall := Filter.eventually_cofinite.1 (hR.2.2.and hfin.eventually_cofinite_notMem)
  rw [← Matrix.charpoly_map]
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.what₂.places.resChar (D.nd.w i))) D.R.r
    (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
      (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)))
    (fun g => ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))))
    _ (hC hall.toFinset) (hR.1.matrix_map hc) hr.1 ?_ g
  rintro y ⟨w, hw, hs, B, hB, hy⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hw
  obtain ⟨h1, h2⟩ := hw
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at h2
  apply Polynomial.map_injective ι.toRingHom ι.injective
  have e : ι.toRingHom.comp (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)) = iotaO D.nd D.naut i := by
    ext z
    simp
  rw [Matrix.charpoly_map, Polynomial.map_map, e, h1 B y hB hy, (hr.2.2 w h2.1).2.2 (hπ.1.unr w h2.2) B y hB hy,
    hP.2.2 w hs, hW w, hπ.2 w hs]

theorem resTied_of_lattices {D : D7} (hC : GlobalTheory.RowTie.ChebSplit D.nd) (Rw : RowSide D) (Pl : PlSide D) (hI : IotaOk D Pl)
    (hι : ∀ i : D.nd.Loc, D.naut.iotaQC i = qCast (D.nd.w_l i) (Pl.ι (D.nd.w i)))
    (hk : ∀ (i : D.nd.Loc) (y : D.nd.O i), ∃ h : iotaO D.nd D.naut i y ∈ Pl.plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (Pl.plκ (D.nd.w i) (IsLocalRing.residue (Pl.plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y))
    (hW : ∀ i σ w, D.naut.locW i σ w = Rw.locR σ w)
    (hL : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∃ i : D.nd.Loc, D.nd.j i = j ∧ D.nd.w i = w)
    (hrep : GlobalTheory.RowTie.RowRepAtG D) : ResTied D Rw := by
  refine resTied_of_plSide hI fun w hw σ π r hg ⟨j, h1, h2, hσ⟩ hπ hr => ?_
  obtain ⟨i, rfl, rfl⟩ := hL j h1 h2 σ hσ w hw
  obtain ⟨Sig, ρ, hP, hR, -⟩ := hrep i σ hσ hg
  obtain ⟨hss, hcp⟩ := D.rbar_tie i σ Sig ρ hP hR
  refine ⟨hss, fun g => ?_⟩
  let φ : D.nd.O i →+* Zbar (D.what₂.places.resChar (D.nd.w i)) :=
    ((Pl.ι (D.nd.w i)).symm.toRingHom.comp (iotaO D.nd D.naut i)).codRestrict _
      fun y => (Pl.plB_eq _ _).1 (hk i y).1
  refine ⟨((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map φ, ?_, ?_⟩
  · rw [Polynomial.map_map]
    exact charpoly_lattice hC i _ (hι i) (hW i σ) hP hR hπ hr g
  · apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom (RingEquiv.injective _)
    rw [hcp g, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext y
    obtain ⟨h, e⟩ := hk i y
    refine Eq.trans ?_ e
    change fbCast _ _ _ (Pl.plκ (D.nd.w i) (IsLocalRing.residue (Pl.plB (D.nd.w i)) ⟨_, _⟩)) = _
    congr 4
    exact (Pl.ι (D.nd.w i)).apply_symm_apply _

def plL {D : D7} (L : LocAll (lay0 D)) (Pl : PlSide D) : PlSide (withLoc L) := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩

set_option maxHeartbeats 1000000 in

theorem resTied_withLoc (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D)
    (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D))
    (Sp : NdSpec A.pl M C big L.X L.T) (Au : AutSpec A M tup Sp.iq L.Y L.C) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
    (hlam : GlobalTheory.NRows.LamUsed D) (hrep : GlobalTheory.RowTie.RowRepAtG (withLoc L)) (Rw : RowSide (withLoc L))
    (hRw : ∀ σ w, Rw.locR σ w = A.row.locR σ w) : ResTied (withLoc L) Rw :=
  resTied_of_lattices (D := withLoc L) hC Rw (plL L A.pl) A.iota Au.iotaQC Au.kFbar
    (fun i σ w => (Au.locW i σ w).trans (hRw σ w).symm)
    (fun _ h1 h2 _ hσ _ hw => exists_loc Sp hlam h1 h2 hσ hw) hrep

set_option maxHeartbeats 1000000 in

theorem resTied_built (hC : GlobalTheory.Published.ChebotarevDegreeOne) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (b : NBuilt hL D)
    (hlam : GlobalTheory.NRows.LamUsed D) (hrep : GlobalTheory.RowTie.RowRepAtG D) (Rw : RowSide D) (hRw : HEq Rw.locR b.A.row.locR) :
    ResTied D Rw := by
  obtain ⟨D₀, cf, jE, A, _, _, _, _, _, _, _, _, _, _, _, M, C, tp, _, _, big, L, Sp, Au, _, rfl⟩ := b
  exact resTied_withLoc D₀ cf jE A M C tp.tup big L Sp Au (GlobalTheory.ChebSplitDense.chebSplit hC D₀.nd) hlam hrep Rw
    fun σ w => congrFun (congrFun (eq_of_heq hRw) σ) w

theorem resTied_built_of_rows (hC : GlobalTheory.Published.ChebotarevDegreeOne) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (b : NBuilt hL D)
    (hlam : GlobalTheory.NRows.LamUsed D) (hA : GlobalTheory.NRows.RowsA D) (h42 : SumRepresentations.Conclusion42 D) (hρ : GlobalDatumResidualRepCondition D)
    (hP : GlobalTheory.SplitRead.RowPoint D.nd D.naut) (Rw : RowSide D) (hRw : HEq Rw.locR b.A.row.locR) : ResTied D Rw :=
  resTied_built hC b hlam (GlobalTheory.RowRepOcc.rowRepAtG_of_rowPoint D hA.tie0 hA.a2 hA.a5 h42 hρ hA.gsp hP) Rw hRw

theorem exists_galRep_cast {D : D7} {a p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {ι : Qbar p ≃+* ℂ} {π : D.naut.CG a}
    {r : GalE D →* GL (Fin a) (Qbar p)} (hr : IsGaloisRepOf D π p ι r) : ∃ r', IsGaloisRepOf D π q (qCast h ι) r' := by
  subst h
  exact ⟨r, hr⟩

theorem resTied_of_points {D : D7} (hC : GlobalTheory.RowTie.ChebSplit D.nd) (Rw : RowSide D) (Pl : PlSide D) (hI : IotaOk D Pl)
    (hι : ∀ i : D.nd.Loc, D.naut.iotaQC i = qCast (D.nd.w_l i) (Pl.ι (D.nd.w i)))
    (hk : ∀ (i : D.nd.Loc) (y : D.nd.O i), ∃ h : iotaO D.nd D.naut i y ∈ Pl.plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (Pl.plκ (D.nd.w i) (IsLocalRing.residue (Pl.plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y))
    (hW : ∀ i σ w, D.naut.locW i σ w = Rw.locR σ w) (hLaw : GlobalTheory.ThetaExh.ParamLaws D.nd D.naut) (hO : SumRepresentations.hypO D)
    (hXi : GlobalTheory.SplitRead.XiOverO D.nd D.naut) (hpair : ∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i)
    (hL : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∃ (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i), D.nd.w i = w ∧ GlobalTheory.ThetaExh.Pairs D.nd D.naut i σ P ∧
        D.naut.ptV i P = some x) : ResTied D Rw := by
  refine resTied_of_plSide hI fun w hw σ π r hg ⟨j, h1, h2, hσ⟩ hπ hr => ?_
  obtain ⟨i, P, x, rfl, hPσ, hx⟩ := hL j h1 h2 σ hσ w hw
  obtain ⟨r', hr'⟩ := exists_galRep_cast (D.nd.w_l i) hr
  rw [← hι i] at hr'
  obtain ⟨ρ, hR⟩ := lattice_of_point D.nd D.naut hLaw hO hXi i x P hx π
    (fun v hv => by rw [hpair i σ P hPσ v hv, hW, hπ.2 v hv]) hπ.1.unr r' hr'.1 hr'.2.1
    (fun v hv hu B s hB hs => by rw [Matrix.charpoly_map]; exact (hr'.2.2 v hv).2.2 hu B s hB hs)
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Ranks.r]; omega
  have hP : HasParamW D.nd D.naut i σ [⟨D.R.r, π, 1⟩] :=
    ⟨by simp [hr1], by simp [rankIso], fun v hv => by rw [GlobalTheory.RowRepOcc.isoLoc_one, hW, hπ.2 v hv]⟩
  obtain ⟨hss, hcp⟩ := D.rbar_tie i σ _ ρ hP hR
  refine ⟨hss, fun g => ?_⟩
  let φ : D.nd.O i →+* Zbar (D.what₂.places.resChar (D.nd.w i)) :=
    ((Pl.ι (D.nd.w i)).symm.toRingHom.comp (iotaO D.nd D.naut i)).codRestrict _
      fun y => (Pl.plB_eq _ _).1 (hk i y).1
  refine ⟨((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map φ, ?_, ?_⟩
  · rw [Polynomial.map_map]
    exact charpoly_lattice hC i _ (hι i) (hW i σ) hP hR hπ hr g
  · apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom (RingEquiv.injective _)
    rw [hcp g, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext y
    obtain ⟨h, e⟩ := hk i y
    refine Eq.trans ?_ e
    change fbCast _ _ _ (Pl.plκ (D.nd.w i) (IsLocalRing.residue (Pl.plB (D.nd.w i)) ⟨_, _⟩)) = _
    congr 4
    exact (Pl.ι (D.nd.w i)).apply_symm_apply _

theorem points_of_tied (hP : GlobalTheory.NRows.Hypotheses₂) (hH : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (X : GlobalTheory.NRows.Tied hL D) :
    GlobalTheory.ThetaExh.ParamLaws D.nd D.naut ∧ GlobalTheory.SplitRead.XiOverO D.nd D.naut ∧ (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) ∧
      ∀ (i : D.nd.Loc) σ, (∃ f ∈ D.what₂.isot (D.nd.j i) σ, D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f ≠ 0) →
        ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x' : D.nd.X i'), D.nd.j i' = D.nd.j i ∧ D.nd.w i' = D.nd.w i ∧
          GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  obtain ⟨J⟩ := GlobalTheory.T.nonempty_join_of_agreement hH hD hL D X.P X.X X.agree
  have hRM : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D X.P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hP.fin hL D X.P hRM
  have hU := GlobalTheory.RowUnitProof.rowUnit_of_isTrue hL D X.P hRM S hT
  have hPR := GlobalTheory.T.pair_reading_of_join hP.bz hL D X.P J S hT hU
  exact ⟨GlobalTheory.RowLaws.paramLaws_of_tie X.P.T,
    xiOverO D X.P.cf X.P.C X.P.tp X.P.chr X.P.val (GlobalTheory.AutomorphismSplitting.tieAut_and_split hP.fin hL D X.P).1
      (GlobalTheory.T.adm2_of_prints_localLanglands hP hL D X.P) (GlobalTheory.ChebSplitDense.chebSplit hP.cheb D.nd),
    GlobalTheory.SplitPairLift.main hP.bz hP.bern hP.howe _ _ _ D.nd D.naut X.P.T S hLaws hU hPR,
    exists_pair_point D X.P.M X.P.H.hecke X.P.H.av X.P.H.cover (GlobalTheory.T.hecke_standard_twist hL D X.P)⟩

set_option maxHeartbeats 1000000 in

theorem resTied_built_of_tied (hP : GlobalTheory.NRows.Hypotheses₂) (hH : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (b : NBuilt hL D) (X : GlobalTheory.NRows.Tied hL D) (hO : SumRepresentations.hypO D) (hd : DV.LamDef D)
    (hpos : ∀ v, TwistedAt D v → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP (D.what₂.muTw v) j σ)
    (hloc : ∀ v, TwistedAt D v → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j)
    (Rw : RowSide D) (hRw : HEq Rw.locR b.A.row.locR) : ResTied D Rw := by
  obtain ⟨a1, a2, a3, a4⟩ := points_of_tied hP hH hD X
  have hpt : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∃ (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i), D.nd.w i = w ∧ GlobalTheory.ThetaExh.Pairs D.nd D.naut i σ P ∧
        D.naut.ptV i P = some x := by
    intro j h1 h2 σ hσ w hw
    obtain ⟨i, rfl, rfl⟩ := hloc w hw j h1 h2 σ hσ
    obtain ⟨i', P, x, -, e, h⟩ := a4 i σ (exists_thetaT_ne hd h1 h2 hσ (by rw [D.nd.mu_w i]; exact hpos _ hw _ h1 h2 σ hσ))
    exact ⟨i', P, x, e, h⟩
  clear X hd hpos hloc a4
  obtain ⟨D₀, cf, jE, A, _, _, _, _, _, _, _, _, _, _, _, M, C, tp, _, _, big, L, Sp, Au, _, rfl⟩ := b
  exact resTied_of_points (D := withLoc L) (GlobalTheory.ChebSplitDense.chebSplit hP.cheb D₀.nd) Rw (plL L A.pl) A.iota Au.iotaQC Au.kFbar
    (fun i σ w => (Au.locW i σ w).trans (congrFun (congrFun (eq_of_heq hRw) σ) w).symm) a1 hO a2 a3 hpt

end GlobalTheory.ResLoc

namespace GlobalTheory.ResLoc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 1000000 in

theorem resTied_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.EigTie.ResTied (w.D Z) Rw := by
  intro hP hL
  refine EvG.imp (Model.AtMem.and (Model.AtMem.and (GlobalTheory.T.exists_tied_realization_place hP hL) (GlobalTheory.T.twisted_place_weight_positive hP hL)) (GlobalTheory.T.twisted_place_local_index hP hL))
    fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hE hX hp Rw hRw => ?_
  obtain ⟨⟨⟨X, -⟩, hpos⟩, hloc⟩ := H kp w Z Wt p0 t nch n xd c hE hX hp
  obtain ⟨e⟩ := hE
  exact resTied_built_of_tied hP.what₂ hP.hc hP.decay c.a.nt.toNBuilt X
    (e : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd).large.1 t.r.Y.lam hpos hloc Rw hRw

end GlobalTheory.ResLoc

end
