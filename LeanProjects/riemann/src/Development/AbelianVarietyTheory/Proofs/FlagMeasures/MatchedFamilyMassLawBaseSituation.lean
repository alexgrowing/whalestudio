import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusLocalDataProductLocalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericGenericTermsClosedUnderLocalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPairStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeWeightTermDatumPosStatement

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinitePlaceMassFactors

theorem infinite_finPlaces (K : Type) [Field K] [NumberField K] :
    Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      la.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

theorem wt_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ}
    {P : LocNG.FPair H r} (d : LocNG.Datum P) : LocNG.Datum.wt d d = 1 := by
  unfold LocNG.Datum.wt LocNG.volRel
  simp [Subgroup.relIndex_self]

end GlobalTheory.FinitePlaceMassFactors

namespace GlobalTheory.FinitePlaceMassFactors

theorem dl_loc_unsigned {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T)
    (F' : FlagG (VS D) D.R.rS T') (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    (locH Z p).Dl (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)) (fun a => frFac Z.δ p a • baseChange₂ D p (F'.fvec a)) l =
      (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i)) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F F' l) := by
  have hZ : (locH Z p).Zhat (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a))
      (fun a => frFac Z.δ p a • baseChange₂ D p (F'.fvec a)) =
      Matrix.diagonal (fun a => (Z.M p).L.cj (frFac Z.δ p a)) * (Formalism.MainNotions.S.Zhat F F').map (D.s.atP p).ιE *
        Matrix.diagonal (fun b => frFac Z.δ p b) := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    show LocFacts₂ Z.M p (frFac Z.δ p b • baseChange₂ D p (F'.fvec b)) (frFac Z.δ p a • baseChange₂ D p (F.fvec a)) = _
    rw [Formalism.L2.SG.Pf.BBTie.formP_bc, Matrix.map_apply]
    simp only [Formalism.MainNotions.S.Zhat]
    ring
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl leadMinorE
  rw [dif_pos hl, dif_pos hl, hZ]
  have hsub : (Matrix.diagonal (fun a => (Z.M p).L.cj (frFac Z.δ p a)) *
        (Formalism.MainNotions.S.Zhat F F').map (D.s.atP p).ιE *
        Matrix.diagonal (fun b => frFac Z.δ p b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i))) *
        ((Formalism.MainNotions.S.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE *
        Matrix.diagonal (fun i => frFac Z.δ p (Fin.castLE hl i)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have hdm : ∀ A : Matrix (Fin l) (Fin l) D.host.E, (A.map (D.s.atP p).ιE).det = (D.s.atP p).ιE A.det :=
    fun A => (RingHom.map_det _ A).symm
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hdm, Finset.prod_mul_distrib]
  ring

theorem gval_ne_of_primeTo : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)),
    Based Z FP Tn T'n F F' → ∀ p : PlF D, (FP p).PrimeTo → Gval F F' ≠ 0 := by
  intro D Z FP Tn T'n F F' hB p hP hG0
  obtain ⟨-, ⟨-, y, -, hy⟩, -⟩ := hP
  obtain ⟨hA, hB', hT, hT'⟩ := hB p
  set c := ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p i.castSucc) * frFac Z.δ p i.castSucc with hc
  have h1 := dl_loc_unsigned Z p F.fl F'.fl (D.R.rS + 1) le_rfl
  rw [Fin.prod_univ_castSucc] at h1
  simp only [Fin.castLE_rfl, id, Formalism.L2.SG.Pf.BBTie.bt_frFac_last, mul_one, map_one] at h1
  have h2 : (locH Z p).Dl (fun a => frFac Z.δ p a • baseChange₂ D p (F.fl.fvec a))
      (fun a => frFac Z.δ p a • baseChange₂ D p (F'.fl.fvec a)) D.R.rS =
      c * (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl D.R.rS) := by
    rw [dl_loc_unsigned Z p F.fl F'.fl D.R.rS (Nat.le_succ _)]
    rfl
  have hcj : ∀ x : D.host.E, (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) :=
    fun x => cj_iota (Z.hcj p) x
  have hG' : (FP p).Gv = (c * (Z.M p).L.cj c) * (D.s.atP p).ιE (Gval F F') := by
    unfold Formalism.MainNotions.S.LocNG.FPair.Gv Loc.HermSp.Gdet Loc.HermSp.normE
    rw [hA, hB', hT, hT']
    erw [h1, h2]
    simp only [map_mul, hcj, Gval, Gflag, map_sub, map_natCast]
    ring
  rw [hG', hG0, map_zero, mul_zero, zero_mul] at hy
  exact zero_ne_one hy

end GlobalTheory.FinitePlaceMassFactors

namespace GlobalTheory.FinitePlaceMassFactors

theorem finprod_wt_eq {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (P : Finset (PlF D)) (d0 d : Dat Z FP) (h : ∀ p, p ∉ P → d p = d0 p) :
    ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p) = ∏ p ∈ P, LocNG.Datum.wt (d0 p) (d p) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
  by_contra hP
  apply hp
  show LocNG.Datum.wt (d0 p) (d p) = 1
  rw [h p hP, wt_self]

theorem tied_mass_law : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → ∀ (K : Type) (S : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → K), GlobalTheory.SnFam.FamQ Y u u' S TS cls → ∀ (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) K (NuC D)), FamTie TS cls (nmlOf Y u u') γ Fm → OrbitFamilyIdentityAt Fm Fm.V0 → ∃ (w : Point D.host.E (D.R.rS + 1)) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (Y0 : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), toPts w = γ ∧ (∃ n ∈ NRat (lf D (X.Fu u)), ∀ a, frame F a = n (frame (lf D (X.Fu u)) a)) ∧ ZhatOM (ZhatL F F') = ptMat w ∧ TotPos (Gval F F') ∧ BaseOK (Tu D u) (Tu D u') F F' Fm.P Fm.d0 ∧ MassLaw F F' Fm.P Fm.d0 Fm.V0 ∧ ∀ p ∈ Fm.P, Fm.ngenL p = (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p))).toReal ∧ ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t ∧ (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p) (Y0 p) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ K S TS cls hFQ γ Fm hFT hG5
  obtain ⟨w, F00, F'0, F'1, hw, hDs, -, hn0, hZ, hbase, -, hgood, hstd, ⟨t₀, ht₀, hpt₀, ht₀loc⟩, hd0P,
    ⟨Λ₀, hΛ₀, hΛ₀loc⟩, hdat, -, hngen⟩ := hFT
  subst hw
  set F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E) := ⟨F00.fl, F00.fl.z⟩ with hFdef
  set F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) := ⟨F'0.fl, F'0.fl.z⟩ with hF'def
  have hBased : Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' := fun p => hbase p
  have hZF : ZhatOM (ZhatL F F') = ptMat w := hZ
  have hG : Gval F F' ≠ 0 := by
    haveI : Infinite (PlF D) := infinite_finPlaces D.host.F
    obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset Fm.P
    exact gval_ne_of_primeTo D (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' hBased p (hgood p hp)
  have hRel : ∀ p, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p)) := fun p =>
    (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w F00 F'0 hZ hG p).2 _ (hbase p)
  have hTot : TotPos (Gval F F') := fun τ =>
    (Formalism.MainNotions.LatticeGluingRadicals.b_G_pos (Formalism.MainNotions.LatticeGluingRadicals.p_starConj D) (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) F F' rfl rfl hG
      (Formalism.MainNotions.LatticeGluingRadicals.p_posX D _ (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) F) _).1
  have hd0 : ∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ := fun p =>
    if hp : p ∈ Fm.P then hd0P p hp else ⟨_, ht₀loc p hp⟩
  have hΛfin : {p | ¬ ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀}.Finite :=
    Fm.P.finite_toSet.subset fun p hp => by
      by_contra h
      exact hp ⟨_, hΛ₀loc p h, rfl⟩
  obtain ⟨V1, hV1, hmass⟩ := GlobalTheory.T.mass_genus_local_data_product_local_weights D X Y u u' F F' w hZF hG (zOf Y) Fm.FP hBased hRel Fm.d0 hd0
    ⟨Λ₀, hΛ₀, hΛfin⟩
  obtain ⟨hcNG, hcGen, -, -⟩ := GlobalTheory.T.nonGeneric_generic_terms_closed_under_localUnitary D X Y u u' F F' w hZF hG (zOf Y) Fm.FP hBased hRel
  have hLC : LocClosed F F' (zOf Y) Fm.FP TS := by
    rw [hFQ.1]
    intro t t' Λ Λ' h1 h2 h3 ht
    obtain ⟨hGt, hSt⟩ := ht
    by_cases hg : (Y.tO u u').gener t
    · have h' : t' ∈ (Y.tO u u').genSet := hcGen t t' Λ Λ' h1 h2 h3 ⟨hGt, hg⟩
      refine ⟨h'.1, ?_⟩
      have e : (¬ (Y.tO u u').gener t') = (¬ (Y.tO u u').gener t) := propext (by simp [hg, h'.2])
      rw [e]; exact hSt
    · have h' : t' ∈ (Y.tO u u').ngSet := hcNG t t' Λ Λ' h1 h2 h3 ⟨hGt, hg⟩
      refine ⟨h'.1, ?_⟩
      have e : (¬ (Y.tO u u').gener t') = (¬ (Y.tO u u').gener t) := propext (by simp [hg, h'.2])
      rw [e]; exact hSt
  have hdat' : ∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
      ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
        ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν →
          (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (Formalism.L2.SG.TermOp.wt t) ^ 2 := by
    intro c ν
    have h := hdat c ν
    refine ⟨fun hn => ?_, fun d hd => ?_⟩
    · rw [hn] at h; exact h
    · rw [hd] at h; exact h
  have hΛrows : ∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P →
      ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀ :=
    ⟨Λ₀, hΛ₀, fun p hp => ⟨_, hΛ₀loc p hp, rfl⟩⟩

  have hV : Fm.V0 = V1 := by
    cases hd : Fm.dat (cls t₀) (nmlOf Y u u' t₀) with
    | none => exact absurd ⟨t₀, ht₀, rfl, hpt₀, rfl⟩ ((hdat' _ _).1 hd)
    | some d =>
      set dd : Dat (zOf Y) Fm.FP := fun p => if hp : p ∈ Fm.P then (d ⟨p, hp⟩).1 else Fm.d0 p with hdd
      have hdd1 : ∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1 := fun p hp => by simp [hdd, hp]
      have hdd2 : ∀ p, p ∉ Fm.P → dd p = Fm.d0 p := fun p hp => by simp [hdd, hp]
      obtain ⟨hddT, hsum⟩ := GlobalTheory.T.rowWeights_localOrbits_sum_eq_genusMass D X Y u u' F F' w hZF hG TS cls Fm hBased hFQ.2.1 hLC hDs hstd
        hΛrows hdat' d ⟨(cls t₀, nmlOf Y u u' t₀), hd⟩ dd hdd1 hdd2
      have hfin : {p | dd p ≠ Fm.d0 p}.Finite :=
        Fm.P.finite_toSet.subset fun p hp => by
          by_contra h
          exact hp (hdd2 p h)
      have hm := hmass dd hddT hfin
      have h5 := hG5.2 d ⟨(cls t₀, nmlOf Y u u' t₀), hd⟩
      rw [hsum, hm, finprod_wt_eq Fm.P Fm.d0 dd hdd2] at h5
      have hprod : ∏ p, Fm.toL.wt p (d p) = ∏ p ∈ Fm.P, LocNG.Datum.wt (Fm.d0 p) (dd p) := by
        rw [← Finset.prod_coe_sort Fm.P]
        refine Finset.prod_congr rfl fun p _ => ?_
        show LocNG.Datum.wt (Fm.d0 p.1) (d p).1 = _
        rw [hdd1 p.1 p.2]
        rfl
      rw [hprod] at h5
      have hpos : 0 < ∏ p ∈ Fm.P, LocNG.Datum.wt (Fm.d0 p) (dd p) :=
        Finset.prod_pos fun p _ => GlobalTheory.T.relative_weight_term_datum_pos D (zOf Y) p (Fm.FP p) (hRel p) _ _ (hd0 p) (hddT p)
      rw [ENNReal.ofReal_eq_ofReal_iff (mul_pos hV1 hpos).le (mul_pos hG5.1 hpos).le] at h5
      exact (mul_right_cancel₀ hpos.ne' h5).symm
  refine ⟨w, F, F', fun p => (locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1), rfl, hn0, hZF, hTot,
    ⟨hBased, hRel, hgood, hd0, Λ₀, hΛ₀, fun p hp => ?_⟩, fun d hoff hterm => ?_, hngen⟩
  · have e1 := (hbase p).2.2.1
    have e2 := (hbase p).2.2.2
    simp only [tm, e1, e2]
    exact hΛ₀loc p hp
  · have hfin : {p | d p ≠ Fm.d0 p}.Finite :=
      Fm.P.finite_toSet.subset fun p hp => by
        by_contra h
        exact hp (hoff p h)
    rw [hmass d hterm hfin, finprod_wt_eq Fm.P Fm.d0 d hoff, hV]

end GlobalTheory.FinitePlaceMassFactors
