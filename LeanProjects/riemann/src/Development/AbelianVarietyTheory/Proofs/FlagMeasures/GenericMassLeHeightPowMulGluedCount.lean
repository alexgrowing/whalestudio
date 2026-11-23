import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassPairingClassBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOntoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipotStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFramesPrescribedLocalClassesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedCountGluedLatticesEqMassMulLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCountStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueUnimodularLatticeRepsMoveIsometryFramesStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGDictPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChangeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairValueInvariantUnitriangularChangeStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMassBound

theorem tri_trans : ∀ (K W : Type) [CommRing K] [AddCommGroup W] [Module K W] (n : ℕ) (f g h : Fin n → W), Tri K f g → Tri K g h → Tri K f h := by
  intro K W _ _ _ n f g h ⟨A, hA, hfg⟩ ⟨B, hB, hgh⟩
  refine ⟨A * B, ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : c < a
    · rw [hA.1 a c hca, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hba (not_lt.1 hca)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h1 | h1
      · rw [hA.1 a c h1, zero_mul]
      · rw [hB.1 c a h1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [hgh b]
    have e : ∀ c, g c = ∑ a, A a c • f a := hfg
    simp only [e, Finset.smul_sum, smul_smul]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]

theorem mapLF_frame : ∀ (D : D7) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (m : GV D), m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame (Formalism.L2.SG.TermOp.mapLF m F) a = m (frame F a)) ∧ (Formalism.L2.SG.TermOp.mapLF m F).zt = m F.zt ∧ (Formalism.L2.SG.TermOp.mapLF m F).fl.z = m F.fl.z := by
  intro D T F m hm
  rw [Formalism.L2.SG.TermOp.mapLF, dif_pos hm]
  refine ⟨fun a => ?_, rfl, rfl⟩
  simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · simp

theorem zhat_isom : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (m : GV D), m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame G a = m (frame F a)) → (∀ a, frame G' a = m (frame F' a)) → ZhatL G G' = ZhatL F F' := by
  intro D T T' F G F' G' m hm hG hG'
  funext a b
  have h1 : G.fl.fvec a = m (F.fl.fvec a) := hG a
  have h2 : G'.fl.fvec b = m (F'.fl.fvec b) := hG' b
  simp only [ZhatL, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, h1, h2]
  rw [hm]

theorem zhat_chg : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Chg (frame F) A (frame G) → Chg (frame F') A' (frame G') → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' := by
  intro D T T' F G F' G' A A' hc hc'
  funext a b
  have h1 : G.fl.fvec a = ∑ c, A c a • F.fl.fvec c := hc a
  have h2 : G'.fl.fvec b = ∑ c, A' c b • F'.fl.fvec c := hc' b
  simp only [ZhatL, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, h1, h2, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [starRingEnd_apply, RingHom.id_apply]
  ring

theorem cell_chg : ∀ {K : Type} [CommRing K] {r : ℕ} (Z L U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (w : Point K (r + 1)), IsLoUni L → Uni U → ZhatOM Z = ptMat w → IsInCell (ZhatOM (L * Z * U)) w := by
  intro K _ r Z L U w hL hU hZ
  set s : Fin (r + 1) → K := fun b => (-1 : K) ^ (r - b.val) with hsdef
  have hs : ∀ b, s b * s b = 1 := by
    intro b
    simp only [hsdef, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hZS : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ZhatOM M = M * Matrix.diagonal s := by
    intro M
    funext a b
    simp [ZhatOM, Matrix.mul_diagonal, hsdef, mul_comm]
  have hDD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, show (fun i => s i * s i) = fun _ => (1 : K) from funext hs, Matrix.diagonal_one]
  refine ⟨L, Matrix.diagonal s * U * Matrix.diagonal s, hL, fun i j => ⟨fun hji => ?_, fun hij => ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hU.1 i j hji]
  · subst hij
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hU.2 i, mul_one]
    exact hs i
  · rw [← hZ, hZS, hZS]
    rw [show L * (Z * Matrix.diagonal s) * (Matrix.diagonal s * U * Matrix.diagonal s) =
      L * Z * (Matrix.diagonal s * Matrix.diagonal s) * U * Matrix.diagonal s by simp only [Matrix.mul_assoc], hDD,
      Matrix.mul_one]

theorem frameN : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r), Fr.T ≠ 0 → ∀ (g0 g : Fin (r + 1) → V)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∃ n ∈ Fr.N, g0 = fun b => n (Fr.f b)) → Uni A → Chg g0 A g →
    ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr hT g0 g A hg0 hA hc
  have u := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hOK H r Fr hT
  obtain ⟨n, hn, rfl⟩ := hg0
  exact u.2.2 g (tri_trans E V (r + 1) _ _ _ (u.2.1 n hn) ⟨A, hA, hc⟩)

theorem genericMass_le_heightPow_mul_glueSum : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), 4 * D.R.rS + 7 ≤ D.R.k → ∀ {K : Type} (Fm : LocFam (zOf Y) K (NuC D)) (γ : PN.Pts D.host.E D.R.rS), 0 < Fm.V0 → (∃ (w : Point D.host.E (D.R.rS + 1)) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (Y0 : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), toPts w = γ ∧ (∃ n ∈ NRat (lf D (X.Fu u)), ∀ a, frame F a = n (frame (lf D (X.Fu u)) a)) ∧ ZhatOM (ZhatL F F') = ptMat w ∧ TotPos (Gval F F') ∧ BaseOK (Tu D u) (Tu D u') F F' Fm.P Fm.d0 ∧ MassLaw F F' Fm.P Fm.d0 Fm.V0 ∧ ∀ p ∈ Fm.P, Fm.ngenL p = (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p))).toReal ∧ ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t ∧ (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p) (Y0 p)) → 0 < Fm.toL.ngenTot ∧ (∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp) ∧ ∃ (w : Point D.host.E (D.R.rS + 1)) (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), toPts w = γ ∧ G'.zt = G'.fl.z ∧ TotPos (Gval (lf D (X.Fu u)) G') ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w ∧ ∀ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s → s.Nonempty ∧ Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) * glueSum (lf D (X.Fu u)) G' s := by
  intro D X Y u u' hk K Fm γ hV0 hyp
  obtain ⟨w, F, F', Y0, hw, hFn, hZw, hTP, hBase, hML, hloc⟩ := hyp
  have hBased := hBase.1
  have hRel := hBase.2.1
  have hd0 := hBase.2.2.2.1

  have hOK : ∀ p : PlF D, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hpos : ∀ p ∈ Fm.P, 0 < Fm.ngenL p ∧ ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p)) ≠ ⊤ ∧
      1 ≤ (Fm.FP p).Hp := by
    intro p hp
    obtain ⟨hng, d, t, ht, hc⟩ := hloc p hp
    obtain ⟨g0, g1, -, -⟩ := GlobalTheory.mass_pairingClass_bounds ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS D.R.k (Fm.FP p)
      hk (rank_Vp p) (hRel p) (Fm.R p) (Fm.d0 p) (hd0 p) d t ht (Y0 p) (clsLoc ((zOf Y).M p) (Y0 p)) rfl hc _ rfl
    refine ⟨?_, g1, ?_⟩
    · rw [hng]; exact ENNReal.toReal_pos g0.ne' g1
    · obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := Formalism.MainNotions.KappaEndpoints.ng_factors (hOK p) (hRel p).2.2.1 ht
      unfold LocNG.FPair.Hp
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos (mul_pos a0 b0) c0) ?_ (by norm_num)
      exact mul_le_one₀ (mul_le_one₀ a1 b0.le b1) c0.le c1
  have hTot : 0 < Fm.toL.ngenTot := by
    show 0 < Fm.V0 * ∏ p : {p // p ∈ Fm.P}, Fm.ngenL p.1
    exact mul_pos hV0 (Finset.prod_pos fun p _ => (hpos p.1 p.2).1)
  refine ⟨hTot, fun p hp => (hpos p hp).2.2, ?_⟩

  choose dd tt htt hcls using fun p (hp : p ∈ Fm.P) => (hloc p hp).2
  let f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p := fun p =>
    if hp : p ∈ Fm.P then (tt p hp).f else scaled (zOf Y) p (frame F)
  let f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p := fun p =>
    if hp : p ∈ Fm.P then (tt p hp).f' else scaled (zOf Y) p (frame F')
  have hAf : ∀ p, (Fm.FP p).A.f = scaled (zOf Y) p (frame F) := fun p => (hBased p).1
  have hBf : ∀ p, (Fm.FP p).B.f = scaled (zOf Y) p (frame F') := fun p => (hBased p).2.1
  have hAT : ∀ p, (Fm.FP p).A.T ≠ 0 := fun p => (hRel p).2.2.2.2.2.2.2.1
  have hBT : ∀ p, (Fm.FP p).B.T ≠ 0 := fun p => (hRel p).2.2.2.2.2.2.2.2.2.1
  have htri : ∀ p ∈ Fm.P, Tri (D.s.atP p).Ep (scaled (zOf Y) p (frame F)) (f p) ∧
      Tri (D.s.atP p).Ep (scaled (zOf Y) p (frame F')) (f' p) := by
    intro p hp
    obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := htt p hp
    have u1 := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).A (hAT p)
    have u2 := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).B (hBT p)
    have e1 : f p = (tt p hp).f := dif_pos hp
    have e2 : f' p = (tt p hp).f' := dif_pos hp
    rw [e1, e2, ← hAf p, ← hBf p, hfn, hfn']
    exact ⟨u1.2.1 n hn, u2.2.1 n' hn'⟩
  obtain ⟨G, G'', hStd, hch⟩ := GlobalTheory.T.exists_rational_frames_prescribed_local_classes D (zOf Y) u u' F F' Fm.P f f' htri

  have hlocw : ∀ p ∈ Fm.P, ∃ wp : ℝ, 0 < wp ∧ wp ≤ (Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2) ∧
      ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p)) =
        ENNReal.ofReal wp * locSum G G'' p (Fm.R p) (Fm.d0 p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc1, hc2⟩ := hch p hp
    have e1 : f p = (tt p hp).f := dif_pos hp
    have e2 : f' p = (tt p hp).f' := dif_pos hp
    rw [e1] at hc1
    rw [e2] at hc2
    obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := htt p hp
    have hN := frameN ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).A (hAT p) _ _ A ⟨n, hn, hfn⟩ hA hc1
    have hN' := frameN ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).B (hBT p) _ _ A' ⟨n', hn', hfn'⟩ hA' hc2
    have hZc := GlobalTheory.T.localPairingClass_stable_unitriangularChange ((zOf Y).M p) (locH (zOf Y) p) D.R.rS (Y0 p) _ _ _ _ A A' hA hA' hint hc1 hc2 (hcls p hp)
    obtain ⟨wp, h0, h1, h2⟩ := GlobalTheory.T.mass_class_eq_weight_count_alt ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS D.R.k (Fm.FP p) hk
      (rank_Vp p) (hRel p) (Fm.R p) (Fm.d0 p) _ _ hN hN' (Y0 p) (clsLoc ((zOf Y).M p) (Y0 p)) rfl hZc
      ⟨dd p hp, tt p hp, htt p hp, hcls p hp⟩
    exact ⟨wp, h0, h1, h2⟩

  have hTu : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have fc := GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D (lf D (X.Fu u)) hTu
  have hTri1 : Tri D.host.E (frame (lf D (X.Fu u))) (frame F) := (fc.2 F).2 hFn
  obtain ⟨m, hm, hGm⟩ := (fc.2 G).1 (tri_trans _ _ _ _ _ _ hTri1 hStd.1)
  have hmI : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hm.1
  have hmI' : m⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := inv_mem hmI
  obtain ⟨hfr, hzt, hz⟩ := mapLF_frame D G'' m⁻¹ hmI'
  have hG''m : ∀ a, frame G'' a = m (frame (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') a) := by
    intro a
    rw [hfr a]
    exact (DFunLike.congr_fun (mul_inv_cancel m) (frame G'' a)).symm
  have hzt' : (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').zt = (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').fl.z := by
    rw [hzt, hz, hStd.2.2.2.1]
  obtain ⟨A, hA, hcA⟩ := hStd.1
  obtain ⟨A', hA', hcA'⟩ := hStd.2.1
  have hZG := zhat_chg D F G F' G'' A A' hcA hcA'
  have hZiso : ZhatL G G'' = ZhatL (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') :=
    zhat_isom D _ G _ G'' m hmI hGm hG''m
  refine ⟨w, Formalism.L2.SG.TermOp.mapLF m⁻¹ G'', hw, hzt', ?_, ?_, ?_⟩
  · have e : Gval (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') = Gval G G'' := by
      have h' : Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').fl = Formalism.MainNotions.S.Zhat G.fl G''.fl :=
        hZiso.symm
      unfold Gval Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
      rw [h']
      rfl
    rw [e, GlobalTheory.T.flagPairValue_invariant_unitriangularChange D F G F' G'' A A' hA hA' hZG]
    exact hTP
  · rw [← hZiso, hZG]
    refine cell_chg _ _ _ w ?_ hA' hZw
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 j i hij]
    · subst hij
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 i]
  · intro s hs
    obtain ⟨s', hs', hsum⟩ := GlobalTheory.T.glueUnimodularLatticeReps_move_isometry_frames D _ _ (lf D (X.Fu u)) G (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') G'' m hmI hGm
      hG''m s hs
    have hcnt := GlobalTheory.T.weighted_count_glued_lattices_eq_mass_mul_local D (zOf Y) Fm.FP u u' F G F' G'' Fm.P Fm.d0 hk hBase hStd hTP Fm.R Fm.V0 hV0.le hML s' hs'
    choose! wp hwp0 hwpH hwpE using hlocw
    have hglue : glueSum G G'' s' = Fm.V0 * ∏ p ∈ Fm.P, (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal := by
      have hg0 : 0 ≤ glueSum G G'' s' := Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)
      have h := congrArg ENNReal.toReal hcnt
      rwa [ENNReal.toReal_ofReal hg0, ENNReal.toReal_mul, ENNReal.toReal_ofReal hV0.le, ENNReal.toReal_prod] at h
    have hng : ∀ p ∈ Fm.P, Fm.ngenL p = wp p * (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal := by
      intro p hp
      rw [(hloc p hp).1, hwpE p hp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwp0 p hp).le]
    have hle : Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) *
        glueSum (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') s := by
      rw [← hsum]
      refine le_of_le_of_eq ?_ (congrArg _ hglue.symm)
      show Fm.V0 * ∏ p : {p // p ∈ Fm.P}, Fm.ngenL p.1 ≤
        (∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp) ^ (3 * (D.R.rS + 1) ^ 2) * _
      rw [← Finset.prod_pow, Finset.prod_coe_sort Fm.P (fun p => Fm.ngenL p),
        Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2)), Finset.prod_congr rfl hng]
      calc Fm.V0 * ∏ p ∈ Fm.P, (wp p * (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal)
          ≤ Fm.V0 * ∏ p ∈ Fm.P, ((Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2) *
              (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal) := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)) hV0.le
            · exact mul_nonneg (hwp0 p hp).le ENNReal.toReal_nonneg
            · exact mul_le_mul_of_nonneg_right (hwpH p hp) ENNReal.toReal_nonneg
        _ = _ := by rw [Finset.prod_mul_distrib]; ring
    refine ⟨?_, hle⟩
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp only [glueSum, Finset.sum_empty, mul_zero] at hle
    linarith

end GlobalTheory.GenMassBound
