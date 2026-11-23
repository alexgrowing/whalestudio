import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantWachModuleBasisOfNonnegJumpsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixCofactorEqQPowFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixFrameAtPrimitiveRootFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWachModuleMapMatrixReductionCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachModuleMapMatrixCompMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankReducedLetterMatrixEqRankModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContinuousCrystallineMatrixRepOfIntertwinesDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLocalSituationOfEmbeddingStatement

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

theorem eq_zero_of_lrank {F : Type} [Field F] {a b : ℕ} (A : Mx F⟦X⟧ a b) (h : lrank A = 0) : A = 0 := by
  have h0 : A.map (algebraMap F⟦X⟧ (LaurentSeries F)) = 0 := by
    unfold lrank Matrix.rank at h
    have hr := Submodule.finrank_eq_zero.mp h
    have hB := LinearMap.range_eq_bot.mp hr
    refine Matrix.ext fun i j => ?_
    have := congrFun (LinearMap.congr_fun hB (Pi.single j 1)) i
    simpa [Matrix.mulVecLin_apply] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [LaurentSeries.coe_algebraMap] at this
  exact HahnSeries.ofPowerSeries_injective (this.trans (map_zero _).symm)

section Functor

variable {D : D7} {HW : HWOf D.loc} (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) {l : ℕ} [Fact l.Prime]
  {K LL : FinExt l} (hA : CaseA K LL)

include F Cm in
theorem exists_frame {n : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ}
    (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r U) (hU : ∀ i, ∀ u ∈ U i, 0 ≤ u) (γ : ((HW l).W K 1 LL hA.2.2).Gam) :
    ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr.1))) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)),
      IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r hr.1) γ b N := by
  have hn : Module.finrank ↥(OL LL) ↥(latOf r hr.1).L.T = n := by
    rw [Module.finrank_eq_card_basis (basisOf r hr.1), Fintype.card_fin]
  exact GlobalTheory.T.exists_invariant_wachModule_basis_of_nonneg_jumps D HW F Cm l K LL hA (latOf r hr.1) U n hr.2 hU hn γ

include F Cm in
theorem latAt_of_frame {n h : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ}
    (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r fun i => Finset.univ.val.map (U i)) (hU : ∀ i a, 0 ≤ U i a ∧ U i a ≤ h)
    {γ : ((HW l).W K 1 LL hA.2.2).Gam} {b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr.1))} {N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)}
    (hb : IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r hr.1) γ b N) {u : ℤ_[l]ˣ} {c : ℤ_[l]} {ζ : ↥(OL LL)} {jj : ℕ → (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧}
    (hγ : (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (u : ℤ_[l])) (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hζ : IsPrimitiveRoot ζ l) (hjj : ∀ a ∈ Finset.Ioo 0 l, IsExpAt (OL LL).val.toRingHom (ζ ^ a) (jj a)) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    LatAt l (N.P i) (N.D i) (N.Th i) h u (U i) (OL LL).val.toRingHom jj := by
  refine ⟨?_, hb.2.2.2 i, ?_⟩
  · refine GlobalTheory.T.frobeniusMatrix_cofactor_eq_q_pow_frame D HW F Cm l K LL hA (latOf r hr.1) (fun i => Finset.univ.val.map (U i)) n h γ b N hr.2
      (fun i v hv => ?_) hb i
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hv
    exact hU i a
  · intro a ha
    obtain ⟨ha0, hal⟩ := Finset.mem_Ioo.mp ha
    have hprim : IsPrimitiveRoot (ζ ^ a) l :=
      hζ.pow_of_coprime a (Nat.coprime_comm.mp
        ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha0 hal)))
    exact GlobalTheory.T.frobeniusMatrix_frame_at_primitiveRoot_factor D HW F Cm l K LL hA (latOf r hr.1) n U γ b N (u : ℤ_[l]) c (ζ ^ a) (jj a) hr.2
      (fun i a => (hU i a).1) hb hγ hu hprim (hjj a ha) i

private theorem coe_basisOf_eq_stdMap_single {n : ℕ} (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (hr : Cont r) (k : Fin n) :
    ((basisOf r hr k : ↥(latOf r hr).L.T) : (latOf r hr).V) = stdMap LL n (Pi.single k 1) := by
  show stdMap LL n ((Pi.basisFun ↥(OL LL) (Fin n)) k) = _
  rw [Pi.basisFun_apply]

include F in
theorem exists_mapMat {n n' : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin n') ↥(OL LL)}
    {U U' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ} (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r U) (hr' : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r' U')
    {γ : ((HW l).W K 1 LL hA.2.2).Gam} {b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr.1))} {N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)}
    (hb : IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r hr.1) γ b N)
    {b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r' hr'.1))} {N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)}
    (hb' : IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r' hr'.1) γ b' N') {u : ℤ_[l]} {un : (↥(OL LL))⟦X⟧}
    (hγ : (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u) (hun : IsUn l ↥(OL LL) u un) {a : Mx ↥(OL LL) n' n} (ha : Tw r r' a) :
    ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n' n, IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr.1 hr'.1 a ha) b b' A ∧
      (∀ i, RedHom l (PowerSeries.map (residue ↥(OL LL)) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL))))
        ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL))))) ∧ ∀ i, lrank ((A i).map (PowerSeries.map (residue ↥(OL LL)))) = (a.map (residue ↥(OL LL))).rank := by
  obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.exists_wachModule_map_matrix_reduction_comm (HW l) K LL hA (latOf r hr.1) (latOf r' hr'.1) n n' γ b b' N N' u un
    (homOf hr.1 hr'.1 a ha) hr.2.1 hr'.2.1 hb hb' hγ hun
  refine ⟨A, hA1, hA2, fun i => ?_⟩
  refine GlobalTheory.T.rank_reduced_letter_matrix_eq_rank_mod_maximal D HW F l K LL hA (latOf r hr.1) (latOf r' hr'.1) n n' b b' (homOf hr.1 hr'.1 a ha) A
    (basisOf r hr.1) (basisOf r' hr'.1) a hr.2.1 hr'.2.1 hA1 (fun k => ?_) i
  simp only [coe_basisOf_eq_stdMap_single]
  show (a.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (stdMap LL n (Pi.single k 1)) =
    ∑ m, ((a m k : ↥(OL LL)) : ↥LL.1) • stdMap LL n' (Pi.single m 1)
  rw [stdMap_mulVec]
  funext j
  rw [stdMap_apply, Finset.sum_apply, Finset.sum_eq_single j
    (fun m _ hm => by simp [stdMap_apply, Pi.single_apply, Ne.symm hm]) (by simp)]
  simp [stdMap_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mapMat_mul {n n' n'' : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin n') ↥(OL LL)}
    {r'' : ↥(GK K) →* GL (Fin n'') ↥(OL LL)} {hr : Cont r} {hr' : Cont r'} {hr'' : Cont r''}
    {b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr))}
    {b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r' hr'))}
    {b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r'' hr''))}
    {a : Mx ↥(OL LL) n' n} {ha : Tw r r' a} {a' : Mx ↥(OL LL) n'' n'} {ha' : Tw r' r'' a'} {a'' : Mx ↥(OL LL) n'' n} {ha'' : Tw r r'' a''}
    {A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n' n} {A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n'' n'} {A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n'' n}
    (h : IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr hr' a ha) b b' A) (h' : IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr' hr'' a' ha') b' b'' A')
    (h'' : IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr hr'' a'' ha'') b b'' A'') (e : a'' = a' * a) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    (A'' i).map (PowerSeries.map (residue ↥(OL LL))) = (A' i).map (PowerSeries.map (residue ↥(OL LL))) * (A i).map (PowerSeries.map (residue ↥(OL LL))) := by
  have hc : ∀ v : Fin n → ↥LL.1, (homOf hr hr'' a'' ha'').f v = (homOf hr' hr'' a' ha').f ((homOf hr hr' a ha).f v) := by
    intro v
    show (a''.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec v =
      (a'.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec ((a.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec v)
    rw [e, Matrix.map_mul, Matrix.mulVec_mulVec]
  rw [GlobalTheory.T.wachModuleMapMatrix_comp_mul (HW l) K LL hA (latOf r hr) (latOf r' hr') (latOf r'' hr'') n n' n'' b b' b''
    (homOf hr hr' a ha) (homOf hr' hr'' a' ha') (homOf hr hr'' a'' ha'') A A' A'' h h' h'' hc i, Matrix.map_mul]

include F Cm in
set_option maxHeartbeats 1000000 in

theorem exists_positions {n t h R : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {ψ : Fin t → ↥(GK K) →* GL (Fin 1) ↥(OL LL)}
    {U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ} {wt : Fin t → ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ}
    (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r fun i => Finset.univ.val.map (U i)) (hU : ∀ i a, 0 ≤ U i a ∧ U i a ≤ h)
    (hψ : ∀ s, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (ψ s) fun i => {wt s i}) (hwt : ∀ s i, 0 ≤ wt s i ∧ wt s i ≤ h)
    {x : GalMats ↥(GK K) ↥(OL LL) n t R} {rs : Fin t → Fin R} {dim : Fin (R + 1) → ℕ}
    (hx : x.Chain (residue ↥(OL LL)) r ψ rs dim) {u : ℤ_[l]ˣ} {c : ℤ_[l]} {un : (↥(OL LL))⟦X⟧} {ζ : ↥(OL LL)}
    {jj : ℕ → (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧} (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c) (hun : IsUn l ↥(OL LL) (u : ℤ_[l]) un)
    (hζ : IsPrimitiveRoot ζ l) (hjj : ∀ a ∈ Finset.Ioo 0 l, IsExpAt (OL LL).val.toRingHom (ζ ^ a) (jj a)) :
    ∃ (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (Nψ : Fin t → Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) 1 ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Slot (ResidueField ↥(OL LL)) n t R), ∀ i,
      LatAt l (N.P i) (N.D i) (N.Th i) h u (U i) (OL LL).val.toRingHom jj ∧
      (∀ s, LatAt l ((Nψ s).P i) ((Nψ s).D i) ((Nψ s).Th i) h u (fun _ => wt s i) (OL LL).val.toRingHom jj) ∧
      (y i).Chain (y (i - 1)) l (PowerSeries.map (residue ↥(OL LL)) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) (fun s => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim := by
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA).2.2.2.1 u
  have hU0 : ∀ i, ∀ v ∈ Finset.univ.val.map (U i), 0 ≤ v := fun i v hv => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hv
    exact (hU i a).1
  have hone : ∀ w : ℤ, (Finset.univ.val.map fun _ : Fin 1 => w) = {w} := fun w => by simp
  have hψ' : ∀ s, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (ψ s)
      (fun i => Finset.univ.val.map fun _ : Fin 1 => wt s i) := fun s => by
    simpa only [hone] using hψ s
  have hψ0 : ∀ s i, ∀ v ∈ Finset.univ.val.map (fun _ : Fin 1 => wt s i), 0 ≤ v := fun s i v hv => by
    rw [hone, Multiset.mem_singleton] at hv
    rw [hv]
    exact (hwt s i).1
  have hrk : ∀ k, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (x.rk k) (fun i => Finset.univ.val.map (U i)) :=
    fun k => GlobalTheory.T.isContinuousCrystallineMatrixRep_of_intertwines_det_ne_zero (D.loc l) K LL _ n _ r (x.rk k) _ (x.a k) hr (hx.1 k).1 (hx.1 k).2.1
  have hr2 : ∀ s, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (x.r2 s)
      (fun i => Finset.univ.val.map (U i) + {wt s i}) :=
    fun s => GlobalTheory.T.matGood_of_block_extension_twist (D.loc l) (D.locA l) (D.locT l) K LL _ n _ r (ψ s) (x.r2 s) _ _ (x.B s) (x.C s) hr (hψ s)
      (hx.2.2 s).1 (hx.2.2 s).2.2.1 (hx.2.2 s).2.2.2.2.2.2.2.2.2.2
  have hr20 : ∀ s i, ∀ v ∈ Finset.univ.val.map (U i) + {wt s i}, 0 ≤ v := fun s i v hv => by
    rcases Multiset.mem_add.mp hv with hv | hv
    · exact hU0 i v hv
    · rw [Multiset.mem_singleton] at hv
      rw [hv]
      exact (hwt s i).1
  obtain ⟨b0, N0, hb0⟩ := exists_frame F Cm hA hr hU0 γ
  choose bk Nk hbk using fun k : Fin (R + 1) => exists_frame F Cm hA (hrk k) hU0 γ
  choose bψ Nψ hbψ using fun s : Fin t => exists_frame F Cm hA (hψ' s) (hψ0 s) γ
  choose b2 N2 hb2 using fun s : Fin t => exists_frame F Cm hA (hr2 s) (hr20 s) γ
  choose Aa hAa1 hAa2 hAa3 using fun k : Fin (R + 1) =>
    exists_mapMat F hA (hrk k) hr (hbk k) hb0 hγ hun (hx.1 k).1
  choose Ab hAb1 hAb2 hAb3 using fun k : Fin R =>
    exists_mapMat F hA (hrk k.castSucc) (hrk k.succ) (hbk k.castSucc) (hbk k.succ) hγ hun (hx.2.1 k).1
  choose AB hAB1 hAB2 hAB3 using fun s : Fin t =>
    exists_mapMat F hA (hr2 s) hr (hb2 s) hb0 hγ hun (hx.2.2 s).1
  choose AB' hAB'1 hAB'2 hAB'3 using fun s : Fin t =>
    exists_mapMat F hA (hr2 s) (hrk (rs s).succ) (hb2 s) (hbk (rs s).succ) hγ hun (hx.2.2 s).2.1
  choose AC hAC1 hAC2 hAC3 using fun s : Fin t =>
    exists_mapMat F hA (hr2 s) (hψ' s) (hb2 s) (hbψ s) hγ hun (hx.2.2 s).2.2.1
  choose AE hAE1 hAE2 hAE3 using fun s : Fin t =>
    exists_mapMat F hA (hrk (rs s).castSucc) (hr2 s) (hbk (rs s).castSucc) (hb2 s) hγ hun (hx.2.2 s).2.2.2.1
  choose AZ hAZ1 hAZ2 hAZ3 using fun s : Fin t =>
    exists_mapMat F hA (hrk (rs s).castSucc) (hψ' s) (hbk (rs s).castSucc) (hbψ s) hγ hun (a := 0)
      (fun g => by simp)
  refine ⟨N0, Nψ, fun i =>
    { Pk := fun k => ((Nk k).P i).map (PowerSeries.map (residue ↥(OL LL)))
      Dk := fun k => ((Nk k).D i).map (PowerSeries.map (residue ↥(OL LL)))
      A := fun k => (Aa k i).map (PowerSeries.map (residue ↥(OL LL)))
      Bb := fun k => (Ab k i).map (PowerSeries.map (residue ↥(OL LL)))
      P2 := fun s => ((N2 s).P i).map (PowerSeries.map (residue ↥(OL LL)))
      D2 := fun s => ((N2 s).D i).map (PowerSeries.map (residue ↥(OL LL)))
      B := fun s => (AB s i).map (PowerSeries.map (residue ↥(OL LL)))
      B' := fun s => (AB' s i).map (PowerSeries.map (residue ↥(OL LL)))
      C := fun s => (AC s i).map (PowerSeries.map (residue ↥(OL LL)))
      E := fun s => (AE s i).map (PowerSeries.map (residue ↥(OL LL))) }, fun i => ⟨?_, fun s => ?_, ?_⟩⟩
  · exact latAt_of_frame F Cm hA hr hU hb0 hγ hu hζ hjj i
  · exact latAt_of_frame F Cm hA (hψ' s) (fun i _ => hwt s i) (hbψ s) hγ hu hζ hjj i
  · refine ⟨fun k => ⟨hAa2 k i, (hAa3 k i).trans (hx.1 k).2.2⟩, fun k => ?_,
      fun s => ⟨hAB2 s i, hAC2 s i, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact mapMat_mul hA (hAb1 k) (hAa1 k.succ) (hAa1 k.castSucc) (hx.2.1 k).2 i
    · exact (mapMat_mul hA (hAE1 s) (hAB1 s) (hAa1 (rs s).castSucc) (hx.2.2 s).2.2.2.2.1.symm i).symm
    · have h0 := mapMat_mul hA (hAE1 s) (hAC1 s) (hAZ1 s) (hx.2.2 s).2.2.2.2.2.1.symm i
      have hz := eq_zero_of_lrank _ ((hAZ3 s i).trans (by simp))
      exact h0.symm.trans hz
    · exact mapMat_mul hA (hAB'1 s) (hAa1 (rs s).succ) (hAB1 s) (hx.2.2 s).2.2.2.2.2.2.1 i
    · exact (hAE3 s i).trans (hx.2.2 s).2.2.2.2.2.2.2.1
    · exact (hAC3 s i).trans (hx.2.2 s).2.2.2.2.2.2.2.2.1
    · exact (hAB'3 s i).trans (hx.2.2 s).2.2.2.2.2.2.2.2.2.1

end Functor

theorem glue_orbits {ι X : Type} (σ : Equiv.Perm ι) (Rel : ι → X → X → Prop)
    (h : ∀ i₀, ∃ (ι' : Type) (σ' : Equiv.Perm ι') (κ : ι' → ι) (x : ι' → X), Function.Injective κ ∧
      (∀ j, κ (σ' j) = σ (κ j)) ∧ i₀ ∈ Set.range κ ∧ ∀ j, Rel (κ j) (x j) (x (σ' j))) :
    ∃ x : ι → X, ∀ i, Rel i (x i) (x (σ i)) := by
  classical
  choose ι' σ' κ x hκ hcomm hmem hrel using h
  by_cases hne : Nonempty X
  · obtain ⟨x₀⟩ := hne
    obtain ⟨r, hr, hrσ⟩ : ∃ r : ι → ι, (∀ i, σ.SameCycle (r i) i) ∧ ∀ i, r (σ i) = r i :=
      ⟨fun i => (Quotient.mk'' i : Quotient (Equiv.Perm.SameCycle.setoid σ)).out,
        fun i => by exact Quotient.mk_out' (s₁ := Equiv.Perm.SameCycle.setoid σ) i,
        fun i => congrArg Quotient.out
          (Quotient.sound' (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl σ i)))⟩
    have hpow : ∀ k (m : ℤ) j, (σ ^ m) (κ k j) = κ k ((σ' k ^ m) j) := by
      intro k m
      induction m using Int.induction_on with
      | zero => intro j; simp
      | succ m ih =>
        intro j
        rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hcomm, ih]
      | pred m ih =>
        intro j
        rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ih]
        congr 1
        rw [Equiv.Perm.inv_eq_iff_eq, ← hcomm, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have hin : ∀ i, ∃ j, κ (r i) j = i := fun i => by
      obtain ⟨m, hm⟩ := hr i
      obtain ⟨j₀, hj₀⟩ := hmem (r i)
      exact ⟨(σ' (r i) ^ m) j₀, by rw [← hpow, hj₀, hm]⟩
    refine ⟨fun i => Function.extend (κ (r i)) (x (r i)) (fun _ => x₀) i, fun i => ?_⟩
    obtain ⟨j, hj⟩ := hin i
    have e1 := (hκ (r i)).extend_apply (x (r i)) (fun _ => x₀) j
    have e2 := (hκ (r i)).extend_apply (x (r i)) (fun _ => x₀) (σ' (r i) j)
    rw [hj] at e1
    rw [hcomm, hj] at e2
    have h3 := hrel (r i) j
    rw [hj] at h3
    show Rel i (Function.extend (κ (r i)) (x (r i)) (fun _ => x₀) i)
      (Function.extend (κ (r (σ i))) (x (r (σ i))) (fun _ => x₀) (σ i))
    rw [hrσ i, e1, e2]
    exact h3
  · have hι : IsEmpty ι := ⟨fun i => by obtain ⟨j, -⟩ := hmem i; exact hne ⟨x i j⟩⟩
    exact ⟨fun i => (hι.false i).elim, fun i => (hι.false i).elim⟩

end GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

set_option maxHeartbeats 1000000 in

theorem exists_positions_global (hBS : GlobalTheory.Published.BhattScholzeCrystallineLattices) {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hd : ¬ (l : ℤ) ∣ NumberField.discr E)
    {σ : Equiv.Perm (E →+* PadicAlgCl l)} (hσ : GlobalTheory.ExpFrame.IsFrobPerm σ) {n t h R : ℕ}
    {J : (E →+* PadicAlgCl l) → Fin n → ℤ} {wt : Fin t → (E →+* PadicAlgCl l) → ℤ}
    (hJ : ∀ i a, 0 ≤ J i a ∧ J i a ≤ h) (hwt : ∀ s i, 0 ≤ wt s i ∧ wt s i ≤ h) {LL : FinExt l}
    (hz : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) (hE : ∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1)
    {r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)} {ψ : Fin t → (Ω ≃ₐ[E] Ω) →* GL (Fin 1) ↥(OL LL)}
    (hr : GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) fun τ => Finset.univ.val.map (J τ))
    (hψ : ∀ s, GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (ψ s)) fun τ => {wt s τ})
    {x : GalMats (Ω ≃ₐ[E] Ω) ↥(OL LL) n t R} {rs : Fin t → Fin R} {dim : Fin (R + 1) → ℕ}
    (hx : x.Chain (residue ↥(OL LL)) r ψ rs dim) {u : ℤ_[l]ˣ} {c : ℤ_[l]} {un : (↥(OL LL))⟦X⟧} {ζ : ↥(OL LL)}
    {jj : ℕ → (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧} (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hun : IsUn l ↥(OL LL) (u : ℤ_[l]) un) (hζ : IsPrimitiveRoot ζ l)
    (hjj : ∀ a ∈ Finset.Ioo 0 l, IsExpAt (OL LL).val.toRingHom (ζ ^ a) (jj a)) :
    ∃ (N : Lat (E →+* PadicAlgCl l) n ↥(OL LL)) (Nψ : Fin t → Lat (E →+* PadicAlgCl l) 1 ↥(OL LL))
      (y : (E →+* PadicAlgCl l) → Slot (ResidueField ↥(OL LL)) n t R),
      LatN l N h u J (OL LL).val.toRingHom jj ∧
      (∀ s, LatN l (Nψ s) h u (fun i _ => wt s i) (OL LL).val.toRingHom jj) ∧
      ∀ i, (y i).Chain (y (σ i)) l (PowerSeries.map (residue ↥(OL LL)) un)
        ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim := by
  obtain ⟨D⟩ := GlobalTheory.MemLoc.record_nonempty
  obtain ⟨HW, F, ⟨Cm⟩, -⟩ := GlobalTheory.HWL.exists_hw_fon_cmp_ties hBS D.loc D.locA D.locT
  obtain ⟨xg, hxg⟩ := glue_orbits
    (X := (Mx (↥(OL LL))⟦X⟧ n n × Mx (↥(OL LL))⟦X⟧ n n × Mx ↥(OL LL) n n) ×
      (Fin t → Mx (↥(OL LL))⟦X⟧ 1 1 × Mx (↥(OL LL))⟦X⟧ 1 1 × Mx ↥(OL LL) 1 1) ×
      Slot (ResidueField ↥(OL LL)) n t R) σ
    (fun τ d d' =>
      LatAt l d.1.1 d.1.2.1 d.1.2.2 h u (J τ) (OL LL).val.toRingHom jj ∧
      (∀ s, LatAt l (d.2.1 s).1 (d.2.1 s).2.1 (d.2.1 s).2.2 h u (fun _ => wt s τ) (OL LL).val.toRingHom jj) ∧
      d.2.2.Chain d'.2.2 l (PowerSeries.map (residue ↥(OL LL)) un)
        (d.1.1.map (PowerSeries.map (residue ↥(OL LL)))) (d.1.2.1.map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => (d.2.1 s).1.map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => (d.2.1 s).2.1.map (PowerSeries.map (residue ↥(OL LL)))) rs dim)
    (fun i₀ => by
      obtain ⟨K, hA, ι, κ, hκ, hκσ, hi₀, hMG⟩ :=
        GlobalTheory.T.exists_unramifiedLocalSituation_of_embedding (D.loc l) (D.locA l) (D.locT l) (HW l) E Ω hl hd σ hσ LL hz hE i₀
      obtain ⟨N, Nψ, y, hy⟩ := exists_positions F Cm hA (U := fun i => J (κ i)) (wt := fun s i => wt s (κ i))
        (hMG n r _ hr) (fun i a => hJ (κ i) a) (fun s => hMG 1 (ψ s) _ (hψ s)) (fun s i => hwt s (κ i))
        (hx.res ι) hu hun hζ hjj
      exact ⟨ZMod (Module.finrank ℚ_[l] ↥(K0 K)), Equiv.subRight 1, κ,
        fun j => ((N.P j, N.D j, N.Th j), fun s => ((Nψ s).P j, (Nψ s).D j, (Nψ s).Th j), y j),
        hκ, fun j => hκσ j, hi₀, fun j => hy j⟩)
  exact ⟨⟨fun i => (xg i).1.1, fun i => (xg i).1.2.1, fun i => (xg i).1.2.2⟩,
    fun s => ⟨fun i => ((xg i).2.1 s).1, fun i => ((xg i).2.1 s).2.1, fun i => ((xg i).2.1 s).2.2⟩,
    fun i => (xg i).2.2, (latN_iff l _ h u J _ jj).2 fun i => (hxg i).1,
    fun s => (latN_iff l _ h u _ _ jj).2 fun i => (hxg i).2.1 s, fun i => (hxg i).2.2⟩

end GlobalTheory.WachPlace

end
