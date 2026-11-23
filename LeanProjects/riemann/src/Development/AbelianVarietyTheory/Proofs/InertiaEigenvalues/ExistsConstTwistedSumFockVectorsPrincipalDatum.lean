import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LevTransl

variable {D : D7} {S T : HSp D}

open GlobalTheory.ExportSeries.DualType Matrix

def fE (u : Bridge.Gf S) : GL (Fin S.rank) (Lev.EAf D) :=
  Lev.finE S (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S)

theorem finPt_symm (u : Bridge.Gf S) :
    finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) = u :=
  (GlobalTheory.ClassRegroup.finEquiv S).apply_symm_apply u

theorem finE_eq (g : GA D S) : Lev.finE S g = Formalism.UG.bc (Lev.swapAE D) (finPt S g).1 := rfl

theorem fE_finPt {g : GA D S} : fE (finPt S g) = Lev.finE S g := by
  unfold fE
  rw [finE_eq, finE_eq g, finPt_symm]

theorem fE_mul (u v : Bridge.Gf S) : fE (u * v) = fE u * fE v := by
  unfold fE
  rw [map_mul, Subgroup.coe_mul, map_mul]

theorem fE_inv (u : Bridge.Gf S) : fE u⁻¹ = (fE u)⁻¹ := by
  unfold fE
  rw [map_inv, Subgroup.coe_inv, map_inv]

theorem mem_levJ_iff (B : Base S T) (ψ : Twist D Circle) (u : Bridge.Gf S) :
    u ∈ B.levJ ψ ↔ fE u ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ) := by
  have hk := ((GlobalTheory.ClassRegroup.finEquiv S).symm u).2
  have e := finPt_symm u
  constructor
  · intro h
    rw [← e] at h
    exact ((B.finPt_mem_levJ ψ hk).1 h).2
  · intro h
    rw [← e]
    exact (B.finPt_mem_levJ ψ hk).2 ⟨hk, h⟩

theorem mem_lev_princ (B : Base S T) (ψ : Twist D Circle) (x : GL (Fin S.rank) (Lev.EAf D)) :
    x ∈ lev D.sp.cm S.gram B.F.βS ((GlobalTheory.FlatVecSum.princ B).levS ψ) ↔
      x ∈ parLev D.sp.cm S.gram B.F.βS (B.levS ψ) ∧ rTup B.F.βS (B.levS ψ) x = 1 := by
  show x ∈ parLev D.sp.cm S.gram B.F.βS (B.levS ψ) ∧ rTup B.F.βS (B.levS ψ) x ∈ (⊥ : Subgroup (G0 B.G.Pg T.rank)) ↔ _
  exact and_congr_right fun _ => Subgroup.mem_bot

section Group

variable {B : Base S T} {ψ : Twist D Circle}

theorem parLev_of_levJ {u : Bridge.Gf S} (h : u ∈ B.levJ ψ) : fE u ∈ parLev D.sp.cm S.gram B.F.βS (B.levS ψ) :=
  lev_le_parLev ((mem_levJ_iff B ψ u).1 h)

theorem tup_eq_of_mem {u v : Bridge.Gf S} (hu : u ∈ B.levJ ψ) (hv : v ∈ B.levJ ψ)
    (h : u⁻¹ * v ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) :
    rTup B.F.βS (B.levS ψ) (fE u) = rTup B.F.βS (B.levS ψ) (fE v) := by
  have h1 := ((mem_lev_princ B ψ _).1 ((mem_levJ_iff _ ψ _).1 h)).2
  rw [fE_mul, fE_inv, rTup_mul (inv_mem (parLev_of_levJ hu)) (parLev_of_levJ hv), rTup_inv (parLev_of_levJ hu)] at h1
  exact inv_mul_eq_one.1 h1

theorem mem_princ_of_tup {u v : Bridge.Gf S} (hu : u ∈ B.levJ ψ) (hv : v ∈ B.levJ ψ)
    (h : rTup B.F.βS (B.levS ψ) (fE u) = rTup B.F.βS (B.levS ψ) (fE v)) : u⁻¹ * v ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  refine (mem_levJ_iff _ ψ _).2 ((mem_lev_princ B ψ _).2 ⟨?_, ?_⟩)
  · rw [fE_mul, fE_inv]
    exact mul_mem (inv_mem (parLev_of_levJ hu)) (parLev_of_levJ hv)
  · rw [fE_mul, fE_inv, rTup_mul (inv_mem (parLev_of_levJ hu)) (parLev_of_levJ hv), rTup_inv (parLev_of_levJ hu), h,
      inv_mul_cancel]

variable {F : Finset (Bridge.Gf S)} (hF : ∀ u ∈ F, u ∈ B.levJ ψ)
  (hU : ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ)
include hF hU

theorem tup_inj {u v : Bridge.Gf S} (hu : u ∈ F) (hv : v ∈ F)
    (h : rTup B.F.βS (B.levS ψ) (fE u) = rTup B.F.βS (B.levS ψ) (fE v)) : u = v := by
  obtain ⟨w, -, hw⟩ := hU v (hF v hv)
  have e1 := hw v ⟨hv, by rw [inv_mul_cancel]; exact one_mem _⟩
  have e2 := hw u ⟨hu, mem_princ_of_tup (hF u hu) (hF v hv) h⟩
  exact e2.trans e1.symm

theorem tup_surj (hB : B.Good) (hQ : B.admitted ψ.Q) {p : G0 B.G.Pg T.rank} (hp : p ∈ B.G.P.H) :
    ∃ u ∈ F, rTup B.F.βS (B.levS ψ) (fE u) = p := by
  obtain ⟨N, hN⟩ := GlobalTheory.TypeSupportLift.exists_isBaseFrame hB.frame.frS hB.frame.sdS
  obtain ⟨R, h1, h2, hR⟩ := hQ.1.split
  obtain ⟨-, κ, -, hall⟩ := GlobalTheory.ParahoricLift.exists_lift_prod S B.F.βS (B.levS ψ) B.F.ΛS N hN
    (fun PP hP PP' hP' => GlobalTheory.ExportType.not_isConjPl_of_splitSet hR (h1 hP) (by rcases hP' with h | h; exacts [h1 h, h2 h]))
    hQ.1.disj p
  obtain ⟨hκ, -⟩ := hall Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)
  have hkJ : finPt S (List.map κ Finset.univ.toList).prod ∈ B.levJ ψ :=
    (B.finPt_mem_levJ ψ hκ.1).2 ⟨hκ.1, hκ.2.1, by rw [hκ.2.2]; exact hp⟩
  obtain ⟨u, ⟨huF, hu⟩, -⟩ := hU _ hkJ
  refine ⟨u, huF, ?_⟩
  rw [tup_eq_of_mem (hF u huF) hkJ hu, fE_finPt, hκ.2.2]

end Group

section Datum

theorem low_top_left {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {K : GL (Fin n) κ} (hK : K ∈ blockTri (blk2 r))
    (u : Matrix (Fin n) (Fin r) κ) :
    LowZero r ((K⁻¹).val * u) ∧ topL r ((K⁻¹).val * u) = 1 ↔ LowZero r u ∧ (upperLeftBlock hr K).val = topL r u := by
  have eK : (K⁻¹).val * u = (K⁻¹).val * u * ((1 : GL (Fin r) κ)).val := by rw [Units.val_one, Matrix.mul_one]
  rw [eK, GlobalTheory.AdjDatumMove.lowZero_mul_iff (inv_mem hK)]
  refine and_congr_right fun hu => ?_
  rw [GlobalTheory.AdjDatumMove.topL_mul hr (inv_mem hK) _ hu, Units.val_one, Matrix.mul_one,
    show upperLeftBlock hr K⁻¹ = (upperLeftBlock hr K)⁻¹ from extendOne_inv _ hK, Units.inv_mul_eq_one]

open Classical in
theorem omegaK_left {n r : ℕ} (hr : r ≤ n) (Pg : Finset (Pl D.host.E)) (K : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP))
    (hK : ∀ PP ∈ Pg, K PP ∈ blockTri (blk2 r)) (y : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaK Pg (fun PP => ((K PP)⁻¹).val * y PP) =
      if (∀ PP ∈ Pg, LowZero r (y PP)) ∧ ∀ PP : ↥Pg, (upperLeftBlock hr (K PP.1)).val = topL r (y PP.1) then 1 else 0 := by
  unfold omegaK
  congr 1
  refine propext ⟨fun h => ⟨fun PP hP => ((low_top_left hr (hK PP hP) _).1 (h PP hP)).1,
    fun PP => ((low_top_left hr (hK PP.1 PP.2) _).1 (h PP.1 PP.2)).2⟩, fun h PP hP => ?_⟩
  exact (low_top_left hr (hK PP hP) _).2 ⟨h.1 PP hP, h.2 ⟨PP, hP⟩⟩

theorem flat_mul_right {k R : Type} [CommRing k] [CommRing R] {n r : ℕ} (hr : r ≤ n) (ν : kˣ →* Rˣ) {K : GL (Fin n) k}
    (hK : K ∈ blockTri (blk2 r)) (y : Matrix (Fin r) (Fin n) k) :
    flat ν (y * K.val) = (ν (GeneralLinearGroup.det (upperLeftBlock hr K)) : R) * flat ν y := by
  have e : K = (K⁻¹)⁻¹ := (inv_inv K).symm
  rw [e, flat_mul_inv hr ν (inv_mem hK), show upperLeftBlock hr K⁻¹ = (upperLeftBlock hr K)⁻¹ from extendOne_inv _ hK, map_inv, map_inv, inv_inv,
    ← e]

open Classical in
theorem locFn_right (B : Base S T) (ψ : Twist D Circle) (K : ∀ PP : Pl D.host.E, GL (Fin S.rank) (kP PP))
    (hK : ∀ PP ∈ B.de.Q ∪ ψ.Q, K PP ∈ blockTri (blk2 T.rank)) (y : Reds D T.rank S.rank) :
    B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) (fun PP => y PP * (K PP).val) =
      (((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (K PP)))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (K PP))) : ℂˣ) : ℂ) *
        B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y := by
  unfold Base.locFn
  rw [Finset.prod_congr rfl fun PP hP => flat_mul_right B.hr _ (hK PP (Finset.mem_union_left _ hP)) (y PP),
    Finset.prod_congr (s₁ := Finset.univ) rfl fun (PP : ↥ψ.Q) _ => flat_mul_right B.hr _ (hK PP.1 (Finset.mem_union_right _ PP.2)) (y PP.1),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_coe_sort ψ.Q]
  simp only [Units.val_mul, Units.coe_prod]
  ring

end Datum

theorem alg4 {G : Type} [CommGroup G] (a b c d : G) : a * b * (c⁻¹ * d⁻¹) * (c * d) = a * b := by
  rw [← mul_inv, inv_mul_cancel_right]

open Classical in
theorem term_eq (B : Base S T) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {g : GA D S}
    (hk : Lev.finE S g ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ)) (y : Reds D S.rank T.rank) (y' : Reds D T.rank S.rank) :
    ((levFn B.F.βS (B.levS ψ) (Lev.finE S g) * vacC B ψ g 1 : ℂˣ) : ℂ) *
      (omegaK B.G.Pg (fun PP => (redFn B.F.βS PP (Lev.finE S g⁻¹)).val * y PP * ((redFn B.F.βT PP (Lev.finE T 1))⁻¹).val) *
        B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1))
          (fun PP => (redFn B.F.βT PP (Lev.finE T 1)).val * y' PP * ((redFn B.F.βS PP (Lev.finE S g⁻¹))⁻¹).val)) =
    (if (∀ PP ∈ B.G.Pg, LowZero T.rank (y PP)) ∧
        ∀ PP : ↥B.G.Pg, (upperLeftBlock B.hr (redFn B.F.βS PP.1 (Lev.finE S g))).val = topL T.rank (y PP.1) then
      ((B.G.P.chi ⟨_, hk.2⟩ : ℂˣ) : ℂ) *
        ∏ PP : ↥B.G.Pg, ((B.G.muC PP.1 (GeneralLinearGroup.det (rTup B.F.βS (B.levS ψ) (Lev.finE S g) PP)) : ℂˣ) : ℂ)⁻¹
      else 0) * B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := by
  have hp := lev_le_parLev hk
  have ri : ∀ PP, redFn B.F.βS PP (Lev.finE S g⁻¹) = (redFn B.F.βS PP (Lev.finE S g))⁻¹ := fun PP => by
    rw [map_inv, redFn_inv (parLev_St hp)]
  simp only [finE_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul, ri, inv_inv]
  rw [omegaK_left B.hr B.G.Pg _ (fun PP hP => blockTri_blkOf_le _ _ (parLev_g hp hP)) y,
    locFn_right B ψ _ (fun PP hP => parLev_q hp hP) y']
  have hs := dualTypeVacuumScalar_div_levelScalar hQ hk
  have e1 : levFn B.F.βS (B.levS ψ) (Lev.finE S g) * vacC B ψ g 1 = srcC B ψ g hk := by
    rw [mul_inv_eq_iff_eq_mul] at hs
    rw [hs, mul_inv_cancel_left]
  rw [e1]
  split_ifs with h
  · have e2 : srcC B ψ g hk * ((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) =
        B.G.P.chi ⟨_, hk.2⟩ * ∏ PP ∈ B.G.Pg, (B.G.muC PP (blkA B g PP))⁻¹ := by
      unfold srcC
      rw [Finset.prod_inv_distrib (s := B.de.Q), Finset.prod_inv_distrib (s := ψ.Q)]
      exact alg4 _ _ _ _
    calc _ = ((srcC B ψ g hk * ((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) : ℂˣ) : ℂ) *
          B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := by
          simp only [Units.val_mul]; ring
      _ = _ := by
          rw [e2, Units.val_mul, Units.coe_prod, ← Finset.prod_coe_sort B.G.Pg]
          simp only [Units.val_inv_eq_inv_val]
          rfl
  · simp

open Classical in

theorem datum_sum (B : Base S T) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {ι : Type} [Fintype ι] (g : ι → GA D S)
    (hk : ∀ i, Lev.finE S (g i) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ))
    (inj : ∀ i j, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g j)) → i = j)
    (surj : ∀ p ∈ B.G.P.H, ∃ i, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = p) (x : WO S T) :
    B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) x =
      ∑ i, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g i)) * vacC B ψ (g i) 1 : ℂˣ) : ℂ) *
        B.F.datumFn (GlobalTheory.FlatVecSum.princG B.G) (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1))
          (actO S T (g i)⁻¹ 1 x) := by
  have st : ∀ i, Lev.finE S (g i)⁻¹ ∈ St B.F.βS := fun i => by
    rw [map_inv]; exact inv_mem (parLev_St (lev_le_parLev (hk i)))
  have hO := fun i => frMapO_act B.F (st i) (one_mem_St T B.F.βT) x
  have hJ := fun i => frMapAdj_act B.F (st i) (one_mem_St T B.F.βT) x
  have hH : ∀ i, IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) (actO S T (g i)⁻¹ 1 x) ↔ IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x :=
    fun i => ⟨GlobalTheory.ThetaMove.isHalf_of_act _ _, GlobalTheory.AdjDatumMove.isHalf_actO' _ _⟩
  unfold Frame.datumFn
  simp only [GlobalTheory.FlatVecSum.omegaG_princ, show (GlobalTheory.FlatVecSum.princG B.G).Pg = B.G.Pg from rfl, hH, fun i => (hO i).1,
    fun i => (hJ i).1]
  by_cases c1 : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x ∧ IsIntM (frMapAdj S T B.F.βS B.F.βT x)
  swap
  · simp only [if_neg c1, zero_mul, mul_zero, Finset.sum_const_zero]
  by_cases c2 : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x ∧ IsIntM (frMapO S T B.F.βS B.F.βT x)
  swap
  · simp only [if_neg c2, mul_zero, Finset.sum_const_zero]
  simp only [if_pos c1, if_pos c2]
  symm
  calc _ = ∑ i, (if (∀ PP ∈ B.G.Pg, LowZero T.rank (redM PP (frMapAdj S T B.F.βS B.F.βT x))) ∧
        ∀ PP : ↥B.G.Pg, (upperLeftBlock B.hr (redFn B.F.βS PP.1 (Lev.finE S (g i)))).val =
          topL T.rank (redM PP.1 (frMapAdj S T B.F.βS B.F.βT x)) then
        ((B.G.P.chi ⟨_, (hk i).2⟩ : ℂˣ) : ℂ) *
          ∏ PP : ↥B.G.Pg, ((B.G.muC PP.1 (GeneralLinearGroup.det (rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) PP)) : ℂˣ) : ℂ)⁻¹
        else 0) * B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) (fun PP => redM PP (frMapO S T B.F.βS B.F.βT x)) :=
        Finset.sum_congr rfl fun i _ => by
          rw [funext ((hO i).2 c2.2), funext ((hJ i).2 c1.2)]
          exact term_eq B hQ (hk i) _ _
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      by_cases hy : (∀ PP ∈ B.G.Pg, LowZero T.rank (redM PP (frMapAdj S T B.F.βS B.F.βT x))) ∧
          ∃ g0 : G0 B.G.Pg T.rank, (∀ PP : ↥B.G.Pg, (g0 PP).val = topL T.rank (redM PP.1 (frMapAdj S T B.F.βS B.F.βT x))) ∧
            g0 ∈ B.G.P.H
      · obtain ⟨h0, g0, hg0, hH0⟩ := hy
        obtain ⟨i, rfl⟩ := surj g0 hH0
        rw [omegaG_levT_of B.G h0 _ hg0 hH0, Finset.sum_eq_single i]
        · rw [if_pos ⟨h0, fun PP => hg0 PP⟩]
          rfl
        · intro j _ hj
          rw [if_neg]
          intro hc
          exact hj (inj j i (funext fun PP => Units.ext ((hc.2 PP).trans (hg0 PP).symm)))
        · exact fun h => absurd (Finset.mem_univ _) h
      · rw [omegaG_levT_zero B.G hy]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg]
        rintro ⟨h0, h1⟩
        exact hy ⟨h0, _, h1, (hk i).2⟩

open Classical in

theorem om_princ_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) {g : GA D S} (hg : g ∈ GfC S) (sg : Lev.finE S g ∈ St B.F.βS) :
    ω (g, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) = (((vacC B ψ g 1 : ℂˣ) : ℂ) * 1) •
      B.F.placeMap (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) (fun x => B.F.datumFn (GlobalTheory.FlatVecSum.princG B.G) (B.de.Q ∪ ψ.Q)
        (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) (actO S T g⁻¹ 1 x)) := by
  have hF := hB.frame
  have hsq := hQ.1.isOrthSum.1.idem
  have hinf := hQ.1.isOrthSum.1.infPart_eq
  have hM := Frame.isPlaceModel_placeMap (G := B.G) hF hQ.1
  have hΛ : ∀ a : GA D S, Lev.finE S a ∈ St B.F.βS → ∀ u, u ∈ B.F.lat ↔ actO S T a 1 u ∈ B.F.lat := fun a ha =>
    GlobalTheory.VecInv.mem_latO_iff hF.frS hF.frT ha (one_mem_St T _)
  have hω' : ∀ y y', (∀ PP ∈ B.de.Q ∪ ψ.Q, y PP = y' PP) →
      B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y = B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  have hsb := Frame.isSBHalf_datumFn (G := GlobalTheory.FlatVecSum.princG B.G) hF hQ.1 hω'
  have hθ := Frame.isThetaAt_vec (G := GlobalTheory.FlatVecSum.princG B.G) hF hQ.1 hω'
  have sg' : Lev.finE S g⁻¹ ∈ St B.F.βS := by rw [map_inv]; exact inv_mem sg
  have s := GlobalTheory.ThetaMove.isSBHalf_comp _ _ (hΛ g⁻¹ sg') hsb
  refine om_theta_move hω (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D _ hF.vac.1 S T _ _ hF.sdS hF.sdT _ hsq hinf _
    hF.vac.2.theta Tm hT Ψ hΨ) ⟨⟨_, hM⟩, fun _ h₂ => GlobalTheory.PlaceVec.placeModel_unique hF.vac.1 hF.sdS hF.sdT hsq hinf hM h₂ s⟩ hθ
    (hΛ _ sg) (Units.ne_zero _) (om_vac_base hB hS hψ hQ hω hg (one_mem _) sg (one_mem_St T _)) fun x => ?_
  have := GlobalTheory.SplitHecke.actO_inv_actO g (1 : GA D T) x
  rw [inv_one] at this
  rw [one_mul, this]

open Classical in

theorem vec_sum {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) {ι : Type} [Fintype ι] (g : ι → GA D S) (hg : ∀ i, g i ∈ GfC S)
    (hk : ∀ i, Lev.finE S (g i) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ))
    (inj : ∀ i j, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g j)) → i = j)
    (surj : ∀ p ∈ B.G.P.H, ∃ i, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = p) :
    ∑ i, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g i)) : ℂˣ) : ℂ) • ω (g i, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) =
      B.vecFlat ψ := by
  have e : B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) =
      ∑ i, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g i)) * vacC B ψ (g i) 1 : ℂˣ) : ℂ) • fun x =>
        B.F.datumFn (GlobalTheory.FlatVecSum.princG B.G) (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1))
          (actO S T (g i)⁻¹ 1 x) := by
    funext x
    rw [datum_sum B hQ g hk inj surj x, Finset.sum_apply]
    rfl
  conv_rhs => rw [Base.vecFlat, Base.vecAt, Frame.vec, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [om_princ_move hB hS hψ hQ hω (hg i) (parLev_St (lev_le_parLev (hk i))), smul_smul, map_smul, mul_one, Units.val_mul]

theorem levLam_eq (B : Base S T) (ψ : Twist D Circle) (u : Bridge.Gf S) (h : u ∈ B.levJ ψ) :
    ((B.levLam ψ ⟨u, h⟩ : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ) (fE u) : ℂˣ) : ℂ) := by
  have h' : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) ∈ B.levJ ψ := (finPt_symm u).symm ▸ h
  have e : (⟨u, h⟩ : B.levJ ψ) = ⟨_, h'⟩ := Subtype.ext (finPt_symm u).symm
  rw [e, B.levLam_finPt ψ h']
  rfl

theorem om_fock {B : Base S T} (hB : B.Good) {ν : (AE D)ˣ →* Circle} {ω : PairRep S T} (hω : B.IsWeil ν ω) {g : GA D S}
    (hg : g ∈ GfC S) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f) (P : Links.PolF D T.rank S.rank) :
    ω (g, 1) (B.F.fock f P) = B.F.fock (ω (g, 1) f) P :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf _ _ _ _ _ _ _ _ g 1
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hg])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hg])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)]) f hf P).2

theorem sum_om_fock_princ : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (F : Finset (Bridge.Gf S)) (hF : ∀ u ∈ F, u ∈ B.levJ ψ),
    (∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) →
    ∃ κ : ℂ, ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ F.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P := by
  intro D S T B hB hS ψ hψ hQ ω hω F hF hU
  refine ⟨1, fun P => ?_⟩
  have hB0 := GlobalTheory.FlatVecSum.princ_good hB
  have hQ0 : (GlobalTheory.FlatVecSum.princ B).admitted ψ.Q := hQ
  have hf0 : IsThetaFunO B.F.ψ S T ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB0.frame.vac.1 hB0.frame.vac.2.inf (Base.isThetaAt_vecAt hB0 hQ0 _) hB0.frame.vac.2.theta
  let g : {x // x ∈ F} → GA D S := fun u => (((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S)
  have hg : ∀ u, g u ∈ GfC S := fun u => ((GlobalTheory.ClassRegroup.finEquiv S).symm u.1).2
  have hk : ∀ u, Lev.finE S (g u) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ) := fun u => (mem_levJ_iff B ψ u.1).1 (hF u.1 u.2)
  have inj : ∀ u v, rTup B.F.βS (B.levS ψ) (Lev.finE S (g u)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g v)) → u = v :=
    fun u v h => Subtype.ext (tup_inj hF hU u.2 v.2 h)
  have surj : ∀ p ∈ B.G.P.H, ∃ u, rTup B.F.βS (B.levS ψ) (Lev.finE S (g u)) = p := fun p hp => by
    obtain ⟨u, hu, e⟩ := tup_surj hF hU hB hQ hp
    exact ⟨⟨u, hu⟩, e⟩
  have hv := vec_sum hB hS hψ hQ hω g hg hk inj surj
  have hth : ∀ u ∈ (Finset.univ : Finset {x // x ∈ F}), IsThetaFunO B.F.ψ S T (ω (g u, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)) :=
    fun u _ => hω.om_pres _ _ hf0
  rw [one_smul, ← Finset.univ_eq_attach]
  calc _ = ∑ u, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g u)) : ℂˣ) : ℂ) •
        B.F.fock (ω (g u, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)) P :=
        Finset.sum_congr rfl fun u _ => by
          rw [levLam_eq B ψ u.1 (hF u.1 u.2)]
          exact congrArg₂ (· • ·) rfl (om_fock hB hω (hg u) hf0 P)
    _ = B.F.fock (∑ u, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g u)) : ℂˣ) : ℂ) •
        ω (g u, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)) P :=
        (GlobalTheory.SpecFac.pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ _ _ _ hth P).symm
    _ = _ := by rw [hv]

end GlobalTheory.LevTransl
