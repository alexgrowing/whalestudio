import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeComponentsScaledIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesUnitaryDiagonalTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)

noncomputable section

namespace GlobalTheory.InertHomIdx

def rmul {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin n) (Fin n) L) :
    Matrix (Fin m) (Fin n) L →+ Matrix (Fin m) (Fin n) L where
  toFun X := X * g
  map_zero' := Matrix.zero_mul g
  map_add' X Y := Matrix.add_mul X Y g

theorem rmul_apply {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin n) (Fin n) L) (X : Matrix (Fin m) (Fin n) L) :
    rmul g X = X * g := rfl

end GlobalTheory.InertHomIdx

open GlobalTheory.FinWeilO in

theorem GlobalTheory.InertHomIdx.heisenbergRelativeIndex_inert_move_source (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (hi : IsInertAt D.host.F D.host.E v w) (g : Gv S v) : GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v g, 1))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h g)⁻¹.1)) := by
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hε : IsPlaceIdem D v ε := hns.1
  have hη : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hk : GlobalTheory.WeilParts.SuppPl ε S (embV S v g) := by
    rw [GlobalTheory.PlaceDatum.placeIdem_eq hε hη]
    exact GlobalTheory.PlaceTensor.suppPl_emb S v g
  have hg : GlobalTheory.WeilParts.SuppPl ε T (1 : GA D T) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hk) (off_smul_mt_place hg)
  have hmat : (mt S (embV S v g⁻¹)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig S.gram h g)⁻¹.1 := by
    have e := finMat_map_compAt D.sp.cm.sig S.gram h (embV S v g⁻¹)
    rw [proj_emb_self] at e
    rw [← map_inv]
    exact e
  refine GlobalTheory.InertHomIdx.relIndex_map_of_proj (latF S T (frameLat S) (frameLat T)).toAddSubgroup
    (rhoF S T (embV S v g, 1)).toAddMonoidHom (mulF S T (algebraMap (AF D.host.F) (AE D) ε)).toAddMonoidHom
    (GlobalTheory.InertHomIdx.matW S T w) (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h g)⁻¹.1) ?_ ?_ ?_ ?_
  · intro x
    show (actO S T (embV S v g) 1 x).map (GlobalTheory.InertHomIdx.compW D w) = (x : WO S T).map (GlobalTheory.InertHomIdx.compW D w) * (locMat D.sp.cm.sig S.gram h g)⁻¹.1
    rw [actO, mt_one, Matrix.one_mul, ← map_inv, Matrix.map_mul, hmat]
  · intro x hx
    refine XF.ext (Matrix.ext fun i j => ?_)
    have h0 : GlobalTheory.InertHomIdx.compW D w ((x : WO S T) i j) = 0 := congrFun (congrFun hx i) j
    show algebraMap (AF D.host.F) (AE D) ε * (x : WO S T) i j = 0
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hp, zero_mul, RingHom.map_zero]
    · rw [RingHom.map_mul, finPart_of_isPrimeIdem hp, singleAt_mul, RingHom.map_zero]
      have h1 : compAt D.host.F w (finPart D ((x : WO S T) i j)) = 0 := h0
      rw [h1, mul_zero, ← singleAt_zero]
  · intro a ha
    exact GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε ha)
  · intro a _
    refine XF.ext ?_
    have := hoff (a : WO S T)
    rw [sub_smul, sub_smul, one_smul, one_smul] at this
    exact this

namespace GlobalTheory.InertHomLattice

theorem mem_map_latF_iff_frames (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hv : w.under (𝓞 D.host.F) = v) (hw : IsInertAt D.host.F D.host.E v w) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig hv c) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)) (ha : IsFrameAt w (frameLat T) a) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (haS : IsFrameAt w (frameLat S) aS) : ∃ (c₀ : w.adicCompletion D.host.E) (b : GL (Fin S.rank) (w.adicCompletion D.host.E)), c₀ ≠ 0 ∧ (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) ∧ ∀ X : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), X ∈ (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) ↔ c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) ∈ GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by

  obtain ⟨a₀, ha₀, h0, hgen⟩ := exists_gen (D := D) w
  set π := algebraMap D.host.E (w.adicCompletion D.host.E) with hπ
  set G : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E) := S.gram.map π with hG
  set B : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E) := Formalism.UG.cT c aS.1 * G with hB
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul, isUnit_iff_ne_zero]
    refine mul_ne_zero ?_ ?_
    · rw [Formalism.UG.cT, Matrix.det_transpose, show (aS.1.map c).det = c aS.1.det from (RingHom.map_det c aS.1).symm]
      exact (map_ne_zero c).2 (Matrix.det_ne_zero_of_left_inverse (B := (aS⁻¹).1) (by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]))
    · rw [hG, show (S.gram.map π).det = π S.gram.det from (RingHom.map_det π S.gram).symm]
      exact ((GlobalTheory.LatVac.gram_det_isUnit S).map π).ne_zero
  refine ⟨(π a₀)⁻¹, (Matrix.nonsingInvUnit B hBu)⁻¹, inv_ne_zero h0, by rw [inv_inv]; rfl, fun X => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [GlobalTheory.InertHomIdx.matW_apply]
    have hx' : (x : WO S T) ∈ latO S T (frameLat S) (frameLat T) fun _ => True := hx
    have hb : ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = B⁻¹ := rfl
    let Φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) := AddMonoidHom.mk'
      (fun u => (π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *
        u.map (GlobalTheory.InertHomIdx.compW D w) * ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1))
      fun u u' => by simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
    suffices hle : latO S T (frameLat S) (frameLat T) (fun _ => True) ≤
        (GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank).comap Φ from hle hx'
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a1, ha1, s, hs, t, ht, rfl⟩
    set lam := GlobalTheory.AdeleBaseChange.locMap D.host.F w (α (w.under (𝓞 D.host.F))) with hlam
    have hlamO : lam ∈ Formalism.UG.Ov D.host.E w := GlobalTheory.AdeleBaseChange.locMap_int w _ (hα _)
    have hmap : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a1 * t i * ∑ k, star (s k) * S.gram k j) : WO S T).map (GlobalTheory.InertHomIdx.compW D w) =
        (lam * π a1) • Matrix.vecMulVec (fun i => π (t i)) ((fun k => c (π (s k))) ᵥ* G) := by
      ext i j
      have e1 : GlobalTheory.InertHomIdx.compW D w (pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a1 * t i * ∑ k, star (s k) * S.gram k j)) =
          lam * π (a1 * t i * ∑ k, star (s k) * S.gram k j) := compAt_tmul w α _
      rw [Matrix.map_apply, Matrix.of_apply, e1, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      have hconj : ∀ y, c (π y) = π (star y) := fun y => InertChart.conj_algebraMap hc y
      simp only [map_mul, map_sum, Matrix.vecMul, dotProduct, hG, Matrix.map_apply, hconj]
      ring_nf
    have hy : ∀ p, ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p ∈ Formalism.UG.Ov D.host.E w := by
      refine (ha _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, ht, rfl⟩
    set z := (aS⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun k => π (s k) with hz
    have hzO : ∀ k, z k ∈ Formalism.UG.Ov D.host.E w := by
      refine (haS _).2 ?_
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨s, hs, rfl⟩
    have hsz : (fun k => π (s k)) = aS.1 *ᵥ z := by
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hcs : (fun k => c (π (s k))) = (fun k => c (z k)) ᵥ* Formalism.UG.cT c aS.1 := by
      funext k
      rw [Formalism.UG.cT, Matrix.vecMul_transpose, show c (π (s k)) = c ((fun k => π (s k)) k) from rfl, hsz]
      exact RingHom.map_mulVec c aS.1 z k
    have hr : ((fun k => c (π (s k))) ᵥ* G) ᵥ* ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 =
        fun k => c (z k) := by
      rw [hb, hcs, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← hB, Matrix.mul_nonsing_inv B hBu, Matrix.vecMul_one]
    intro p q
    show ((π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a1 * t i * ∑ k, star (s k) * S.gram k j) : WO S T).map (GlobalTheory.InertHomIdx.compW D w) *
        ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 :
        Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E))) p q ∈ _
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_vecMulVec_mul_apply, hr]
    have h1 := hgen a1 ha1
    have h2 := InertChart.conj_mem hw hc (hzO q)
    rw [intL_iff, show (π a₀)⁻¹ * (lam * π a1 * (((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p * c (z q))) =
      lam * ((π a₀)⁻¹ * π a1) * ((((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p) * c (z q)) by ring]
    exact mul_mem (mul_mem hlamO h1) (mul_mem (hy p) h2)
  · set Y := (π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X *
        ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1) with hY
    have hb : ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = B⁻¹ := rfl
    have hX : X = π a₀ • (a.1 * Y * B) := by
      rw [hY, hb, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ h0, one_smul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul B hBu, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have hsingle : ∀ {n : ℕ} (i : Fin n) (k : Fin n), (Pi.single i 1 : Fin n → w.adicCompletion D.host.E) k ∈ Formalism.UG.Ov D.host.E w := by
      intro n i k
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have htI : ∀ i, (fun k => singleAt D.host.F w (a.1 k i)) ∈ Formalism.L2.NTheta.LamHat T := fun i => by
      have := (ha (Pi.single i 1)).1 (hsingle i)
      rw [Matrix.mulVec_single_one] at this
      exact singleAt_mem_lamHat this
    have hsJ : ∀ j, (fun k => singleAt D.host.F w (aS.1 k j)) ∈ Formalism.L2.NTheta.LamHat S := fun j => by
      have := (haS (Pi.single j 1)).1 (hsingle j)
      rw [Matrix.mulVec_single_one] at this
      exact singleAt_mem_lamHat this
    have hu : (∑ i, ∑ j, GlobalTheory.LatticeStable.liftFin D (singleAt D.host.F w (Y i j)) •
        GlobalTheory.SplitHomLattice.rk S T a₀ (fun k => singleAt D.host.F w (aS.1 k j))
          (fun k => singleAt D.host.F w (a.1 k i)) : WO S T) ∈ latO S T (L0c D S) (L0c D T) fun _ => True :=
      sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _
        (by rw [GlobalTheory.SplitHomLattice.finPart_liftFin]; exact singleAt_mem_intAE (h i j)) _
        (GlobalTheory.SplitHomLattice.rk_mem S T ha₀ (hsJ j) (htI i))
    rw [hermitianSpaceBaseLattice_eq_frameLattice, hermitianSpaceBaseLattice_eq_frameLattice] at hu
    refine AddSubgroup.mem_map.2 ⟨GlobalTheory.FinWeilO.XF.mk _ (GlobalTheory.SplitScalar.latO_fin hu), hu, ?_⟩
    rw [GlobalTheory.InertHomIdx.matW_apply, GlobalTheory.FinWeilO.XF.coe_mk]
    exact (map_compW_sum S T hv hc a₀ Y a.1 aS.1).trans hX.symm

end GlobalTheory.InertHomLattice

namespace GlobalTheory.InertHomIdx

theorem relIndex_intMat_rmul_cT {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L)
    (hcc : ∀ x, c (c x) = x) (hcv : ∀ x, Valued.v (c x) = Valued.v x) (m n : ℕ) (k : Matrix (Fin n) (Fin n) L) :
    (intMat L m n).relIndex ((intMat L m n).map (rmul (Formalism.UG.cT c k))) =
      (intMat L n m).relIndex ((intMat L n m).map (lmul k)) := by
  let ψ : Matrix (Fin m) (Fin n) L →+ Matrix (Fin n) (Fin m) L :=
    { toFun := fun Y => Formalism.UG.cT c Y
      map_zero' := by ext i j; simp [Formalism.UG.cT]
      map_add' := fun X Y => by ext i j; simp [Formalism.UG.cT] }
  have hψ : Function.Injective ψ := by
    intro X Y hXY
    ext i j
    have := congrFun (congrFun hXY j) i
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    have := congrArg c this
    rwa [hcc, hcc] at this
  have hint : ∀ x : L, c x ∈ Formalism.UG.intL L ↔ x ∈ Formalism.UG.intL L := fun x => by
    show Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hcv]
  have h1 : ∀ {p r : ℕ}, (intMat L p r).map
      ({ toFun := fun Y => Formalism.UG.cT c Y
         map_zero' := by ext i j; simp [Formalism.UG.cT]
         map_add' := fun X Y => by ext i j; simp [Formalism.UG.cT] } : Matrix (Fin p) (Fin r) L →+ Matrix (Fin r) (Fin p) L) = intMat L r p := by
    intro p r
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩ i j
      exact (hint _).2 (hX j i)
    · intro hY
      refine ⟨Formalism.UG.cT c Y, fun i j => (hint _).2 (hY j i), ?_⟩
      ext i j
      simp [Formalism.UG.cT, hcc]
  have hcomm : ψ.comp (rmul (Formalism.UG.cT c k)) = (lmul k).comp ψ := by
    refine AddMonoidHom.ext fun X => ?_
    ext i j
    simp only [ψ, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, rmul_apply, lmul_apply,
      Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, hcc]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hψ, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map]
  exact congrArg₂ _ (h1) (congrArg _ h1)

end GlobalTheory.InertHomIdx

theorem GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∀ (d : Fin S.rank → ℤ) (t : GU c S.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c S.rank, ∀ k₂ ∈ KU c S.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm (k₁ * t * k₂)), 1))) = qV D.host.E w ^ (T.rank * (∑ i, max (d i) 0).toNat) := by
  intro D S T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨hc, ⟨a, ha, haJ, hea⟩, -⟩ := he
  have hlat := GlobalTheory.HeckeDual.isLattice_frameLat T
  obtain ⟨aT, haT⟩ := InertChart.exists_isFrameAt (L := frameLat T) hw hlat.fg hlat.span_eq_top
  obtain ⟨c₀, b, hc₀, hb, hX⟩ := GlobalTheory.InertHomLattice.mem_map_latF_iff_frames D S T v w h hw c hc aT haT a ha
  rw [GlobalTheory.InertHomIdx.heisenbergRelativeIndex_inert_move_source D S T v w h hw]
  set k : GU c S.rank := k₁ * t * k₂ with hk
  have hg : locMat D.sp.cm.sig S.gram h (e.symm k) = a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E)) * a⁻¹ := by
    have h1 := hea (e.symm k)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    group
  have hQ : ((b⁻¹ * a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * a⁻¹ * b : GL (Fin S.rank) (w.adicCompletion D.host.E))).1 =
      Formalism.UG.cT c k.1.1 := by
    set u : GL (Fin S.rank) (w.adicCompletion D.host.E) := b⁻¹ * a with hu
    have hu1 : u.1 = Formalism.UG.antiJ (w.adicCompletion D.host.E) S.rank := by
      rw [hu, Units.val_mul, hb, haJ]
    have hkU : Formalism.UG.cT c k.1.1 * Formalism.UG.antiJ (w.adicCompletion D.host.E) S.rank * k.1.1 = Formalism.UG.antiJ (w.adicCompletion D.host.E) S.rank := k.2
    have e1 : b⁻¹ * a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * a⁻¹ * b = u * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * u⁻¹ := by
      rw [hu]; group
    rw [e1]
    calc (u * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * u⁻¹).1
        = (Formalism.UG.cT c k.1.1 * u.1 * k.1.1) * (((k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * u⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E))).1 := by
          rw [hu1, hkU, ← hu1, ← Units.val_mul, mul_assoc]
      _ = Formalism.UG.cT c k.1.1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left, mul_inv_cancel,
            Units.val_one, Matrix.mul_one]
  set M := (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) with hM
  clear_value M
  let τ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    { toFun := fun X => c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1)
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul, smul_add] }
  have hτ : Function.Injective τ := by
    intro X Y hXY
    have h1 : c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) = c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * Y * b.1) := hXY
    have h2 := congrArg (fun Z => c₀⁻¹ • (aT.1 * Z * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) h1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc₀, one_smul] at h2
    simpa [← Matrix.mul_assoc, Matrix.mul_assoc _ _ (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1] using h2
  have h1 : M.map τ = GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
    ext Y
    constructor
    · rintro ⟨X, hX', rfl⟩
      exact (hX X).1 hX'
    · intro hY
      refine ⟨c₀⁻¹ • (aT.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1), (hX _).2 ?_, ?_⟩
      · show c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (c₀⁻¹ • (aT.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) * b.1) ∈ _
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
        exact hY
      · show c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (c₀⁻¹ • (aT.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) * b.1) = Y
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have h2 : (M.map (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹.1)).map τ =
      (GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank).map (GlobalTheory.InertHomIdx.rmul (Formalism.UG.cT c k.1.1)) := by
    have hcomm : τ.comp (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹.1) =
        (GlobalTheory.InertHomIdx.rmul (Formalism.UG.cT c k.1.1)).comp τ := by
      refine AddMonoidHom.ext fun X => ?_
      show c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (X * (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹.1) * b.1) = (c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1)) * Formalism.UG.cT c k.1.1
      rw [← hQ, Matrix.smul_mul]
      congr 1
      have e2 : (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹ * b =
          b * (b⁻¹ * a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * a⁻¹ * b) := by
        rw [hg]; group
      rw [Matrix.mul_assoc, Matrix.mul_assoc X, ← Units.val_mul, e2, Units.val_mul]
      simp only [Matrix.mul_assoc]
    rw [← h1, AddSubgroup.map_map, AddSubgroup.map_map, hcomm]
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hτ, h2, h1,
    GlobalTheory.InertHomIdx.relIndex_intMat_rmul_cT c hU.1 hU.2.1 T.rank S.rank k.1.1, hk,
    GlobalTheory.LatIdx.relIndex_intMat_translate ϖ c _ hU S.rank T.rank d t ht k₁ hk₁ k₂ hk₂]
  congr 1
  show (Ideal.absNorm v.asIdeal) ^ 2 = Ideal.absNorm w.asIdeal
  rw [GlobalTheory.LFun.InertChart.absNorm_eq (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw]

end
