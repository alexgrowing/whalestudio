import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertHomLattice

variable {D : D7}

theorem intL_iff {w : HeightOneSpectrum (𝓞 D.host.E)} (x : w.adicCompletion D.host.E) :
    x ∈ Formalism.UG.intL (w.adicCompletion D.host.E) ↔ x ∈ Formalism.UG.Ov D.host.E w := Iff.rfl

theorem compAt_sigR {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : w.under (𝓞 D.host.F) = v) {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : IsConjAt D.sp.cm.sig hv c) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    compAt D.host.F w (sigR (Af D.host.F) D.sp.cm.sig y) = c (compAt D.host.F w y) := by
  rw [compAt_apply, compAt_apply, finAdEquiv_apply hv, finAdEquiv_apply hv, hc]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_gen (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ a₀ ∈ D.host.AA, algebraMap D.host.E (w.adicCompletion D.host.E) a₀ ≠ 0 ∧
      ∀ a ∈ D.host.AA, (algebraMap D.host.E (w.adicCompletion D.host.E) a₀)⁻¹ *
        algebraMap D.host.E (w.adicCompletion D.host.E) a ∈ Formalism.UG.Ov D.host.E w := by
  have hfg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (GlobalTheory.SplitHomLattice.ideal_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact GlobalTheory.SplitHomLattice.ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  let π := algebraMap D.host.E (w.adicCompletion D.host.E)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (π a)) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), Valued.v (π a) ≤ Valued.v (π a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [RingHom.map_add]; exact (Valuation.map_add_le _ hx hy)
    | smul o x _ hx =>
      have ho : Valued.v (π (o : D.host.E)) ≤ 1 := by
        rw [Formalism.UG.P.levelaf_valued_algebraMap, show w.valuation D.host.E (o : D.host.E) = w.intValuation o from
          w.valuation_of_algebraMap o]
        exact w.intValuation_le_one o
      rw [show o • x = (o : D.host.E) * x from rfl, RingHom.map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' ho).trans hx
  have h0 : π a₀ ≠ 0 := by
    intro h
    apply GlobalTheory.SplitHomLattice.ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero π).1 this
  refine ⟨a₀, ?_, h0, fun a ha => ?_⟩
  · show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  · show Valued.v ((π a₀)⁻¹ * π a) ≤ 1
    rw [Valuation.map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
    exact hle a ha

theorem mul_vecMulVec_mul_apply {K : Type} [CommRing K] {m n : ℕ} (A : Matrix (Fin m) (Fin m) K)
    (B : Matrix (Fin n) (Fin n) K) (t : Fin m → K) (r : Fin n → K) (p : Fin m) (q : Fin n) :
    (A * Matrix.vecMulVec t r * B) p q = (A *ᵥ t) p * (r ᵥ* B) q := by
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem compW_liftFin (w : HeightOneSpectrum (𝓞 D.host.E)) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.InertHomIdx.compW D w (GlobalTheory.LatticeStable.liftFin D z) = compAt D.host.F w z := by
  rw [GlobalTheory.InertHomIdx.compW, RingHom.comp_apply, GlobalTheory.SplitHomLattice.finPart_liftFin]

theorem compAt_one_tmul (w : HeightOneSpectrum (𝓞 D.host.E)) (y : D.host.E) :
    compAt D.host.F w ((1 : Af D.host.F) ⊗ₜ[D.host.F] y) = algebraMap D.host.E (w.adicCompletion D.host.E) y := by
  rw [compAt_tmul]
  simp

end GlobalTheory.InertHomLattice

namespace GlobalTheory.InertHomLattice

variable {D : D7}

theorem map_compW_sum (S T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : w.under (𝓞 D.host.F) = v) {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : IsConjAt D.sp.cm.sig hv c) (a₀ : D.host.E)
    (Y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E))
    (A : Matrix (Fin T.rank) (Fin T.rank) (w.adicCompletion D.host.E))
    (A' : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    Matrix.map (∑ i, ∑ j, GlobalTheory.LatticeStable.liftFin D (singleAt D.host.F w (Y i j)) •
      GlobalTheory.SplitHomLattice.rk S T a₀ (fun k => singleAt D.host.F w (A' k j)) (fun k => singleAt D.host.F w (A k i)) : WO S T)
      (GlobalTheory.InertHomIdx.compW D w) =
    algebraMap D.host.E (w.adicCompletion D.host.E) a₀ •
      (A * Y * (Formalism.UG.cT c A' * S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)))) := by
  refine Matrix.ext fun p q => ?_
  rw [Matrix.map_apply, Matrix.sum_apply, map_sum]
  simp only [Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul, map_mul, compW_liftFin, compAt_singleAt,
    GlobalTheory.SplitHomLattice.rk, Matrix.of_apply, compAt_sigR hv hc, compAt_one_tmul]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end GlobalTheory.InertHomLattice

namespace GlobalTheory.InertHomLattice

theorem mem_map_latF_iff : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → ∀ a : GL (Fin T.rank) (w.adicCompletion D.host.E), IsFrameAt w (frameLat T) a → ∃ (c₀ : w.adicCompletion D.host.E) (b : GL (Fin S.rank) (w.adicCompletion D.host.E)), c₀ ≠ 0 ∧ ∀ X : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), X ∈ (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) ↔ c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) ∈ GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
  intro D S T v w hv hw a ha
  obtain ⟨c, hc, -⟩ := InertChart.existsUnique_isConjAt D.sp.cm.sig hw hv
  have hlat := GlobalTheory.HeckeDual.isLattice_frameLat S
  obtain ⟨aS, haS⟩ := InertChart.exists_isFrameAt (L := frameLat S) hw hlat.fg hlat.span_eq_top
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
  refine ⟨(π a₀)⁻¹, (Matrix.nonsingInvUnit B hBu)⁻¹, inv_ne_zero h0, fun X => ⟨fun h => ?_, fun h => ?_⟩⟩
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
