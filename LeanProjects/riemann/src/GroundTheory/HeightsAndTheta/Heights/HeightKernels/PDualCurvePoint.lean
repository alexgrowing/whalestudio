import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace DualCurvePointAlt

section General

variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]

set_option linter.unusedSectionVars false

theorem eval_one_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = eval₂ (Int.castRingHom Ω) y f := by
  have h : (MvPolynomial.eval (fun _ : B => (1 : Ω))).comp (mConeMap y : MRing ι →+* MvPolynomial B Ω) =
      eval₂Hom (Int.castRingHom Ω) y :=
    MvPolynomial.ringHom_ext (fun a => by simp [mConeMap]) (fun p => by simp [mConeMap])
  exact RingHom.congr_fun h f

theorem mConeMap_eq_eval₂ {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    mConeMap y f = eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1) f := by
  have h : (mConeMap y : MRing ι →+* MvPolynomial B Ω) =
      eval₂Hom (Int.castRingHom (MvPolynomial B Ω)) (fun p => C (y p) * X p.1) :=
    MvPolynomial.ringHom_ext (fun a => by simp [mConeMap]) (fun p => by simp [mConeMap])
  exact RingHom.congr_fun h f

theorem aeval_eq_zero_of_mem {Ω : Type} [Field Ω] {z : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal z) : eval₂ (Int.castRingHom Ω) z f = 0 := by
  rw [← eval_one_mConeMap, RingHom.mem_ker.1 hf, map_zero]

theorem aeval_genPt (W : Ideal (MRing ι)) (f : MRing ι) :
    eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) f =
      algebraMap (MRing ι ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W) (Ideal.Quotient.mk W f) := by
  have h : eval₂Hom (Int.castRingHom (IndefiniteRowSideFullHecke.Inter.FnField W)) (IndefiniteRowSideFullHecke.Inter.genPt W) =
      (algebraMap (MRing ι ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W)).comp (Ideal.Quotient.mk W) :=
    MvPolynomial.ringHom_ext (fun a => by simp) (fun p => by simp [IndefiniteRowSideFullHecke.Inter.genPt])
  exact RingHom.congr_fun h f

theorem mCoordIdeal_genPt (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W) = W := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [← IndefiniteRowSideFullHecke.Inter.ker_algebraMap_comp_mk W, RingHom.mem_ker, RingHom.comp_apply, ← aeval_genPt]
    exact aeval_eq_zero_of_mem hf
  · obtain ⟨S, hS, hSW⟩ := hW
    calc W = Ideal.span S := hSW
      _ ≤ _ := Ideal.span_le.2 fun s hs => by
        obtain ⟨a, ha⟩ := hS s hs
        have hsW : s ∈ W := hSW ▸ Ideal.subset_span hs
        have h0 : eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) s = 0 := by
          rw [aeval_genPt, Ideal.Quotient.eq_zero_iff_mem.2 hsW, map_zero]
        show s ∈ RingHom.ker _
        rw [RingHom.mem_ker, mConeMap_eq_eval₂]
        have h3 := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha
          (fun k => (X k : MvPolynomial B (IndefiniteRowSideFullHecke.Inter.FnField W))) (fun p => C (IndefiniteRowSideFullHecke.Inter.genPt W p))
        have e2 : eval₂ (Int.castRingHom (MvPolynomial B (IndefiniteRowSideFullHecke.Inter.FnField W)))
            (fun p => C (IndefiniteRowSideFullHecke.Inter.genPt W p)) s =
              C (eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) s) := by
          rw [eval₂_comp_left]
          congr 1
        have h4 : eval₂ (Int.castRingHom (MvPolynomial B (IndefiniteRowSideFullHecke.Inter.FnField W)))
            (fun p => C (IndefiniteRowSideFullHecke.Inter.genPt W p) * X p.1) s = 0 := by
          rw [show (fun p : Σ k, ι k => C (IndefiniteRowSideFullHecke.Inter.genPt W p) * X p.1) =
            fun p => X p.1 * C (IndefiniteRowSideFullHecke.Inter.genPt W p) from funext fun _ => mul_comm _ _, h3, e2, h0, C_0,
            mul_zero]
        exact h4

theorem ker_coneMapQ_eq {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) :
    RingHom.ker (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.coneMapQ y) = ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) := by
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hint : ∀ m : ℤ, (C m : MRing ι) ∈ mCoordIdeal y → m = 0 := fun m hm => by
    have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from CoordinateConeArithVar.horizontal y,
      Ideal.mem_bot] at h
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hint
  have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤ RingHom.ker (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.coneMapQ y) :=
    Ideal.map_le_iff_le_comap.mpr (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.comap_ker_coneMapQ y).ge
  refine (eq_of_le_of_not_lt hle fun hlt => ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.comap_ker_coneMapQ] at h
  exact lt_irrefl _ h

open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in

theorem aeval_ratio_eq_zero_of_le {Ω L : Type} [Field Ω] [CharZero Ω] [Field L] [CharZero L]
    {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hyz : mCoordIdeal y ≤ mCoordIdeal z) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) (hzd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : aeval (fun p => y p / y ⟨p.1, d p.1⟩) g = 0) :
    aeval (fun p => z p / z ⟨p.1, d p.1⟩) g = 0 := by
  have hN : ∀ m ∈ g.support, ∀ k, blockDeg m k ≤ g.totalDegree := fun m hm k =>
    blockDeg_le_totalDegree hm k
  have hG : homog d g.totalDegree g ∈ RingHom.ker (coneMapQ y) := by
    rw [RingHom.mem_ker]
    let j := algebraMap (MvPolynomial B Ω) (FractionRing (MvPolynomial B Ω))
    have hj : Function.Injective j := IsFractionRing.injective _ _
    apply hj
    have hw : ∀ k, (j ∘ fun p : Σ k, ι k => C (y p) * X p.1) ⟨k, d k⟩ ≠ 0 := fun k =>
      (map_ne_zero_iff j hj).mpr (mul_ne_zero (C_ne_zero.mpr (hyd k)) (X_ne_zero _))
    rw [map_zero, coneMapQ, aeval_def, eval₂_comp_left, eval₂_homog _ d _ g hN _ hw]
    apply mul_eq_zero_of_right
    have e : (fun p : Σ k, ι k => (j ∘ fun p : Σ k, ι k => C (y p) * X p.1) p /
        (j ∘ fun p : Σ k, ι k => C (y p) * X p.1) ⟨p.1, d p.1⟩) =
        (j.comp C) ∘ fun p => y p / y ⟨p.1, d p.1⟩ := by
      funext p
      have hX : j (X p.1) ≠ 0 := (map_ne_zero_iff j hj).mpr (X_ne_zero _)
      simp only [Function.comp_apply, map_mul, RingHom.coe_comp]
      rw [mul_div_mul_right _ _ hX, ← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
        map_div₀]
    rw [e, show j.comp (algebraMap ℚ (MvPolynomial B Ω)) = (j.comp C).comp (algebraMap ℚ Ω) from
      RingHom.ext_rat _ _, ← eval₂_comp_left, ← aeval_def, hg0, map_zero]
  have hGz : aeval z (homog d g.totalDegree g) = 0 := by
    rw [ker_coneMapQ_eq y] at hG
    have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤
        RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] L) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
        algebraMap_int_eq]
      exact aeval_eq_zero_of_mem (hyz hf)
    exact hle hG
  rw [aeval_def, eval₂_homog _ d _ g hN _ hzd] at hGz
  rw [aeval_def]
  exact (mul_eq_zero.mp hGz).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzd k))

theorem eval₂_ratio_eq_zero_of_le {Ω L : Type} [Field Ω] [CharZero Ω] [Field L] [CharZero L]
    {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hyz : mCoordIdeal y ≤ mCoordIdeal z) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) (hzd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : eval₂ (Rat.castHom Ω) (fun p => y p / y ⟨p.1, d p.1⟩) g = 0) :
    eval₂ (Rat.castHom L) (fun p => z p / z ⟨p.1, d p.1⟩) g = 0 := by
  have := aeval_ratio_eq_zero_of_le hyz d hyd hzd (g := g) (by rw [aeval_def]; exact hg0)
  rwa [aeval_def] at this

end General

section Dual

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]

set_option linter.unusedSectionVars false

abbrev constK (K : Type) [Field K] (i : ℕ) : K →+* ProjField K i :=
  (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)).comp C

def linVal (w : Fin i → K) : ProjField K i :=
  algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (∑ j, C (w j) * X j)

theorem linVal_eq (w : Fin i → K) :
    linVal w = ∑ j, constK K i (w j) * algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) := by
  simp [linVal, map_sum, map_mul]

theorem linVal_smul (a : K) (w : Fin i → K) : linVal (a • w) = constK K i a * linVal w := by
  rw [linVal_eq, linVal_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem linVal_single (j : Fin i) :
    linVal (Pi.single j (1 : K)) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) := by
  rw [linVal_eq, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem dualLatticeCoord_eq (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    dualLatticeCoord b ⟨(), t⟩ = linVal (b t : Fin i → K) := rfl

theorem exists_combo (b : Module.Basis T ℤ (dualLattice F)) (w : Fin i → K) :
    ∃ (D : ℤ) (c : T → ℤ), D ≠ 0 ∧
      (D : ProjField K i) * linVal w = ∑ t, (c t : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ := by
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg w
  have hmem' : D • w ∈ dualLattice F := hmem
  refine ⟨D, b.repr ⟨D • w, hmem'⟩, hD, ?_⟩
  have h : D • w = ∑ t, (b.repr ⟨D • w, hmem'⟩ t) • (b t : Fin i → K) := by
    have := congrArg Subtype.val (b.sum_repr ⟨D • w, hmem'⟩)
    rw [Submodule.coe_sum] at this
    simpa using this.symm
  have hj : ∀ j, (D : K) * w j = ∑ t, (b.repr ⟨D • w, hmem'⟩ t : K) * (b t : Fin i → K) j := fun j => by
    have := congrFun h j
    simpa [Finset.sum_apply, zsmul_eq_mul] using this
  simp only [linVal_eq, dualLatticeCoord_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := congrArg (constK K i) (hj j)
  simp only [map_mul, map_intCast, map_sum] at h2
  rw [← mul_assoc, h2, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => mul_assoc _ _ _

theorem exists_eval_eq (b : Module.Basis T ℤ (dualLattice F)) (t0 : T) (w : Fin i → K) :
    ∃ g : MvPolynomial (Σ _ : Unit, T) ℚ,
      eval₂ (Rat.castHom _) (fun p => dualLatticeCoord b p / dualLatticeCoord b ⟨(), t0⟩) g =
        linVal w / dualLatticeCoord b ⟨(), t0⟩ := by
  obtain ⟨D, c, hD, h⟩ := exists_combo b w
  refine ⟨∑ t, C ((c t : ℚ) / D) * X ⟨(), t⟩, ?_⟩
  have hD' : (D : ProjField K i) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hl : linVal w = ∑ t, ((c t : ProjField K i) / D) * dualLatticeCoord b ⟨(), t⟩ := by
    rw [← mul_div_cancel_left₀ (linVal w) hD', h, Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hl, Finset.sum_div, eval₂_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eval₂_mul, eval₂_C, eval₂_X, map_div₀, map_intCast, map_intCast]
  ring

theorem exists_point (b : Module.Basis T ℤ (dualLattice F)) {L : Type} [Field L] [CharZero L]
    (z : (Σ _ : Unit, T) → L) (t0 : T) (hz : z ⟨(), t0⟩ = 1) (hle : dualIdeal b ≤ mCoordIdeal z) :
    ∃ (_ : Algebra K L) (v : Fin i → L), v ≠ 0 ∧ dualPointCoord b v = z := by
  have hu : dualLatticeCoord b ⟨(), t0⟩ ≠ 0 := fun h0 => by
    have hX : (X ⟨(), t0⟩ : MRing (dualBlocks T)) ∈ mCoordIdeal z :=
      hle (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)
    have := aeval_eq_zero_of_mem hX
    rw [eval₂_X, hz] at this
    exact one_ne_zero this
  let ev : MvPolynomial (Σ _ : Unit, T) ℚ →+* ProjField K i :=
    eval₂Hom (Rat.castHom _) fun p => dualLatticeCoord b p / dualLatticeCoord b ⟨(), t0⟩
  let ev2 : MvPolynomial (Σ _ : Unit, T) ℚ →+* L := eval₂Hom (Rat.castHom L) z
  have hker : ∀ g ∈ RingHom.ker ev, ev2 g = 0 := fun g hg => by
    have h := eval₂_ratio_eq_zero_of_le hle (fun _ => t0) (fun _ => hu)
      (fun _ => by rw [hz]; exact one_ne_zero) (RingHom.mem_ker.1 hg)
    have e : (fun p : Σ _ : Unit, T => z p / z ⟨p.1, (fun _ : Unit => t0) p.1⟩) = z := by
      funext ⟨⟨⟩, t⟩
      show z ⟨(), t⟩ / z ⟨(), t0⟩ = z ⟨(), t⟩
      rw [hz, div_one]
    show eval₂ (Rat.castHom L) z g = 0
    rw [← e]
    exact h
  let ψ : ev.range →+* L :=
    (Ideal.Quotient.lift (RingHom.ker ev) ev2 hker).comp ev.quotientKerEquivRange.symm.toRingHom
  have hψ : ∀ g, ψ ⟨ev g, g, rfl⟩ = ev2 g := fun g => by
    show Ideal.Quotient.lift _ ev2 hker (ev.quotientKerEquivRange.symm ⟨ev g, g, rfl⟩) = ev2 g
    rw [show ev.quotientKerEquivRange.symm ⟨ev g, g, rfl⟩ = Ideal.Quotient.mk _ g from
      (RingEquiv.symm_apply_eq _).2 rfl]
    rfl
  have hmem : ∀ w, linVal w / dualLatticeCoord b ⟨(), t0⟩ ∈ ev.range := fun w => by
    obtain ⟨g, hg⟩ := exists_eval_eq b t0 w
    exact ⟨g, hg⟩
  have hκ : ∀ a, constK K i a ∈ ev.range := fun a => by
    have h := hmem (a • (b t0 : Fin i → K))
    rwa [linVal_smul, ← dualLatticeCoord_eq, mul_div_assoc, div_self hu, mul_one] at h
  let lam : K →+* L := ψ.comp ((constK K i).codRestrict ev.range hκ)
  let _ : Algebra K L := lam.toAlgebra
  let v : Fin i → L := fun j => ψ ⟨linVal (Pi.single j 1) / dualLatticeCoord b ⟨(), t0⟩, hmem _⟩
  have hv : dualPointCoord b v = z := by
    funext p
    obtain ⟨⟨⟩, t⟩ := p
    have e : (∑ j, (constK K i).codRestrict ev.range hκ ((b t : Fin i → K) j) *
        (⟨linVal (Pi.single j 1) / dualLatticeCoord b ⟨(), t0⟩, hmem _⟩ : ev.range)) =
          ⟨ev (X ⟨(), t⟩), X ⟨(), t⟩, rfl⟩ := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, RingHom.codRestrict_apply]
      rw [show ev (X ⟨(), t⟩) = dualLatticeCoord b ⟨(), t⟩ / dualLatticeCoord b ⟨(), t0⟩ from eval₂_X _ _ _,
        dualLatticeCoord_eq b t, linVal_eq (b t : Fin i → K), Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [linVal_single, mul_div_assoc]
    have h2 := congrArg ψ e
    rw [map_sum, hψ] at h2
    simp only [map_mul] at h2
    rw [show ev2 (X ⟨(), t⟩) = z ⟨(), t⟩ from eval₂_X _ _ _] at h2
    rw [← h2]
    rfl
  refine ⟨lam.toAlgebra, v, fun h0 => ?_, hv⟩
  have := congrFun hv ⟨(), t0⟩
  rw [h0, hz] at this
  simp [dualPointCoord] at this

end Dual

theorem exists_numberField_coords {T : Type} [Fintype T] (W : Ideal (MRing (fun _ : Unit => T)))
    (hW : IsArithVar W 1) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (z : (Σ _ : Unit, T) → L) (t0 : T),
      z ⟨(), t0⟩ = 1 ∧ mCoordIdeal z = W := by
  have : W.IsPrime := hW.2.1.1
  have hinj : Function.Injective (algebraMap ℤ (IndefiniteRowSideFullHecke.Inter.FnField W)) := by
    have e : algebraMap ℤ (IndefiniteRowSideFullHecke.Inter.FnField W) =
        (algebraMap (MRing (fun _ : Unit => T) ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W)).comp
          (algebraMap ℤ (MRing (fun _ : Unit => T) ⧸ W)) := RingHom.ext_int _ _
    rw [e, RingHom.coe_comp]
    exact (IsFractionRing.injective _ _).comp (CoordinateConeArithVar.algebraMap_injective W hW.2.2.1)
  have : CharZero (IndefiniteRowSideFullHecke.Inter.FnField W) := charZero_of_injective_algebraMap hinj
  have hy : mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W) = W := mCoordIdeal_genPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W)) 1 := by rw [hy]; exact hW
  obtain ⟨t0, ht0⟩ := hW.2.1.2.2 ()
  have hc : ∀ k, IndefiniteRowSideFullHecke.Inter.genPt W ⟨k, (fun _ : Unit => t0) k⟩ ≠ 0 := fun k h =>
    ht0 (by rw [← hy]; exact IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h)
  have : Finite (coneRatios (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ : Unit => t0) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (CoordinateConeArithVar.ratioField (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0) :=
    IntermediateField.finiteDimensional_adjoin fun x ⟨p, hp⟩ =>
      hp ▸ (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP _ hc p).isIntegral
  have : CharZero (CoordinateConeArithVar.ratioField (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  refine ⟨CoordinateConeArithVar.ratioField (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0, inferInstance, ⟨⟩,
    CoordinateConeArithVar.ratioPtL (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0, t0, ?_, ?_⟩
  · apply Subtype.ext
    exact div_self (hc ())
  · rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ hc, hy]

end DualCurvePointAlt

theorem DualCurvePoint.proof : DualCurvePoint.Statement := by
  intro K _ _ i F T _ _ b W hW hle
  obtain ⟨L, _, _, z, t0, hz, rfl⟩ := DualCurvePointAlt.exists_numberField_coords W hW
  obtain ⟨_, v, hv, hvz⟩ := DualCurvePointAlt.exists_point b z t0 hz hle
  exact ⟨L, inferInstance, inferInstance, inferInstance, v, hv, by rw [hvz]⟩

end

end GroundTheory.Heights₂.Heights
