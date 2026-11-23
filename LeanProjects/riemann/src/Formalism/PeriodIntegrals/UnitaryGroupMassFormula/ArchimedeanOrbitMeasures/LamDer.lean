import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarMapContDiffAtBase
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfWitt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem reimV_add {V : Type} {n m : ℕ} (A B : V → Matrix (Fin n) (Fin m) ℂ) :
    reimV (A + B) = reimV A + reimV B := by
  ext p
  by_cases h : p.2.2.2 <;> simp [reimV, h]

theorem reimV_smul {V : Type} {n m : ℕ} (r : ℝ) (A : V → Matrix (Fin n) (Fin m) ℂ) :
    reimV (fun v => (r : ℂ) • A v) = r • reimV A := by
  ext p
  by_cases h : p.2.2.2 <;> simp [reimV, h]

theorem map_inv_of_det {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) : (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.map f * (A⁻¹).map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.map_one _ (map_zero _) (map_one _)]
  exact (Matrix.inv_eq_right_inv h1).symm

theorem beta_frame_coordinates {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    betaV X v (Y0 X u') = Matrix.of fun i b => wV X u' v b i := by
  ext i b
  simp only [betaV, Matrix.of_apply, wV]
  congr 2
  funext j
  rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]

theorem gram_betaV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    (betaV X v (Y0 X u'))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * betaV X v (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (X.B.I.φ v) := by
  ext b b'
  rw [Matrix.map_apply, ← gram_wV, beta_frame_coordinates]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem map_symm_of_map {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F) (a : ENNReal)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (h : μ.map e = a • ν) : ν.map e.symm = a⁻¹ • μ := by
  have h1 : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    have : (e.symm ∘ e : E → E) = id := by funext x; simp
    rw [this, Measure.map_id]
  rw [h, Measure.map_smul] at h1
  rw [← h1, smul_smul, ENNReal.inv_mul_cancel ha0 hat, one_smul]

theorem add_zero_of {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A → B) (hf : ∀ x y, f (x + y) = f x + f y) :
    f 0 = 0 := by
  have := hf 0 0
  rw [add_zero] at this
  simpa using this

theorem lamDet_of (hB : BetaIso) (hM : MuBridge) (hN : NuBridge) (hD : DKForm) (hR : RowsZ) (hDet : DetT)
    (hP : PlaceJacAll) : LamDet := by
  intro D X u' ψ hT μinf νinf fibInf hPH η _ eH cν hadd hν hb c S ι _ L hc hL
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : BorelSpace (HmI X) := ⟨rfl⟩
  obtain ⟨Bc, hBc⟩ := hB X
  obtain ⟨κ, _, Hh, Tc, hH1, hH2, hH3, hTcadd, hHθ, hνT⟩ := hN X u' ψ hT μinf νinf fibInf hPH
  have hμT := densMu_holds X u' ψ hT μinf νinf fibInf hPH
  have hμB := hM X u' ψ hT μinf νinf fibInf hPH
  set s := Real.sqrt |(matI X).det| with hs
  set N := X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F) with hNdef
  set w : InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
    fun v => uMat (c v)⁻¹ * betaV X v (Y0 X u') with hw
  have hcinv : ∀ v, (uMat (c v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (c v)⁻¹ = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun v => ((c v)⁻¹).2
  have hcu : ∀ v, (uMat (c v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (c v) = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun v => (c v).2
  have hcc : ∀ v, uMat (c v) * uMat (c v)⁻¹ = 1 := fun v => by simp [uMat]
  have hG : ∀ v, (w v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * w v =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (X.B.I.φ v) := by
    intro v
    rw [← gram_betaV]
    simp only [hw, Matrix.conjTranspose_mul]
    calc (betaV X v (Y0 X u'))ᴴ * (uMat (c v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (uMat (c v)⁻¹ * betaV X v (Y0 X u'))
        = (betaV X v (Y0 X u'))ᴴ * ((uMat (c v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (c v)⁻¹) *
            betaV X v (Y0 X u') := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcinv]
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hPH
  have hmd : ∀ v, ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (X.B.I.φ v)).det =
      X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det := fun v => (RingHom.map_det _ _).symm
  have hGdet : ∀ v, ((w v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * w v).det ≠ 0 := by
    intro v; rw [hG, hmd]; exact (map_ne_zero _).2 hdet
  have hGnorm : ∀ v, ‖((w v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * w v).det‖ = Tw u' := by
    intro v; rw [hG, hmd]; exact hDet X u' ψ hT μinf νinf fibInf hPH v
  obtain ⟨Fe, hFe, hvolF⟩ := hP (InfinitePlace X.B.I.F) X.B.I.n (D.R.rS + 1 + D.R.rS) X.B.I.ε S w
    (fun v => uMat (c v)) L Hh (fun v => by rw [(hc.1 v).1]; exact dimNK_holds X)
    (hR X u' ψ hT μinf νinf fibInf hPH hb c S hc) hGdet hcu (fun x v => hL.1 x v) hL.2.1 hL.2.2 hH1 hH2 hH3

  have hEs : ∀ x y, eH.symm (x + y) = eH.symm x + eH.symm y := by
    intro x y; apply eH.injective; rw [hadd]; simp
  have hTs : ∀ x y, Tc.symm (x + y) = Tc.symm x + Tc.symm y := by
    intro x y; apply Tc.injective; rw [hTcadd]; simp
  let Th0 : EuclideanSpace ℝ η →+ EuclideanSpace ℝ κ :=
    { toFun := fun t => Tc (eH.symm t)
      map_zero' := by rw [add_zero_of _ hEs, add_zero_of _ hTcadd]
      map_add' := fun x y => by rw [hEs, hTcadd] }
  let Ti0 : EuclideanSpace ℝ κ →+ EuclideanSpace ℝ η :=
    { toFun := fun t => eH (Tc.symm t)
      map_zero' := by rw [add_zero_of _ hTs, add_zero_of _ hadd]
      map_add' := fun x y => by rw [hTs, hadd] }
  let Th : EuclideanSpace ℝ η ≃L[ℝ] EuclideanSpace ℝ κ :=
    ContinuousLinearEquiv.equivOfInverse (Th0.toRealLinearMap (Tc.continuous.comp eH.symm.continuous))
      (Ti0.toRealLinearMap (eH.continuous.comp Tc.symm.continuous))
      (fun t => by simp [Th0, Ti0]) (fun t => by simp [Th0, Ti0])
  have hThe : ∀ t, Th t = Tc (eH.symm t) := fun t => rfl
  have hvolT : (volume : Measure (EuclideanSpace ℝ η)).map Th = (ENNReal.ofReal cν)⁻¹ • volume := by
    have h1 : νinf.map Tc = (νinf.map eH).map Th := by
      rw [Measure.map_map Th.continuous.measurable eH.continuous.measurable]
      congr 1
      funext S'
      simp [hThe]
    rw [hνT, hν, Measure.map_smul] at h1
    have hc0 : ENNReal.ofReal cν ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at h1
      exact (NeZero.ne (volume : Measure (EuclideanSpace ℝ κ))) h1
    rw [h1, smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul]
  have hcν : 0 < cν := by
    by_contra hneg
    push_neg at hneg
    have h1 : νinf.map Tc = (νinf.map eH).map Th := by
      rw [Measure.map_map Th.continuous.measurable eH.continuous.measurable]
      congr 1
      funext S'
      simp [hThe]
    rw [hνT, hν, ENNReal.ofReal_of_nonpos hneg, zero_smul, Measure.map_zero] at h1
    exact (NeZero.ne (volume : Measure (EuclideanSpace ℝ κ))) h1
  have hs0 : 0 < s := Real.sqrt_pos.2 (abs_pos.2 (matNDH_holds X u' ψ hT μinf νinf fibInf hPH))
  have hvolB : (volume : Measure (EuclideanSpace ℝ (KapI X))).map Bc =
      ((ENNReal.ofReal s)⁻¹ * ENNReal.ofReal (2 ^ N)) • volume := by
    have h2 : μinf.map (fun Y => reimV (fun v => betaV X v Y)) = (μinf.map (tupCoord X)).map Bc := by
      rw [Measure.map_map Bc.continuous.measurable (tupCoord X).continuous.measurable]
      congr 1
      funext Y
      exact (hBc Y).symm
    rw [hμB, hμT, Measure.map_smul] at h2
    have hs0' : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs0).ne'
    calc (volume : Measure (EuclideanSpace ℝ (KapI X))).map Bc
        = (ENNReal.ofReal s)⁻¹ • (ENNReal.ofReal s • (volume : Measure (EuclideanSpace ℝ (KapI X))).map Bc) := by
          rw [smul_smul, ENNReal.inv_mul_cancel hs0' ENNReal.ofReal_ne_top, one_smul]
      _ = _ := by rw [← h2, smul_smul]

  let Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃L[ℝ] EuclideanSpace ℝ (KapI X) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ ι)).prodCongr Th).trans (Fe.trans Bc.symm)
  have hΦ : ∀ z, Φ z = Bc.symm (Fe (z.1, Th z.2)) := fun z => rfl
  have hTinv : ∀ v, (TinvI X u').map (PI.AprimeInfU.thetaInf X v) =
      ((w v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * w v)⁻¹ := by
    intro v
    rw [hG, ← map_inv_of_det _ _ hdet]
    ext i j
    simp only [TinvI, Matrix.map_apply]
    exact thetaInf_inclR X v _
  refine ⟨Φ, fun z => ?_, ?_⟩
  · apply Bc.injective
    rw [hΦ, ContinuousLinearEquiv.apply_symm_apply, hFe]
    unfold LamMap
    rw [map_add, map_smul]
    have e1 : Bc (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0 z.1) =
        reimV (fun v => uMat (c v) * L z.1 v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) := by
      rw [← (tupCoord X).apply_symm_apply (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0 z.1), hBc]
      congr 1
      funext v
      exact hD X u' ψ hT μinf νinf fibInf hPH hb c S L hc hL z.1 v
    have e2 : Bc (tupCoord X (rmulT X (TinvI X u' * ((eH.symm z.2 : HmI X) : Matrix _ _ _)) (Y0 X u'))) =
        reimV (fun v => betaV X v (Y0 X u') * ((w v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * w v)⁻¹ * Hh (Th z.2) v) := by
      rw [hBc]
      congr 1
      funext v
      rw [betaV_rmul, Matrix.map_mul, hTinv, hThe, hHθ]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, ← reimV_smul, ← reimV_add]
    congr 1
    funext v
    simp only [hw, Matrix.mul_add, Matrix.mul_smul, Pi.add_apply]
    congr 1
    · simp only [Matrix.mul_assoc]
    · rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring]
      congr 1
      simp only [← Matrix.mul_assoc, hcc, Matrix.one_mul]
  ·
    have hTw : (0 : ℝ) < Tw u' := by
      unfold Tw
      exact_mod_cast (D.mem u').A.T_prime.pos
    set DP := ∏ v, (2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS)) /
      ‖((w v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * w v).det‖ ^ (S v).card with hDP
    have hDP' : DP = ((2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS)) / Tw u' ^ D.R.k) ^
        Fintype.card (InfinitePlace X.B.I.F) := by
      rw [hDP, ← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hGnorm v, (hc.1 v).1]
    have hDPpos : 0 < DP := by rw [hDP']; positivity
    have hN2 : (0 : ℝ) < 2 ^ N := by positivity
    set Dv := s * DP / (cν * 2 ^ N) with hDv
    have hDvpos : 0 < Dv := by positivity
    refine ⟨Dv, hDvpos, ?_, ?_⟩
    ·
      have hP1 : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map
          ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ ι)).prodCongr Th) =
          (ENNReal.ofReal cν)⁻¹ • (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) := by
        rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
        have e : (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ ι)).prodCongr Th :
            EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = Prod.map id Th := by
          funext z; rfl
        rw [e, ← Measure.map_prod_map _ _ measurable_id Th.continuous.measurable, Measure.map_id, hvolT,
          Measure.prod_smul_right]
      have ha0 : (ENNReal.ofReal s)⁻¹ * ENNReal.ofReal (2 ^ N) ≠ 0 :=
        mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) (ENNReal.ofReal_pos.2 hN2).ne'
      have hat : (ENNReal.ofReal s)⁻¹ * ENNReal.ofReal (2 ^ N) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hs0).ne') ENNReal.ofReal_ne_top
      have hB2 := map_symm_of_map _ _ Bc _ ha0 hat hvolB
      have e2 : (Φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ (KapI X)) =
          Bc.symm ∘ Fe ∘ ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ ι)).prodCongr Th) := by
        funext z; rfl
      rw [e2, ← Measure.map_map Bc.symm.continuous.measurable (Fe.continuous.measurable.comp
          ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ ι)).prodCongr Th).continuous.measurable),
        ← Measure.map_map Fe.continuous.measurable
          ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ ι)).prodCongr Th).continuous.measurable,
        hP1, Measure.map_smul, hvolF, Measure.map_smul, Measure.map_smul, hB2, smul_smul, smul_smul]
      congr 1
      have h1 : (0 : ℝ) < s⁻¹ * 2 ^ N := by positivity
      have h2 : (0 : ℝ) ≤ cν⁻¹ * DP := by positivity
      rw [← ENNReal.ofReal_inv_of_pos hcν, ← ENNReal.ofReal_inv_of_pos hs0, ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le),
        ← ENNReal.ofReal_inv_of_pos h1, ← ENNReal.ofReal_mul (inv_nonneg.2 hcν.le), ← ENNReal.ofReal_mul h2]
      congr 1
      rw [hDv]
      field_simp
    ·
      rw [hDv, hDP']
      show s / (s * (((2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS)) / Tw u' ^ D.R.k) ^
        Fintype.card (InfinitePlace X.B.I.F)) / (cν * 2 ^ N) * cν) = Tw u' ^ (D.R.k * Fintype.card (InfinitePlace X.B.I.F))
      rw [hNdef, pow_mul, pow_mul, div_pow]
      have hb : (0 : ℝ) < (Tw u' ^ D.R.k) ^ Fintype.card (InfinitePlace X.B.I.F) := by positivity
      have ha : (0 : ℝ) < ((2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS))) ^ Fintype.card (InfinitePlace X.B.I.F) := by
        positivity
      field_simp
      ring

end PI.AprimeInfW
