import Mathlib
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsCharNe

noncomputable section

namespace PositivityTheory.ThKF.A

open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThKF.W GlobalTheory.HeisSchA GlobalTheory.RealWeil

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem trace_nondeg {a : mixedEmbedding.mixedSpace F} (ha : a ≠ 0) :
    ∃ b, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (a * b) ≠ 0 := by
  classical
  have ht : ∀ x : mixedEmbedding.mixedSpace F, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) x =
      ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re := fun x => by
    rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi]
    simp [Algebra.trace_complex_apply]
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := fun h => ha (Prod.ext h1 h)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 h2
    refine ⟨(0, Pi.single w ((starRingEnd ℂ) (a.2 w))), ?_⟩
    have e : ∀ u, (a.2 u * (Pi.single w ((starRingEnd ℂ) (a.2 w)) : _ → ℂ) u).re =
        if u = w then Complex.normSq (a.2 w) else 0 := fun u => by
      by_cases hu : u = w
      · subst hu
        rw [Pi.single_eq_same, Complex.mul_conj, Complex.ofReal_re, if_pos rfl]
      · rw [Pi.single_eq_of_ne hu, mul_zero, Complex.zero_re, if_neg hu]
    rw [ht]
    simp only [Prod.fst_mul, mul_zero, Pi.zero_apply, Finset.sum_const_zero, zero_add, Prod.snd_mul, Pi.mul_apply, e, mul_ite,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact mul_ne_zero two_ne_zero (Complex.normSq_pos.2 hw).ne'
  · obtain ⟨w, hw⟩ := Function.ne_iff.1 h1
    refine ⟨(Pi.single w 1, 0), ?_⟩
    rw [ht, Finset.sum_eq_single w (fun u _ hu => by simp [hu]) (by simp)]
    simpa using hw

def tb (x y : κ → mixedEmbedding.mixedSpace F) : ℝ := -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y)

theorem tb_add_left (a b c : κ → mixedEmbedding.mixedSpace F) : tb (a + b) c = tb a c + tb b c := by
  rw [tb, tb, tb, add_dotProduct, map_add, neg_add]

theorem tb_comm (a b : κ → mixedEmbedding.mixedSpace F) : tb a b = tb b a := by rw [tb, tb, dotProduct_comm]

theorem tb_smul_left (a : ℝ) (b c : κ → mixedEmbedding.mixedSpace F) : tb (a • b) c = a • tb b c := by
  rw [tb, tb, smul_dotProduct, map_smul, smul_neg]

theorem infE_dot (x y : κ → mixedEmbedding.mixedSpace F) :
    infE F x ⬝ᵥ infE F y = (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x ⬝ᵥ y), 0) : AF F) := by
  simp only [dotProduct, infE]
  refine Prod.ext ?_ ?_
  · refine (map_sum (p1 (F := F)) _ _).trans (Eq.trans ?_ (map_sum _ _ _).symm)
    exact Finset.sum_congr rfl fun i _ => (map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
  · exact (map_sum (p2 (F := F)) _ _).trans (Finset.sum_eq_zero fun i _ => mul_zero (0 : Af F))

theorem schrInf_apply {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    schrInf F ψ v f z = Complex.exp (((2 * π * tb z v.2 + π * tb v.1 v.2 : ℝ) : ℂ) * Complex.I) * f (z + v.1) := by
  have e : infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AF F) * (infE F v.1 ⬝ᵥ infE F v.2) =
      mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z ⬝ᵥ v.2 + (2⁻¹ : ℝ) • (v.1 ⬝ᵥ v.2))) 0 := by
    have e2 : ⅟(2 : AF F) * (infE F v.1 ⬝ᵥ infE F v.2) =
        mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((2⁻¹ : ℝ) • (v.1 ⬝ᵥ v.2))) 0 := by
      rw [invOf_mul_eq_iff_eq_mul_left, infE_dot, two_mul]
      refine Prod.ext ?_ (add_zero (0 : Af F)).symm
      show _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
      rw [← map_add, ← add_smul]
      norm_num
    rw [e2, infE_dot, map_add]
    exact Prod.ext rfl (add_zero (0 : Af F))
  rw [schrInf, e, hψ.2.2 _ (at_mk _)]
  have e3 : ∀ a, evI F (mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) 0) = a := fun a =>
    RingEquiv.apply_symm_apply _ _
  rw [e3, map_add, map_smul]
  congr 2
  simp only [tb, smul_eq_mul]
  push_cast
  ring

variable (F κ) in

structure Coord where
  n : ℕ
  Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)
  P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
  fst : ∀ w, (P w).1 = Q (pPart w)
  snd : ∀ w x, tb (Q x) (P w).2 = ⟪qPart w, x⟫

theorem nonempty_coord : Nonempty (Coord F κ) := by
  classical
  set Y := κ → mixedEmbedding.mixedSpace F
  set n := Module.finrank ℝ Y with hn
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ Y := by simp [hn]
  let Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Y := ContinuousLinearEquiv.ofFinrankEq hd
  let tl : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ tb tb_add_left tb_smul_left
    (fun a b c => by rw [tb_comm, tb_add_left, tb_comm b, tb_comm c]) (fun a b c => by rw [tb_comm, tb_smul_left, tb_comm c])
  let R : Y →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun i => tl (Q (EuclideanSpace.single i 1))
  have hR : ∀ y (x : EuclideanSpace ℝ (Fin n)), tb (Q x) y = ∑ i, x i * R y i := fun y x => by
    have : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    show tl (Q x) y = _
    conv_lhs => rw [this]
    simp [R]
  have hinj : Function.Injective R := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    obtain ⟨b, hb⟩ := trace_nondeg hi
    have := hR y (Q.symm (Pi.single i b))
    rw [hy, Q.apply_symm_apply, tb, single_dotProduct, mul_comm] at this
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, neg_eq_zero] at this
    exact hb this
  let R' : Y ≃ₗ[ℝ] (Fin n → ℝ) := R.linearEquivOfInjective hinj (by simp [hn])
  let Q' : (Fin n → ℝ) ≃ₗ[ℝ] Y := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.trans Q.toLinearEquiv
  refine ⟨⟨n, Q, (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans (Q'.prodCongr R'.symm), fun w => rfl, fun w x => ?_⟩⟩
  rw [hR]
  have : R (R'.symm fun i => w (Sum.inr i)) = fun i => w (Sum.inr i) := R'.apply_symm_apply _
  show ∑ i, x i * R (R'.symm fun i => w (Sum.inr i)) i = _
  rw [this]
  simp [qPart, PiLp.inner_apply]

namespace Coord

variable (C : Coord F κ)

def S : SInf F κ ≃L[ℂ] Sch (Fin C.n) where
  toFun := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ C.Q
  invFun := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ C.Q.symm
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv f := SchwartzMap.ext fun x => by simp
  right_inv f := SchwartzMap.ext fun x => by simp
  continuous_toFun := ContinuousLinearMap.continuous _
  continuous_invFun := ContinuousLinearMap.continuous _

theorem S_apply (f : SInf F κ) (x) : C.S f x = f (C.Q x) := rfl

theorem schr_coord {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (x) :
    schrInf F ψ (C.P w) f (C.Q x) = rhoFun w (fun y => f (C.Q y)) x := by
  rw [schrInf_apply hψ, C.fst, C.snd, C.snd, rhoFun, phase, map_add, real_inner_comm (pPart w)]

theorem rho_iff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w) (f g : SInf F κ) :
    ⇑(C.S g) = rhoFun w (C.S f) ↔ ⇑g = schrInf F ψ (C.P w) f :=
  ⟨fun h => funext fun y => by
    obtain ⟨x, rfl⟩ := C.Q.surjective y
    rw [C.schr_coord hψ]
    exact congrFun h x, fun h => funext fun x => by rw [S_apply, h, C.schr_coord hψ]; rfl⟩

theorem sympl_eq (w w') : sympl w w' = tb (C.P w).1 (C.P w').2 - tb (C.P w').1 (C.P w).2 := by
  rw [C.fst, C.fst, C.snd, C.snd, sympl, real_inner_comm (pPart w)]

theorem norm_eq {f g : SInf F κ} (h : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2) :
    ‖(C.S f).toLp 2 volume‖ = ‖(C.S g).toLp 2 volume‖ := by
  haveI := HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := BorelSpace.opensMeasurable
  have hm := Measure.isAddLeftInvariant_eq_smul (Measure.map C.Q volume) (volume : Measure (κ → mixedEmbedding.mixedSpace F))
  have e : ∀ a : SInf F κ, ∫⁻ x, ‖C.S a x‖ₑ ^ 2 = ∫⁻ x, ‖a x‖ₑ ^ 2 ∂(Measure.map C.Q volume) := fun a =>
    (lintegral_map (a.continuous.measurable.enorm.pow_const 2) C.Q.continuous.measurable).symm
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [e, e, hm, lintegral_smul_measure, lintegral_smul_measure, h]

def D (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : SInf F κ →L[ℂ] SInf F κ :=
  (C.S.symm : _ →L[ℂ] _) ∘L dRho (C.P.symm v) ∘L (C.S : _ →L[ℂ] _)

theorem hasDerivAt_D {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v) (f : SInf F κ) (y) :
    HasDerivAt (fun t : ℝ => schrInf F ψ (t • v) f y) (C.D v f y) 0 := by
  obtain ⟨x, rfl⟩ := C.Q.surjective y
  obtain ⟨w, rfl⟩ := C.P.surjective v
  simp only [← map_smul, C.schr_coord hψ]
  have : C.D (C.P w) f (C.Q x) = dRho w (C.S f) x := by
    rw [← S_apply]
    simp [D]
  rw [this]
  exact hasDerivAt_rhoFun w (C.S f) x

end Coord

end PositivityTheory.ThKF.A
