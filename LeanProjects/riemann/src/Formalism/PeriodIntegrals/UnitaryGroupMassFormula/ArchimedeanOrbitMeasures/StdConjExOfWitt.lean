import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FixIffSpan

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
  Formalism.L2.SG.Measures
open scoped TensorProduct Matrix

theorem theta_lin_indep {F E : Type} [Field F] [Field E] [Algebra F E] (φ : E →+* ℂ) (σ : E →+* E)
    (hσφ : ∀ a, φ (σ a) = starRingEnd ℂ (φ a)) (hfix : ∀ a, σ a = a → a ∈ Set.range (algebraMap F E))
    (b : Module.Basis (Fin 2) F E) (r : Fin 2 → ℝ) (h : (r 0 : ℂ) * φ (b 0) + (r 1 : ℂ) * φ (b 1) = 0) :
    r 0 = 0 ∧ r 1 = 0 := by
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  have hφ0 : φ (b 0) ≠ 0 := (map_ne_zero φ).2 hb0
  have hr1 : r 1 = 0 := by
    by_contra hr
    have hr' : (r 1 : ℂ) ≠ 0 := by exact_mod_cast hr
    set γ := b 1 / b 0 with hγ
    have hφγ : φ γ = ((-(r 0 / r 1) : ℝ) : ℂ) := by
      rw [hγ, map_div₀, div_eq_iff hφ0]
      push_cast
      field_simp
      first | linear_combination h | linear_combination -h | linear_combination (↑(r 1) : ℂ)⁻¹ * h
    have hσγ : σ γ = γ := by
      apply φ.injective
      rw [hσφ, hφγ, Complex.conj_ofReal]
    obtain ⟨a, ha⟩ := hfix γ hσγ
    have h1 : b 1 = a • b 0 := by
      rw [Algebra.smul_def, ha, hγ, div_mul_cancel₀ _ hb0]
    exact absurd h1 (by
      intro e
      have hli := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      have := hli (fun i => if i = 0 then a else -1) (by
        rw [Fin.sum_univ_two]
        simp [e])
      simpa using this 1)
  refine ⟨?_, hr1⟩
  rw [hr1] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_eq_zero, hφ0, or_false] at h
  exact_mod_cast h

theorem thetaInf_tmul {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (c : Ainf X.B.I.F) (e : X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (c ⊗ₜ[X.B.I.F] e) = PI.AprimeInfU.evInf X v c * X.B.I.φ v e := by
  simp only [PI.AprimeInfU.thetaInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
  rfl

theorem thetaInf_inj {D : D7} (X : HidaSetting D) (y : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (h : ∀ v, PI.AprimeInfU.thetaInf X v y = 0) : y = 0 := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let b : Module.Basis (Fin 2) X.B.I.F X.B.I.E := Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) b
  have hy : y = ∑ i, B.repr y i ⊗ₜ[X.B.I.F] b i := by
    conv_lhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hc : ∀ i, B.repr y i = 0 := by
    intro i
    change (B.repr y i : (v : InfinitePlace X.B.I.F) → v.Completion) = 0
    funext v
    have hvr : v.IsReal := IsTotallyReal.isReal v
    have hv := h v
    rw [hy, map_sum, Fin.sum_univ_two, thetaInf_tmul, thetaInf_tmul] at hv
    have hev : ∀ c : Ainf X.B.I.F, PI.AprimeInfU.evInf X v c =
        ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
          ((c : (w : InfinitePlace X.B.I.F) → w.Completion) v) : ℝ) : ℂ) := by
      intro c
      rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      rfl
    rw [hev, hev] at hv
    have key := theta_lin_indep (X.B.I.φ v) (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E)
      (fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a)
      (fun a ha => RingHom.mem_range.1 ((X.B.I.cm.fixed a).1 ha)) b
      (fun i => InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
        ((B.repr y i : (w : InfinitePlace X.B.I.F) → w.Completion) v)) hv
    have hz : InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
        ((B.repr y i : (w : InfinitePlace X.B.I.F) → w.Completion) v) = 0 := by
      fin_cases i
      · exact key.1
      · exact key.2
    exact (map_eq_zero_iff _ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr).injective).1 hz
  rw [hy]
  simp [hc]

theorem thetaInf_inclR {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (inclR (Ainf X.B.I.F) e) = X.B.I.φ v e := by
  rw [show inclR (Ainf X.B.I.F) e = (1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e from rfl, thetaInf_tmul, map_one, one_mul]

theorem uMat_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) :
    uMat (x v) = (X.B.I.P v)⁻¹ * (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb x) :
      GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map (PI.AprimeInfU.thetaInf X v) *
      X.B.I.P v := by
  have e : uMat (x v) = ofHAInf X.B.I (toHA X.B.I hb (x, 1)) v := ((toHA_isBridge X.B.I hb) (x, 1)).1 v
  rw [e]
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, PI.AprimeInfU.thetaV_eq]
  rfl

theorem stabInfV_holds : StabInfV := by
  intro D X u' hb x
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb x) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hPu : ∀ v, IsUnit (X.B.I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hmap : ∀ v, Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (x v) * (X.B.I.P v)⁻¹ := by
    intro v
    rw [uMat_toInf X hb x v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hPu v), Matrix.mul_one]
  have hvec : ∀ v b i, PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y0 X u' b) i) =
      ((Mm.map (PI.AprimeInfU.thetaInf X v)) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i := by
    intro v b i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  have hY0 : ∀ v b i, PI.AprimeInfU.thetaInf X v (Y0 X u' b i) = X.B.I.φ v (tupH (frameOf X u') b i) := by
    intro v b i
    rw [show Y0 X u' b i = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b i) from rfl, thetaInf_inclR]
  have hsmul : X.toInf hb x • Y0 X u' = fun b => Mm *ᵥ Y0 X u' b := rfl
  rw [MulAction.mem_stabilizer_iff, hsmul]
  constructor
  · intro hfix v b
    have h1 : (Mm.map (PI.AprimeInfU.thetaInf X v)) *ᵥ (fun j => X.B.I.φ v (tupH (frameOf X u') b j)) =
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext i
      rw [← hvec, ← hY0]
      exact congrArg (PI.AprimeInfU.thetaInf X v) (congrFun (congrFun hfix b) i)
    rw [hmap] at h1
    unfold wV
    have h2 := congrArg (fun z => (X.B.I.P v)⁻¹ *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hPu v), Matrix.one_mul] at h2
    rw [Matrix.mulVec_mulVec]
    exact h2
  · intro hw
    funext b i
    have h0 : Mm *ᵥ Y0 X u' b - Y0 X u' b = 0 := by
      funext i'
      refine thetaInf_inj X _ fun v => ?_
      rw [Pi.sub_apply, map_sub, hvec, hY0, hmap, sub_eq_zero]
      have hv := hw v b
      unfold wV at hv
      calc ((X.B.I.P v * uMat (x v) * (X.B.I.P v)⁻¹) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i'
          = (X.B.I.P v *ᵥ (uMat (x v) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)))) i' := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (X.B.I.P v *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i' := by rw [hv]
        _ = X.B.I.φ v (tupH (frameOf X u') b i') := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mulVec]
    exact sub_eq_zero.1 (congrFun h0 i)

theorem stdConjEx_of_witt (h : WittBlock) : StdConjEx := stdConjEx_of stabInfV_holds h

end PI.AprimeInfW
