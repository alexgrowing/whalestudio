import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FfExpWedgeHasDeriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysApplySingle
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem sgE_cpT (a b : Fin n) :
    sgE ε (cpT (N := N)) cmT a b = LinearMap.lTensor N (sgE ε (cpFock (n := n)) cmFock a b) := by
  have e : ∀ f : Module.End ℂ (Fock n), LinearMap.lTensor N f = Module.End.lTensorAlgHom ℂ (Fock n) N f :=
    fun f => rfl
  unfold sgE
  split_ifs <;> rw [e] <;> simp only [map_sum, map_mul, map_neg, map_zero] <;> rfl

theorem tcoef_eq_sum (φ : Module.Dual ℂ (Fock n)) (y : TensorProduct ℂ N (Fock n)) :
    tcoef φ y = ∑ s : Finset (Fin (n * n)), φ (fockBasis n s) • tcoef ((fockBasis n).coord s) y := by
  conv_lhs => rw [tcoef_expand y]
  simp only [map_sum, tcoef_tmul]

theorem tco_actDiag (E : Fin n → Fin n → Module.End ℂ N) (X : Matrix (Fin n) (Fin n) ℂ)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) =
      actM E X (tcoef ((fockBasis n).coord s) y) + tcoef ((fockBasis n).coord s ∘ₗ sgX ε X) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [actM, diagE, sgE_cpT, eT, sgX, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
      TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply, map_sum, map_smul, map_add,
      tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [Finset.smul_sum, Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul, mul_comm]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_mul]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, map_add, map_add]
    abel

end T

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tco_wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (wK hD hk y) =
      ∑ s', (fockBasis n).coord s (ff ε k (fockBasis n s')) • sigD hD hk (tcoef ((fockBasis n).coord s') y) := by
  conv_lhs => rw [tcoef_expand y]
  simp only [map_sum, wK, TensorProduct.map_tmul, tcoef_tmul, AlgHom.toLinearMap_apply]

theorem tco_wK_hasDeriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inK ε X) (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    HasDerivAt (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
        (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H))
      ((tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) : D) : H) 0 := by
  have hXh : Xᴴ = -X := ((HW.inK_iff' ε X).1 hX).1
  have hfun : (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
      (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H)) =
      fun t : ℝ => ∑ s', (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X)) (fockBasis n s')) •
        σ (NormedSpace.exp ((t : ℂ) • X)) ((tcoef ((fockBasis n).coord s') y : D) : H) := by
    funext t
    rw [tco_wK, Submodule.coe_sum]
    rfl
  rw [hfun]
  have hc : ∀ s', HasDerivAt (fun t : ℝ => (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X))
      (fockBasis n s'))) ((fockBasis n).coord s (sgX ε X (fockBasis n s'))) 0 := by
    intro s'
    have := hasDerivAt_pi.1 (ff_exp_hasDeriv (ε := ε) hXh (fockBasis n s')) s
    simpa only [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using this
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ =>
    (hc s').fun_smul (hD.deriv X hX.1 (tcoef ((fockBasis n).coord s') y))
  convert h using 1
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  simp only [h0, ff_one, AlgHom.id_apply, hσ.1.1, ContinuousLinearMap.one_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [tco_actDiag, Submodule.coe_add, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y, Submodule.coe_sum,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
    simp

def coordH : TensorProduct ℂ D (Fock n) →ₗ[ℂ] (Finset (Fin (n * n)) → H) :=
  LinearMap.pi fun s => D.subtype ∘ₗ tcoef ((fockBasis n).coord s)

theorem coordH_apply (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    coordH y s = ((tcoef ((fockBasis n).coord s) y : D) : H) := rfl

theorem coordH_injective : Function.Injective (coordH (D := D) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot, tcoef_expand y]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : ((tcoef ((fockBasis n).coord s) y : D) : H) = 0 := congrFun hy s
  rw [show tcoef ((fockBasis n).coord s) y = 0 from Subtype.ext this, TensorProduct.zero_tmul]

theorem actDiag_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    actM (diagE ε (eT E) cpT cmT) X y ∈ S' := by
  let T := S'.map (coordH (D := D) (n := n))
  have : FiniteDimensional ℂ T := Module.Finite.map S' coordH
  have hTc : IsClosed (T : Set (Finset (Fin (n * n)) → H)) := Submodule.closed_of_finiteDimensional T
  have hder : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) X y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have h1 : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) ∈ T :=
    fun t => Submodule.mem_map_of_mem (hK _ _ y hy)
  have hmem : coordH (actM (diagE ε (eT E) cpT cmT) X y) ∈ T :=
    hTc.mem_of_tendsto hder.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (h1 _) (h1 _)))
  obtain ⟨w, hw, hweq⟩ := Submodule.mem_map.1 hmem
  rwa [coordH_injective hweq] at hw

theorem diagE_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    diagE ε (eT E) cpT cmT a b y ∈ S' := by
  have h1 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab 1) hy
  have h2 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab Complex.I) hy
  rw [USum.actM_zM] at h1 h2
  have gen : ∀ x y : TensorProduct ℂ D (Fock n),
      x = (1 / 2 : ℂ) • ((x - y) - Complex.I • (Complex.I • x - (-Complex.I) • y)) := by
    intro x y
    rw [smul_sub Complex.I, smul_smul, smul_smul, show Complex.I * Complex.I = -1 from Complex.I_mul_I,
      show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg]]
    module
  have key : diagE ε (eT E) cpT cmT a b y = (1 / 2 : ℂ) •
      ((((1 : ℂ) • diagE ε (eT E) cpT cmT a b - star (1 : ℂ) • diagE ε (eT E) cpT cmT b a) y) -
        Complex.I • (((Complex.I • diagE ε (eT E) cpT cmT a b - star Complex.I • diagE ε (eT E) cpT cmT b a)) y)) := by
    simp only [Complex.star_def, Complex.conj_I, map_one]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul]
    exact gen _ _
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))

end ReciprocityTheory.ChartRestriction.DS.TRGap
