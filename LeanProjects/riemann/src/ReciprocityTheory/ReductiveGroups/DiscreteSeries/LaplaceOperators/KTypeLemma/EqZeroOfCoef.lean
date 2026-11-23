import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.DerivEntries
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem coef_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) (u : H) (m : D) :
    HasDerivAt (fun t : ℝ => ⟪u, σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ)
      ⟪u, σ g ((actM E X m : D) : H)⟫_ℂ 0 := by
  have h := (((innerSL ℂ u).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hD.deriv X hX m)
  refine HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun t => ?_)
  simp only [hσ.1.2 _ hg _ (exp_smul_mem_UJset hX t)]
  rfl

theorem act_cpart (E : Fin n → Fin n → Module.End ℂ D) (Z : Matrix (Fin n) (Fin n) ℂ) (m : D) :
    actM E Z m = actM E (cpart1 ε Z) m + Complex.I • actM E (cpart2 ε Z) m := by
  have h : actL E Z = actL E (cpart1 ε Z) + Complex.I • actL E (cpart2 ε Z) := by
    rw [← map_smul, ← map_add, ta_cpart_sum]
  exact congrArg (fun A : Module.End ℂ D => A m) h

theorem eq_zero_of_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {y : D} (hy : y ∈ genSub E V)
    (h : ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (y : H)⟫_ℂ = 0) : y = 0 := by
  let N : Set D := {m | ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (m : H)⟫_ℂ = 0}
  have hNr : ∀ X, inG ε X → ∀ m ∈ N, actM E X m ∈ N := fun X hX m hm g hg v' => by
    refine (coef_deriv hσ hD hg hX _ m).unique ?_
    have : (fun t : ℝ => ⟪((v' : D) : H), σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ) =
        fun _ => 0 := funext fun t => hm _ (ta_inUJ_mul_exp ε hg hX t) v'
    rw [this]; exact hasDerivAt_const _ _
  have hN : ∀ a b, ∀ m ∈ N, E a b m ∈ N := fun a b m hm g hg v' => by
    rw [← actM_single E a b, act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul, map_add,
      map_smul, inner_add_right, inner_smul_right, hNr _ (ta_inG_cpart1 ε _) m hm g hg v',
      hNr _ (ta_inG_cpart2 ε _) m hm g hg v']
    simp
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  let P : Submodule ℂ D :=
    { carrier := {u | ∀ m ∈ N, ⟪u, m⟫_ℂ = 0}
      add_mem' := fun hu hu' m hm => by rw [inner_add_left, hu m hm, hu' m hm, add_zero]
      zero_mem' := fun m _ => inner_zero_left m
      smul_mem' := fun c u hu m hm => by rw [inner_smul_left, hu m hm, mul_zero] }
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hle : genSub E V ≤ P := sInf_le ⟨fun v hv m hm => by
      have := hm 1 h1J ⟨v, hv⟩
      rw [hσ.1.1] at this
      exact this,
    fun a b u hu m hm => by rw [hU a b, hu _ (hN b a m hm), mul_zero]⟩
  exact inner_self_eq_zero.mp (hle hy y h)

theorem inner_deriv {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (f : ℝ → (U →L[ℂ] U)) (φ : U → U → ℂ)
    (h : ∀ a b, HasDerivAt (fun t => ⟪a, f t b⟫_ℂ) (φ a b) 0) (a b : U) :
    ⟪a, deriv f 0 b⟫_ℂ = φ a b := by
  let e := stdOrthonormalBasis ℂ U
  have hf : f = fun t => ∑ i, ∑ j, ⟪e i, f t (e j)⟫_ℂ • (innerSL ℂ (e j)).smulRight (e i) := by
    funext t
    ext x
    conv_lhs => rw [← e.sum_repr' (f t x), ← e.sum_repr' x]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, sum_smul,
      _root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [mul_comm]
  have hd : DifferentiableAt ℝ f 0 := by
    rw [hf]
    exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
      (h _ _).differentiableAt.smul_const _
  have h2 := (((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ U b)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  exact h2.unique (h a b)

theorem rWord_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (ι : V ≃ₗ[ℂ] U) (Ψ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U))
    (hco : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', Ψ g (ι v)⟫_ℂ)
    (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪ι v', rWord ε L Ψ g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g (((L.map (actM E)).prod (v : D) : D) : H)⟫_ℂ := by
  induction L with
  | nil => intro g hg v v'; exact (hco g hg v v').symm
  | cons Z L ih =>
    intro g hg v v'
    have hR : ∀ X, inG ε X → ⟪ι v', RdV X (rWord ε L Ψ) g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g ((actM E X ((L.map (actM E)).prod (v : D)) : D) : H)⟫_ℂ := by
      intro X hX
      have := inner_deriv (fun t : ℝ => rWord ε L Ψ (g * NormedSpace.exp ((t : ℂ) • X)))
        (fun a b => ⟪((ι.symm a : D) : H),
          σ g ((actM E X ((L.map (actM E)).prod (ι.symm b : D)) : D) : H)⟫_ℂ)
        (fun a b => by
          refine (coef_deriv hσ hD hg hX _ _).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
          have := ih _ (ta_inUJ_mul_exp ε hg hX t) (ι.symm b) (ι.symm a)
          rwa [ι.apply_symm_apply, ι.apply_symm_apply] at this) (ι v') (ι v)
      rwa [ι.symm_apply_apply, ι.symm_apply_apply] at this
    show ⟪ι v', (RdV (cpart1 ε Z) (rWord ε L Ψ) g + Complex.I • RdV (cpart2 ε Z) (rWord ε L Ψ) g) (ι v)⟫_ℂ = _
    rw [_root_.add_apply, _root_.smul_apply, inner_add_right,
      inner_smul_right, hR _ (ta_inG_cpart1 ε Z), hR _ (ta_inG_cpart2 ε Z), List.map_cons,
      List.prod_cons, Module.End.mul_apply, act_cpart (ε := ε) E Z, Submodule.coe_add,
      Submodule.coe_smul, map_add, map_smul, inner_add_right, inner_smul_right]

end Coef

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem omegaP_mem_nhds {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : OmegaP n ∈ 𝓝 x :=
  (tb_inv_hasFDerivAt (tb_isUnit_of_omegaP hx)).choose_spec.1.continuousAt.preimage_mem_nhds
    (isOpen_omega.mem_nhds hx)

def evZ (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : MMT μ →ₗ[ℂ] ℂ :=
  (LinearMap.proj z : (Matrix (Fin n) (Fin n) ℂ → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (cOm n).subtype ∘ₗ (mmSub μ).subtype

theorem evZ_word (μ : Fin n → ℤ) (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ z ∈ OmegaP n,
    evZ μ z ((L.map (actM (eMM μ))).prod (phiMM μ)) = hWord L (PhiP μ) z := by
  induction L with
  | nil => intro z hz; exact Set.indicator_of_mem hz _
  | cons Z L ih =>
    intro z hz
    set F := (L.map (actM (eMM μ))).prod (phiMM μ) with hF
    have h1 : ∀ a b, evZ μ z (eMM μ a b F) =
        fderiv ℂ (hWord L (PhiP μ)) z (z * Matrix.single a b 1) := fun a b => by
      have e : ((F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =ᶠ[𝓝 z] hWord L (PhiP μ) :=
        eventually_of_mem (omegaP_mem_nhds hz) ih
      rw [← e.fderiv_eq]
      exact Set.indicator_of_mem hz _
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← hF]
    show _ = fderiv ℂ (hWord L (PhiP μ)) z (z * Z)
    have hZ : z * Z = ∑ a, ∑ b, Z a b • (z * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ)) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp only [Matrix.mul_sum, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hZ]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h1]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
