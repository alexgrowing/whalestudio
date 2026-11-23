import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => f x * h x) g = fun y => chart f g y * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

private def mulOp (u : Sm E a) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun x => u.1 x * φ.1 x, fun g => by
    rw [chart_prod]
    exact (u.2 g).mul (φ.2 g)⟩
  map_add' φ ψ := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' c φ := Subtype.ext (funext fun x => mul_left_comm _ c _)

private theorem mulOp_apply (u φ : Sm E a) (g : GA E a) : (mulOp u φ).1 g = u.1 g * φ.1 g := rfl

private theorem lie_mulOp (X : Lie E a) (u φ : Sm E a) :
    lie E a X (mulOp u φ) = mulOp u (lie E a X φ) + mulOp (lie E a X u) φ := by
  refine Subtype.ext (funext fun g => ?_)
  have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
    simpa using chart_val f g 1
  change fderiv ℝ (chart (fun x => u.1 x * φ.1 x) g) (oneL E a) X =
    u.1 g * fderiv ℝ (chart φ.1 g) (oneL E a) X + fderiv ℝ (chart u.1 g) (oneL E a) X * φ.1 g
  rw [chart_prod, fderiv_fun_mul (differentiableAt_chart u.2 g) (differentiableAt_chart φ.2 g), hv, hv]
  simp [mul_comm]

private theorem ev_mulOp {d : ℕ} (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((mulOp u).rTensor _ m) g = u.1 g • ev m g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => rw [LinearMap.rTensor_tmul, ev_tmul, ev_tmul, mulOp_apply, mul_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]

private theorem smLie_mulOp (Ξ : AlgRep E a) (X : Lie E a) (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smLie Ξ X ((mulOp u).rTensor _ m) =
      (mulOp u).rTensor _ (smLie Ξ X m) + (mulOp (lie E a X u)).rTensor _ m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    change lie E a X (mulOp u φ) ⊗ₜ[ℂ] v + mulOp u φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v) =
      (mulOp u).rTensor _ (lie E a X φ ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) + mulOp (lie E a X u) φ ⊗ₜ[ℂ] v
    rw [lie_mulOp, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.add_tmul]
    abel
  | add x y hx hy => simp only [map_add, hx, hy]; abel

private theorem smK_mulOp (Ξ : AlgRep E a) (k : Kinf E a) (u : Sm E a) (hu : act (.cpt k) u = u)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smK Ξ k ((mulOp u).rTensor _ m) = (mulOp u).rTensor _ (smK Ξ k m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : act (.cpt k) (mulOp u φ) = mulOp (act (.cpt k) u) (act (.cpt k) φ) := rfl
    simp only [smK, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h, hu]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem lie_one_eq_zero (u : Sm E a) (hu : ∀ t g, u.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = u.1 g) :
    lie E a (oneL E a) u = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))
  have hc : ∀ t, infGL E a (c t) = GlobalTheory.UnitaryBC.splitCentre E a t := fun _ => rfl
  have hval : ∀ t : ℝ, toL (c t).val = Complex.exp t • oneL E a := fun t => by
    ext i j w
    by_cases h : i = j <;> simp [c, expU, toL, oneL, h, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have h0 : c 0 = 1 := Units.ext (by
    have h := hval 0
    rw [Complex.ofReal_zero, Complex.exp_zero, one_smul] at h
    exact h)
  have hd : HasDerivAt (fun t => toL (c t).val) (oneL E a) 0 := by
    simp only [hval]
    simpa using ((Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal).smul_const (oneL E a)
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve u g c _ h0 hd
  simp only [hc, ← CuspidalL2GL.splitCentre_comm, hu] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem levelFn_mulOp {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} {u φ : Sm E a} (hu : IsCut U u)
    (hφ : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (mulOp u φ) := by
  refine ⟨fun γ g => ?_, fun k hk => ?_, fun m hm => ?_⟩
  · rw [mulOp_apply, mulOp_apply, hu.left, hφ.1]
  · have h : act (.fin k) (mulOp u φ) = mulOp (act (.fin k) u) (act (.fin k) φ) := rfl
    rw [h, hu.level k hk, hφ.2.1 k hk]
  · have h : mulOp (0 : Sm E a) φ = 0 := Subtype.ext (funext fun x => zero_mul _)
    rw [lie_mulOp, lie_one_eq_zero u hu.centre, h, add_zero, hφ.2.2 m hm, map_smul]

private theorem ev_dCo (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) (X : Fin (q + 1) → Herm E a) (g : GA E a) :
    ev (dCo (smLie Ξ) ω X) g =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ev (smLie Ξ (toL (X i).1) (ω (i.removeNth X))) g := by
  rw [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

end

theorem UpperTheory.V.Lit.Geo.mulEx :
    MulEx := by
  intro E _ _ _ a U Ξ q u α hu hα
  refine ⟨(((mulOp u).rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap α,
    ⟨fun k => ?_, fun X i hi => ?_, fun X => ?_⟩, fun X g => ev_mulOp u (α X) g, fun X g => ?_⟩
  · intro X
    change (mulOp u).rTensor _ (α _) = smK Ξ k ((mulOp u).rTensor _ (α X))
    rw [smK_mulOp Ξ k u (hu.cpt k), hα.equiv k X]
  · change (mulOp u).rTensor _ (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (mulOp u).rTensor _ (α X) ∈ _
    refine Submodule.span_induction (p := fun m _ => (mulOp u).rTensor _ m ∈ _) ?_ ?_ ?_ ?_ (hα.val X)
    · rintro _ ⟨φ, v, hφ, rfl⟩
      exact Submodule.subset_span ⟨_, v, levelFn_mulOp hu hφ, LinearMap.rTensor_tmul _ _ _ _⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]; exact Submodule.smul_mem _ c hx
  · rw [ev_dCo, ev_dCo, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ • ev (smLie Ξ _ ((mulOp u).rTensor _ (α _))) g = _
    rw [smLie_mulOp, map_add, Pi.add_apply, ev_mulOp, ev_mulOp, smul_add, smul_comm, mul_smul]
