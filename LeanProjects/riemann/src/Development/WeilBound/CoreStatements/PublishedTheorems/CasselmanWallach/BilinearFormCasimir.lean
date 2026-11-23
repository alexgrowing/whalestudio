import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW.ExponentialKSet

variable {n : ℕ}

theorem exp_mem_kset' {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hs : (t • X)ᴴ = -(t • X) := by
      rw [Matrix.conjTranspose_smul, h1]
      simp
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((h2.smul_left t).exp_left).eq

theorem lie_of {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) : X ∈ lieSet ε := by
  show Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0
  rw [h1, Matrix.neg_mul, h2.eq, neg_add_cancel]

theorem commute_Jm {ε : Fin n → Bool} {X : Mx n} (h : ∀ i j, X i j ≠ 0 → ε i = ε j) :
    Commute X (Formalism.REAL.Jm ε) := by
  show X * Jm ε = Jm ε * X
  ext i j
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
  by_cases hx : X i j = 0
  · simp [hx]
  · rw [h i j hx, mul_comm]

theorem single_conjTranspose (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]

theorem single_neg' (a b : Fin n) (c : ℂ) : Matrix.single a b (-c) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.single_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem hasDerivAt_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    {f : ℝ → S} {f' : S} (h : HasDerivAt (fun t => (f t : H)) (f' : H) 0) : HasDerivAt f f' 0 := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  convert h using 2 with t
  show ‖((f t - f 0 - (t - 0) • f' : S) : H)‖ = _
  rw [Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul_of_tower]

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  simp [actM, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem actM_add (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

end Act

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

theorem key (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) {X : Mx n}
    (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (v y : kfin ε σ) :
    B (actM E X v) y = - B v (actM E X y) := by
  have hX : X ∈ lieSet ε := lie_of h1 h2
  have hKt : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Kset ε := exp_mem_kset' h1 h2
  have hKU : ∀ k ∈ Kset ε, k ∈ UJset ε := by
    rintro k ⟨hu, hc⟩
    have h1' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
    calc kᴴ * Formalism.REAL.Jm ε * k = star k * (k * Formalism.REAL.Jm ε) := by
          rw [Matrix.mul_assoc, ← hc]; rfl
      _ = Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hkinv : ∀ t : ℝ, ∀ w : H,
      σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((-t) • X)) w) = w := by
    intro t w
    rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ (hKU _ (hKt t)) _ (hKU _ (hKt (-t))),
      ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, hU.1.1]
    rfl
  obtain ⟨Sv, fv, hv, stv⟩ : IsKFin ε σ (v : H) := v.2
  obtain ⟨Sy, fy, hy, sty⟩ : IsKFin ε σ (y : H) := y.2
  let W : Submodule ℂ H := Sv ⊔ Sy
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_sup Sv Sy
  have stW : ∀ g ∈ Kset ε, ∀ x ∈ W, σ g x ∈ W := by
    intro g hg x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (stv g hg a ha) (sty g hg b hb)
  have hWk : W ≤ kfin ε σ := fun x hx => ⟨W, inferInstance, hx, stW⟩
  have hclosed : IsClosed (W : Set H) := Submodule.closed_of_finiteDimensional W
  have hvW : (v : H) ∈ W := Submodule.mem_sup_left hv
  have hyW : (y : H) ∈ W := Submodule.mem_sup_right hy
  have hder : ∀ x : kfin ε σ,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) x) ((actM E X x : H)) 0 := by
    intro x
    rw [hE X hX x]
    exact GlobalTheory.LowTypeDetermined.hasDerivAt_dRep (G := Formalism.REAL.Jm ε) (hD.1 _ x.2) hX
  have hmemW : ∀ x : kfin ε σ, (x : H) ∈ W → (actM E X x : H) ∈ W := by
    intro x hx
    refine hclosed.mem_of_tendsto (hder x).tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_mem _ (W.sub_mem (stW _ (hKt _) _ hx) (stW _ (hKt _) _ hx))
  let cv : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) v, stW _ (hKt t) _ hvW⟩
  let cy : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) y, stW _ (hKt t) _ hyW⟩
  have hcv : HasDerivAt cv ⟨_, hmemW v hvW⟩ 0 := hasDerivAt_sub W (hder v)
  have hcy : HasDerivAt cy ⟨_, hmemW y hyW⟩ (-0) := by
    rw [neg_zero]
    exact hasDerivAt_sub W (hder y)
  let ι : W →ₗ[ℂ] kfin ε σ := Submodule.inclusion hWk
  let ℓ1 : W →ₗ[ℝ] ℂ :=
    { toFun := fun w => B (ι w) y
      map_add' := fun a b => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        simp [Complex.coe_smul] }
  let ℓ2 : W →ₗ[ℝ] ℂ := ((B v).comp ι).restrictScalars ℝ
  let L1 : W →L[ℝ] ℂ := ⟨ℓ1, LinearMap.continuous_of_finiteDimensional ℓ1⟩
  let L2 : W →L[ℝ] ℂ := ⟨ℓ2, LinearMap.continuous_of_finiteDimensional ℓ2⟩
  have d1 := L1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcv
  have d2 := L2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcy.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)))
  have heq : (L1 ∘ cv) = (L2 ∘ (cy ∘ Neg.neg)) := by
    funext t
    show B (ι (cv t)) y = B v (ι (cy (-t)))
    exact hB _ (hKt t) v (ι (cy (-t))) (ι (cv t)) y rfl (hkinv t y).symm
  rw [heq] at d1
  have hu := d2.unique d1
  rw [neg_one_smul] at hu
  have e1 : ι ⟨_, hmemW v hvW⟩ = actM E X v := Subtype.ext rfl
  have e2 : ι ⟨_, hmemW y hyW⟩ = actM E X y := Subtype.ext rfl
  change B v (ι (-⟨_, hmemW y hyW⟩)) = B (ι ⟨_, hmemW v hvW⟩) y at hu
  rw [map_neg, map_neg, e1, e2] at hu
  rw [← hu]

theorem compact_pair (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) (a b : Fin n) (hab : ε a = ε b)
    (v y : kfin ε σ) : B (E a b v) y = B v (E b a y) := by
  have hsup : ∀ (c d : ℂ) (i j : Fin n),
      (Matrix.single a b c + Matrix.single b a d) i j ≠ 0 → ε i = ε j := by
    intro c d i j h
    by_contra hne
    apply h
    have e1 : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab)
    have e2 : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab.symm)
    simp [Matrix.single_apply, e1, e2]
  have s1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
      -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [star_one, star_neg, single_neg']
    abel
  have s2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [Complex.star_def, Complex.conj_I, single_neg']
    abel
  have k1 := key hU hD hE hB s1 (commute_Jm (hsup 1 (-1))) v y
  have k2 := key hU hD hE hB s2 (commute_Jm (hsup Complex.I Complex.I)) v y
  rw [actM_add, actM_single, actM_single] at k1 k2
  simp only [one_smul, neg_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    map_add, map_neg, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Complex.conj_I, smul_eq_mul,
    RingHom.id_apply, LinearMap.add_apply, LinearMap.neg_apply] at k1 k2
  linear_combination (1 / 2 : ℂ) * k1 + (Complex.I / 2) * k2 +
    ((B (E a b v) y - B v (E a b y) - B v (E b a y) + B (E b a v) y) / 2) * Complex.I_sq

end PositivityTheory.CW.ExponentialKSet

namespace PositivityTheory.CW

open ExponentialKSet in
theorem e2a : E2a := by
  unfold E2a AllIrr
  intro n ε H _ _ _ σ hU hI hD E hE B hB v y
  have hterm : ∀ a b, ε b = ε a → B ((E a b * E b a) v) y = B v ((E a b * E b a) y) := by
    intro a b h
    rw [Module.End.mul_apply, Module.End.mul_apply, compact_pair hU hD hE hB a b h.symm,
      compact_pair hU hD hE hB b a h]
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
    hterm a b (Finset.mem_filter.mp hb).2

end PositivityTheory.CW

end
