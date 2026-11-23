import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.GrowthOfBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def resB (W : Submodule ℂ (smD ε σ)) (hW : IsKStableSub ε (smE ε σ) W) (a b : Fin n) : Module.End ℂ W :=
  if h : ε a = ε b then (smE ε σ a b).restrict (fun x hx => hW a b h x hx) else 0

theorem resB_apply {W : Submodule ℂ (smD ε σ)} (hW : IsKStableSub ε (smE ε σ) W) {a b : Fin n} (h : ε a = ε b)
    (x : W) : ((resB W hW a b x : W) : smD ε σ) = smE ε σ a b x := by
  simp [resB, dif_pos h]

theorem kRel_resB (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W : Submodule ℂ (smD ε σ)}
    (hW : IsKStableSub ε (smE ε σ) W) : Formalism.REAL.KRel ε (resB W hW) := by
  intro a b c d hab hcd
  have hG := (isDerivedOn_smE hσ).glRep a b c d
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h1 := congrArg (fun T : Module.End ℂ (smD ε σ) => T x) hG
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, resB_apply hW hab, resB_apply hW hcd]
  rw [h1]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc; subst hda
    simp [resB_apply hW (rfl : ε d = ε d), resB_apply hW (rfl : ε b = ε b)]
  · subst hbc
    simp [hda, resB_apply hW (hab.trans hcd)]
  · subst hda
    simp [hbc, resB_apply hW (hcd.trans hab)]
  · simp [hbc, hda]

theorem kUnit_resB (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W : Submodule ℂ (smD ε σ)}
    (hW : IsKStableSub ε (smE ε σ) W) : Formalism.REAL.KUnit ε (resB W hW) := by
  intro a b hab x y
  have hU := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ) a b (x : smD ε σ) (y : smD ε σ)
  rw [adjSign, if_pos hab, one_mul] at hU
  simp only [Submodule.coe_inner, resB_apply hW hab, resB_apply hW hab.symm]
  exact hU

theorem hasSum_actM_pow_div_factorial (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W : Submodule ℂ (smD ε σ)}
    [FiniteDimensional ℂ W] (hW : IsKStableSub ε (smE ε σ) W) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {x : smD ε σ} (hx : x ∈ W) :
    HasSum (fun m : ℕ => (((1 : ℝ) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) • ((((actM (smE ε σ) Z) ^ m) x : smD ε σ) : H))
      (σ (NormedSpace.exp Z) (x : H)) := by
  have hD := isDerivedOn_smE hσ
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hW inferInstance hZ
  have hs : Summable fun m : ℕ => C ^ m * ‖x‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_right ‖x‖
    refine this.congr fun m => ?_
    simp
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 x (fun m => C ^ m * ‖x‖) (fun m => hC x hx m) 0 1 hs
  rw [exp_zero_smul, hσ.1.1] at hsum
  simpa only [Complex.ofReal_one, one_smul, ContinuousLinearMap.one_apply, sub_zero] using hsum

theorem intertwiner_actM_pow_comm {W W' : Submodule ℂ (smD ε σ)} (hW : IsKStableSub ε (smE ε σ) W)
    (hW' : IsKStableSub ε (smE ε σ) W') (φ : W →ₗ[ℂ] W')
    (hφ : ∀ a b, ε a = ε b → ∀ x : W, φ (resB W hW a b x) = resB W' hW' a b (φ x))
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (m : ℕ) (x : W) :
    ((φ ⟨((actM (smE ε σ) Z) ^ m) x, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 m⟩ : W') : smD ε σ) =
      ((actM (smE ε σ) Z) ^ m) (φ x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have e1 : (⟨((actM (smE ε σ) Z) ^ (m + 1)) x, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 (m + 1)⟩ : W) =
        ∑ a, ∑ b, Z a b • resB W hW a b
          ⟨((actM (smE ε σ) Z) ^ m) x, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 m⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      show ((actM (smE ε σ) Z) ^ (m + 1)) (x : smD ε σ) = _
      rw [pow_succ', Module.End.mul_apply]
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : ε a = ε b
      · rw [resB_apply hW hab]
      · rw [inK_apply_eq_zero hZ hab, zero_smul, zero_smul]
    rw [e1, map_sum]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
    rw [pow_succ', Module.End.mul_apply, ← ih x]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : ε a = ε b
    · rw [hφ a b hab, resB_apply hW' hab]
    · rw [inK_apply_eq_zero hZ hab, zero_smul, zero_smul]

theorem intertwiner_comm_kset (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W W' : Submodule ℂ (smD ε σ)}
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ W'] (hW : IsKStableSub ε (smE ε σ) W)
    (hW' : IsKStableSub ε (smE ε σ) W') (φ : W →ₗ[ℂ] W')
    (hφ : ∀ a b, ε a = ε b → ∀ x : W, φ (resB W hW a b x) = resB W' hW' a b (φ x))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (x y : W)
    (hxy : ((y : smD ε σ) : H) = σ g ((x : smD ε σ) : H)) :
    (((φ y : W') : smD ε σ) : H) = σ g (((φ x : W') : smD ε σ) : H) := by
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  let Wh : Submodule ℂ H := W.map (smD ε σ).subtype
  have : FiniteDimensional ℂ Wh := Module.Finite.map W _
  let e : W ≃ₗ[ℂ] Wh := Submodule.equivMapOfInjective _ Subtype.val_injective W
  let Φ : H →L[ℂ] H := ((smD ε σ).subtypeL.comp W'.subtypeL).comp
    ((LinearMap.toContinuousLinearMap φ).comp
      ((LinearMap.toContinuousLinearMap (e.symm : Wh →ₗ[ℂ] W)).comp Wh.orthogonalProjection))
  have hΦ : ∀ z : W, Φ ((z : smD ε σ) : H) = (((φ z : W') : smD ε σ) : H) := by
    intro z
    have hz : ((z : smD ε σ) : H) ∈ Wh := Submodule.mem_map_of_mem z.2
    have h1 : Wh.orthogonalProjection ((z : smD ε σ) : H) = ⟨_, hz⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨_, hz⟩ : Wh)
    have h2 : e.symm ⟨_, hz⟩ = z := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [Φ, ContinuousLinearMap.comp_apply, h1, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, h2]
    rfl
  have hs := (hasSum_actM_pow_div_factorial hσ hW hZ x.2).map Φ Φ.continuous
  have hs' := hasSum_actM_pow_div_factorial hσ hW' hZ (φ x).2
  rw [Function.comp_def] at hs
  simp only [map_smul] at hs
  have e3 : ∀ m : ℕ, Φ ((((actM (smE ε σ) Z) ^ m) x : smD ε σ) : H) =
      ((((actM (smE ε σ) Z) ^ m) (φ x) : smD ε σ) : H) := by
    intro m
    have := hΦ ⟨_, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 m⟩
    rw [this, intertwiner_actM_pow_comm hW hW' φ hφ hZ m x]
  simp only [e3] at hs
  rw [← hxy, hΦ] at hs
  exact hs.unique hs'

end

end CompanionTheory.D.gk.HC
