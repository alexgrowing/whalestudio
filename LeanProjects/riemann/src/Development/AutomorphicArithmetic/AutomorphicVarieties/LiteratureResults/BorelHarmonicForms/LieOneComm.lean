import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_fin (X : Lie E a) (k : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin k) (lie E a X φ) = lie E a X (act (.fin k) φ) :=
  (LinearMap.congr_fun (lie_rt_fin X k) φ).symm

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let ρ : GL (Fin a) (Af E) →* Module.End ℂ (Sm E a) := (rt E a).comp (finGL E a)
  let S : Sm E a → Subgroup (GL (Fin a) (Af E)) := fun ψ =>
    { carrier := {k | ρ k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change ρ (x * y) ψ = ψ
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        change ρ x⁻¹ ψ = ψ
        have hx' : ρ x ψ = ψ := hx
        conv_lhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => (lie_fin X k φ).trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem isSq_lie (r : ℝ) (X : Lie E a) (φ : Sm E a) (h : IsSq r φ) : IsSq r (lie E a X φ) where
  left γ g := lie_left X φ _ g (h.left γ)
  level := level_lie X φ h.level
  one := by rw [lie_one_comm, h.one, map_smul]
  sq l := by
    have := h.sq (l ++ [X])
    rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply] at this

end

theorem UpperTheory.V.Lit.Bor.sqLie :
    UpperTheory.V.Lit.Bor.SqLie := by
  intro E _ _ _ a r
  refine ⟨isSq_lie r, fun X φ hφ => ?_⟩
  have h : sqSub E a r ≤ (sqSub E a r).comap (lie E a X) :=
    Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_lie r X ψ hψ)
  exact h hφ
