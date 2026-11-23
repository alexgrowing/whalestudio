import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let S : Sm E a → Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := fun θ =>
    { carrier := {k | finRep E a k θ = θ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => by
    have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
      LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    rw [← e, hk']
  exact Subgroup.isOpen_mono hle h

private theorem left_lie (X : Lie E a) (φ : Sm E a) (x : GA E a) (h : ∀ g, φ.1 (x * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (x * g) = (lie E a X φ).1 g := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have h1 := hasDerivAt_curve φ (x * g) c X c0 cder
  have h2 := hasDerivAt_curve φ g c X c0 cder
  simp only [mul_assoc, h] at h1
  exact h1.unique h2

theorem UpperTheory.V.Lit.Geo.Pf.invLie :
    UpperTheory.V.Lit.Geo.Pf.InvLie := by
  intro E _ _ _ a φ h
  exact ⟨⟨ContAut.continuous_of_isOpen_stab E a φ h.level, h.left, h.centre⟩, fun X =>
    ⟨fun γ => left_lie X φ _ (h.left γ), fun t => left_lie X φ _ (h.centre t), level_lie X φ h.level⟩⟩

end
