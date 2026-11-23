import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem continuous_lie_of_level {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) : Continuous (lie E a X φ).1 := by
  refine ContAut.continuous_of_isOpen_stab E a _ ?_
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

open scoped GlobalTheory.CuspRep.CuspidalL2GL in
theorem UpperTheory.V.Lit.Bor.skew_lie_action_L2 :
    UpperTheory.V.Lit.Bor.SkewLieActionL2 := by
  intro E _ _ _ a μ _ X φ ψ hφ hψ h1 h2 h3 h4
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have g0 : infGL E a (c 0) = 1 := by rw [c0, map_one]
  have key : ∀ (θ : Sm E a), IsOpen {k | act (.fin k) θ = θ} →
      ∀ (p : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ θ.1)
        (q : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X θ).1),
      HasDerivAt (fun s => GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) p.toL2) q.toL2 0 :=
    fun θ hθ p q => UpperTheory.V.Lit.Bor.derivative_right_translate_L2 (GA E a) _ μ θ.1 _ p q (fun s => infGL E a (c s))
      (continuous_lie_of_level X θ hθ) ccont g0 (fun s t => by rw [cadd, map_mul])
      (fun g => hasDerivAt_curve θ g c X c0 cder)
  have d := (key φ hφ h1 h3).inner ℂ (key ψ hψ h2 h4)
  have hc : (fun s : ℝ => inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h1.toL2)
      (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h2.toL2)) = fun _ => inner ℂ h1.toL2 h2.toL2 :=
    funext fun s => (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s))).toLinearMap
      (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
  rw [hc] at d
  have h := d.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [g0, map_one, ContinuousLinearMap.one_apply] at h
  exact (add_comm _ _).trans h
