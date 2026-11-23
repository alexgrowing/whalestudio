import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cxGrp_comp {T : Type} [Fintype T] {a : ℕ} {Φ : (Fin a → Fin a → T → ℂ) → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (g h : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (g.val * Matrix.of x * h.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ (fun x : Fin a → Fin a → T → ℂ => fun i j => (g.val * Matrix.of x * h.val) i j) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  exact (g.isUnit.mul hx').mul h.isUnit

theorem UpperTheory.V.Lit.Bor.cxGrp :
    UpperTheory.V.Lit.Bor.CxGrp := by
  intro E _ _ _ a Ξ
  choose Φ hΦ hv using fun k l => UpperTheory.V.Lit.Bor.holExt E a _ (Ξ.reg k l)
  have hv' : ∀ k l (y : GL (Fin a) (Cinf E)),
      Φ k l (fun i j => (GeneralLinearGroup.map (emb E) y).val i j) = Ξ.mat y k l := fun k l y => hv k l y
  have h1 : ∀ k l (y : GL (Fin a) (Cinf E)) (g : GL (Fin a) ((E →+* ℂ) → ℂ)),
      Φ k l (fun i j => (GeneralLinearGroup.map (emb E) y * g).val i j) =
        ∑ m, Ξ.mat y k m * Φ m l (fun i j => g.val i j) := by
    intro k l y g
    have key := UpperTheory.V.Lit.Bor.holId E a (fun x =>
      Φ k l (fun i j => ((GeneralLinearGroup.map (emb E) y).val * Matrix.of x *
        (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val) i j) - ∑ m, Ξ.mat y k m * Φ m l x)
      ((cxGrp_comp (hΦ k l) _ _).sub
        (DifferentiableOn.fun_sum fun m _ => (hΦ m l).const_mul _)) (fun z => by
          have e := hv' k l (y * z)
          rw [map_mul, map_mul, Matrix.mul_apply] at e
          simp only [hv]
          rw [← e, sub_eq_zero, Units.val_one, mul_one]
          rfl) g
    rw [sub_eq_zero, Units.val_one, mul_one] at key
    exact key
  have h2 : ∀ k l (g h : GL (Fin a) ((E →+* ℂ) → ℂ)),
      Φ k l (fun i j => (g * h).val i j) =
        ∑ m, Φ k m (fun i j => g.val i j) * Φ m l (fun i j => h.val i j) := by
    intro k l g h
    have key := UpperTheory.V.Lit.Bor.holId E a (fun x =>
      Φ k l (fun i j => ((1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val * Matrix.of x * h.val) i j) -
        ∑ m, Φ k m x * Φ m l (fun i j => h.val i j))
      ((cxGrp_comp (hΦ k l) _ _).sub
        (DifferentiableOn.fun_sum fun m _ => (hΦ k m).mul_const _)) (fun z => by
          have e := h1 k l z h
          simp only [hv]
          rw [← e, sub_eq_zero, Units.val_one, one_mul]
          rfl) g
    rw [sub_eq_zero, Units.val_one, one_mul] at key
    exact key
  refine ⟨{ toFun := fun g => Matrix.of fun k l => Φ k l (fun i j => g.val i j)
            map_one' := ?_
            map_mul' := fun g h => ?_ }, Φ, hΦ, fun _ _ _ => rfl, fun y => ?_⟩
  · ext k l
    have e := hv' k l 1
    rw [map_one, map_one] at e
    exact e
  · ext k l
    rw [Matrix.mul_apply]
    exact h2 k l g h
  · ext k l
    exact hv' k l y
