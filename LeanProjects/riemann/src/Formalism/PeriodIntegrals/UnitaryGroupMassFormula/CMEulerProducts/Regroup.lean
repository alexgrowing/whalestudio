import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem euler_product_regroup : StepRegroup := by
  intro F E _ _ _ _ _ _ M hm hf
  classical
  let f : {P : Ideal (𝓞 E) // P.IsMaximal} → {v : Ideal (𝓞 F) // v.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 E)), by
      have := P.2
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.1⟩
  let e := Equiv.sigmaFiberEquiv f
  have h1 : HasProd (fun x => eulerFac E M (e x).1) (lValEta E M) :=
    (e.hasProd_iff (f := fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => eulerFac E M P.1)).mpr
      hm.hasProd
  have hfib : ∀ v : {v : Ideal (𝓞 F) // v.IsMaximal},
      HasProd (fun c : {x // f x = v} => eulerFac E M (e ⟨v, c⟩).1) (eulerF F E M v.1) := by
    intro v
    let ev : {x // f x = v} ≃
        {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.1} :=
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, Subtype.ext c.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (ev.hasProd_iff (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
      P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.1} => eulerFac E M c.1)).mpr (hf v.1 v.2)
  have h2 : HasProd (fun v : {v : Ideal (𝓞 F) // v.IsMaximal} => eulerF F E M v.1) (lValEta E M) :=
    h1.sigma hfib
  exact h2.tprod_eq

end CMEul
