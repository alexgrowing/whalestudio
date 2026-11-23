import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison.Pb

namespace CrystallineSemistableComparison.Om.Glob

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def formCos {ι : Type} (U : ι → X.Opens) (a : ℕ) : Cos.{0} K where
  X n := ∀ i : Fin (n + 1) → ι, OmU q (capO U i) a
  δ n k := LinearMap.pi fun i => (formRes q (capO_comp U i k.succAbove) a).comp (LinearMap.proj (i ∘ k.succAbove))
  rel n j i x := by
    funext t
    have e : (t ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove = (t ∘ j.succAbove) ∘ i.succAbove :=
      funext fun k => congrArg t (Fin.succAbove_succAbove_succAbove_predAbove j i k)
    have key : ∀ (b b' : Fin (n + 1) → ι) (hb : b = b') (h : capO U t ≤ capO U b) (h' : capO U t ≤ capO U b'),
        formRes q h a (x b) = formRes q h' a (x b') := by
      intro b b' hb h h'
      subst hb
      rfl
    change formRes q _ a (formRes q _ a (x _)) = formRes q _ a (formRes q _ a (x _))
    rw [formRes_formRes, formRes_formRes]
    exact key _ _ e _ _

abbrev KC (U : Cov q) (a : ℕ) : ObjectProperty (Thick (smFun X q)) := KS q (a + 1) (Set.range U.U)

abbrev Fk (U : Cov q) (a : ℕ) : (KC q U a).FullSubcategory ⥤ ModuleCat.{0} K := (KC q U a).ι ⋙ HT.grT (smFun X q) a

def Vk (U : Cov q) (a : ℕ) (α : U.ι) : ObjectProperty (KC q U a).FullSubcategory :=
  fun T => InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U.U α) T.obj

end

end CrystallineSemistableComparison.Om.Glob
