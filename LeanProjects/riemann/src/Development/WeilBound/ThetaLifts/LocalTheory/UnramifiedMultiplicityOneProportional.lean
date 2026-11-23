import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def UnramifiedMultiplicityOneProportional : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' a₁ a₁' : ℕ) (G : Geo σ a a') (G₁ : Geo σ a₁ a₁') (X : Chars F E) om om' om₁ om₁' R Rf R₁ Rf₁
    (H' : Plane E (a + a') (a₁ + a₁')) (i₀ i₁ : ℕ) χ r, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    StepTy G G₁ X χ r → H'.IsAdapted σ B G.W G₁.W i₀ i₁ → ∀ v ∉ X.T, ∀ lam lam', IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam → IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam' →
      ∀ c : ℂ, lam' (Rf.p v (G.M.vac v)) = c • lam (Rf.p v (G.M.vac v)) → lam' = c • lam

end PositivityTheory.ThKG.Loc

end
