import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.UnitaryGroupLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EqZeroOfMemMult

noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain Topology Matrix Filter Formalism.HermitianLatticeCounting.LatticeSumBounds

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

def IntM {m : ℕ} (X : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i k, X i k ∈ Formalism.MainNotions.UnitaryGroupLocal.oE v

def SA {m : ℕ} (S : Matrix (Fin m) (Fin m) E) : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F) :=
  S.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (x : E ⊗[F] v.adicCompletion F) :
    PI.UnitaryApproxDefs.sigR σ _ (PI.UnitaryApproxDefs.sigR σ _ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e r => simp [PI.UnitaryApproxDefs.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

def starO (hσ : ∀ e, σ (σ e) = e) : StarRing (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v) where
  star x := ⟨PI.UnitaryApproxDefs.sigR σ _ x, Formalism.MainNotions.UnitaryGroupLocal.sigR_mem v σ x.2⟩
  star_involutive x := Subtype.ext (sigR_sigR v σ hσ x)
  star_mul x y := Subtype.ext (by
    show PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
        ((x : E ⊗[F] v.adicCompletion F) * (y : E ⊗[F] v.adicCompletion F)) =
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (y : E ⊗[F] v.adicCompletion F) *
        PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (x : E ⊗[F] v.adicCompletion F)
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add _ _ _)

def cO (ϖ : v.adicCompletion F) (hϖ : ϖ ∈ v.adicCompletionIntegers F) : Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v :=
  ⟨(1 : E) ⊗ₜ[F] ϖ, Subring.subset_closure (Or.inr ⟨⟨ϖ, hϖ⟩, rfl⟩)⟩

variable {m : ℕ}

def up : Matrix (Fin m) (Fin m) (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v) →+*
    Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F) :=
  (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v).subtype.mapMatrix

def down (X : Matrix (Fin m) (Fin m) (E ⊗[F] v.adicCompletion F)) (hX : IntM v X) :
    Matrix (Fin m) (Fin m) (Formalism.MainNotions.UnitaryGroupLocal.oE (E := E) v) := fun i k => ⟨X i k, hX i k⟩

end Formalism.L2.SG.Pf.Lem3Mass
