import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEvaluationOfMemAdjoin

noncomputable section

namespace GlobalTheory.CompanionTheory.InvPickKP

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.RealMult (Pair2 Inv2 ev2)

variable {n : ℕ}

def toKP : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p =>
    if p.1 then (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, p.2) + FreeAlgebra.ι ℂ (true, p.2))
    else (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, p.2) - FreeAlgebra.ι ℂ (true, p.2))

theorem evalCartan_toCartan {V : Type} [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : evKP E1 E2 (toKP a) = ev2 E1 E2 a := by
  have eK : ∀ a b, evKP E1 E2 (FreeAlgebra.ι ℂ (false, a, b)) = E1 a b + E2 a b := fun a b => by
    simp [evKP, kA]
  have eP : ∀ a b, evKP E1 E2 (FreeAlgebra.ι ℂ (true, a, b)) = E1 a b - E2 a b := fun a b => by
    simp [evKP, pA]
  have h : (evKP E1 E2).comp toKP = ev2 E1 E2 := by
    apply FreeAlgebra.hom_ext
    funext ⟨s, a, b⟩
    show evKP E1 E2 (toKP (FreeAlgebra.ι ℂ (s, a, b))) = ev2 E1 E2 (FreeAlgebra.ι ℂ (s, a, b))
    cases s
    · have t : toKP (FreeAlgebra.ι ℂ (false, a, b)) =
          (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, a, b) - FreeAlgebra.ι ℂ (true, a, b)) := by simp [toKP]
      have e : ev2 E1 E2 (FreeAlgebra.ι ℂ (false, a, b)) = E2 a b := by simp [ev2]
      rw [t, e, map_smul, map_sub, eK, eP]
      module
    · have t : toKP (FreeAlgebra.ι ℂ (true, a, b)) =
          (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, a, b) + FreeAlgebra.ι ℂ (true, a, b)) := by simp [toKP]
      have e : ev2 E1 E2 (FreeAlgebra.ι ℂ (true, a, b)) = E1 a b := by simp [ev2]
      rw [t, e, map_smul, map_add, eK, eP]
      module
  exact DFunLike.congr_fun h a

theorem invKP_toKP {a : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Inv2 a) : InvKP n (toKP a) := by
  intro V _ _ E1 E2 hE c d
  rw [evalCartan_toCartan]
  exact h V E1 E2 ⟨hE.1, hE.2.1, hE.2.2⟩ c d

theorem invPick : InvPick := by
  intro n lam lev V _ _ E1 E2 hA μ v w hv hw hv0 hx
  obtain ⟨a, ha, hav⟩ := GlobalTheory.CompanionTheory.RealMult.Lift.liftInv n V E1 E2 ⟨hA.gl1, hA.gl2, hA.comm⟩ hA.unitK hA.locFin
    μ v w hv0 hv hw hx
  exact ⟨toKP a, invKP_toKP ha, by rw [evalCartan_toCartan, hav]⟩

end GlobalTheory.CompanionTheory.InvPickKP
