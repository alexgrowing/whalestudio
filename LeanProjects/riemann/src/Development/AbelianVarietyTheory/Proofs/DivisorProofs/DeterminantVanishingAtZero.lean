import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt

namespace GlobalTheory.DetEqv

theorem vanishAt_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.DetEqv.VanishAt k 0 := by
  intro Y _ m hm μ hμ L hL
  have hne : μ ≠ 1 := by simpa using hμ 0
  obtain ⟨a, ha⟩ : ∃ a : kˣ, μ a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (MonoidHom.ext h)
  let i : Fin m := ⟨0, hm⟩
  let d : Matrix (Fin m) (Fin m) k := Matrix.diagonal (Function.update (fun _ => (1 : k)) i (a : k))
  have hd : d.det = (a : k) := by
    simp [d, Matrix.det_diagonal, Finset.prod_update_of_mem]
  let g : GL (Fin m) k := Matrix.GeneralLinearGroup.mkOfDetNeZero d (by rw [hd]; exact a.ne_zero)
  have hg : Matrix.GeneralLinearGroup.det g = a := by
    ext
    simp [g, hd]
  ext Φ
  have h := hL g Φ Φ (fun y X => by
    rw [show X * (g : Matrix (Fin m) (Fin m) k) = X from Matrix.ext fun r _ => Fin.elim0 r])
  rw [hg] at h
  have ha' : (μ a : ℂ) ≠ 1 := fun h1 => ha (Units.ext h1)
  have h2 : (1 - (μ a : ℂ)) * L Φ = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm ha'
  · simpa using h3

end GlobalTheory.DetEqv
