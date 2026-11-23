import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat

open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

theorem solve_spec {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E) (e : E)
    (he : e ∈ LinearMap.range f) : f (solve f e) = e := by
  have hex : ∃ y, f y = e := he
  unfold solve
  rw [dif_pos hex]
  exact hex.choose_spec

theorem lin_single {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) (k : Fin n) :
    lin v (Pi.single k 1) = v k := by
  simp [lin, Fintype.linearCombination_apply_single]

theorem ratMuOfRowTest : RatMuOfRowTest := by
  intro K _ _ _ Bs A X fc cr b hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall, -⟩ := hH2
  intro t i k
  have hmem : X.iC cr b t (Pi.single k 1) ∈ LinearMap.range (X.iC cr b Bs.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat Bs.v0.embedding ψ hψ (X.iC cr b Bs.μ0) hinj0
    (fun j l => by rw [CxData.iC, lin_single]; exact hr _ _ _)
    (solve (X.iC cr b Bs.μ0) (X.iC cr b t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, by simpa [CxData.rowMatC, relMat] using ha⟩

end Formalism.IndefR.Rat
