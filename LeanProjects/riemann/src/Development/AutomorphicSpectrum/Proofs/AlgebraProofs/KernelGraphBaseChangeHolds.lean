import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelLatticeBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem kernel_graph_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) :=
  @PositivityTheory.Xgn.kernel_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num
