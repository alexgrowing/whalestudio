import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.Pst

namespace UpperTheory.Lit.Drps

variable {l : ℕ} [Fact l.Prime]

section Coord

variable {S : Type} [CommRing S] [Algebra ℚ_[l] S] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {d : ℕ} (b : Basis (Fin d) ℚ_[l] V)

def cS (i : Fin d) : V ⊗[ℚ_[l]] S →ₗ[ℚ_[l]] S :=
  (TensorProduct.lid ℚ_[l] S).toLinearMap ∘ₗ (b.coord i).rTensor S

@[simp] theorem cS_tmul (i : Fin d) (v : V) (s : S) : cS b i (v ⊗ₜ s) = b.coord i v • s := by
  simp [cS]

end Coord

section Periods

variable {G : Type} [Group G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    {d : ℕ} (b : Basis (Fin d) ℚ_[l] V) (ρ : Representation ℚ_[l] G V)

end Periods

section Pst

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
  (ρ : Representation ℚ_[l] ↥(GK K) V)

end Pst

end UpperTheory.Lit.Drps
