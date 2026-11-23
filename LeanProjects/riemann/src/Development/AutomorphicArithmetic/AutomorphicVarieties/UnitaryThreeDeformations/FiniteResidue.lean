import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

noncomputable section

open IsLocalRing UpperTheory.V.HV

namespace UpperTheory.V.UnitaryThreeInertia

def Frame.shaLen {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type}
    (F : Frame O G Γ ι) [TopologicalSpace Γ] (a : O) : ℕ∞ := Module.length O (F.ShaO a)

instance Coef.isLocalRing {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalRing c.O := c.dvr.toIsLocalRing

instance Coef.complete {l : ℕ} [Fact l.Prime] (c : Coef l) : IsAdicComplete (maximalIdeal c.O) c.O :=
  (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1

instance Coef.finite_residue {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

class CFin (O : Type) [CommRing O] [IsLocalRing O] : Prop where
  complete : IsAdicComplete (maximalIdeal O) O
  fin : Finite (ResidueField O)

attribute [instance] CFin.complete CFin.fin

end UpperTheory.V.UnitaryThreeInertia

end
