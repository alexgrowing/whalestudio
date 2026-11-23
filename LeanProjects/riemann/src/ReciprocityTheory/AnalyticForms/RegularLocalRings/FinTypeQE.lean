import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

universe u

namespace ReciprocityTheory.AnForm.R.FinalTheorems

def FinTypeQE : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], QERing A

end ReciprocityTheory.AnForm.R.FinalTheorems
