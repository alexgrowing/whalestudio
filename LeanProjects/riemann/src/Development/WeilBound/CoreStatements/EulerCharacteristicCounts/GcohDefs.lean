import Formalism.GaloisCohomology.LocalTateDualityK
import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

def SgcRep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M), ContAction rho → ∃ (A : Rep.{0} (ULift.{0} ℤ) G) (_ : IsDiscreteRep A) (e : M ≃+ A.V), ∀ g m, e (rho g m) = A.ρ g (e m)

def Sgc0 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e0 : ↥(H0 rho) ≃+ cohomology A 0, ∀ (m : ↥(H0 rho)) (x : cocycles A 0), (∀ s, cochainOf A (cocycleι A 0 x) s = e m.1) → e0 m = cohomologyπ A 0 x

def Sgc1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e1 : H1 rho ≃+ cohomology A 1, (∀ z : ↥(Z1 rho), ∃ x : cocycles A 1, ∀ s, cochainOf A (cocycleι A 1 x) s = e (z.1 (s 0))) ∧ ∀ (z : ↥(Z1 rho)) (x : cocycles A 1), (∀ s, cochainOf A (cocycleι A 1 x) s = e (z.1 (s 0))) → e1 (Submodule.Quotient.mk z) = cohomologyπ A 1 x

def Sgc2 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e2 : H2 rho ≃+ cohomology A 2, (∀ z : ↥(Z2 rho), ∃ x : cocycles A 2, ∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (s 0, s 1))) ∧ ∀ (z : ↥(Z2 rho)) (x : cocycles A 2), (∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (s 0, s 1))) → e2 (Submodule.Quotient.mk z) = cohomologyπ A 2 x

def Sgcn : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∀ n : ℕ, Nonempty (Hn rho n ≃+ cohomology A n)

def SgcField : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → IsSepClosure ↥K (PadicAlgCl l) ∧ ∃ (_ : ValuativeRel ↥K) (t : TopologicalSpace ↥K), @IsNonarchimedeanLocalField ↥K _ _ t ∧ ∀ m : ℕ, Nat.card (𝒪[↥K] ⧸ Ideal.span {((l ^ m : ℕ) : 𝒪[↥K])}) = (l ^ m) ^ Module.finrank ℚ_[l] ↥K

def SgcMu : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : ℕ), ∃ e : ZMod (l ^ r) ≃+ (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).V, ∀ (g : Formalism.GaloisCohomology.GK l K) (m : ZMod (l ^ r)), e ((Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)) * m) = (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g (e m)

end PositivityTheory.LocalTateOrthogonality.Gcoh
