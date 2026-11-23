import Formalism.GaloisCohomology.Statement
import Formalism.GaloisCohomology.StatementLoc

noncomputable section

open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace Formalism.GaloisCohomology

def SelAllLeInf : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) (R : Type) [CommRing R] (M : Type)
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M), ContAction rhoS →
  ∀ (A : Places F Ω) (L : ∀ v, Submodule R (H1 ((rhoS.comp (toGS Ω S)).comp (Dec (F := F) (A.1 v)).subtype))),
  (∀ v ∉ S, L v ≤ unrAt (rhoS.comp (toGS Ω S)) (A.1 v)) →
    SelAll (rhoS.comp (toGS Ω S)) A L ≤ LinearMap.range (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S))

def SelAllLen : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) (R : Type) [CommRing R] (M : Type)
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M), ContAction rhoS →
  ∀ (A : Places F Ω) (L : ∀ v, Submodule R (H1 ((rhoS.comp (toGS Ω S)).comp (Dec (F := F) (A.1 v)).subtype))),
  (∀ v ∉ S, L v ≤ unrAt (rhoS.comp (toGS Ω S)) (A.1 v)) →
    Module.length R (SelAll (rhoS.comp (toGS Ω S)) A L) =
      Module.length R ((SelAll (rhoS.comp (toGS Ω S)) A L).comap
        (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)))

section Local

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

def cycK (r : ℕ) : GK l K →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
    ((cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (GK l K) (PadicAlgCl l)))

def CycKSpec : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (r : ℕ) (σ : GK l K) (ζ : PadicAlgCl l), ζ ^ (l ^ r) = 1 →
    σ ζ = ζ ^ ((cycK l K r σ : ZMod (l ^ r)).val)

def LocalFinitenessK : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)

def LocalTateDualityK : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ∀ hrho : ContAction rho,
    Nonempty (H2 (charRep (cycK l K r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycK l K r) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycK l K r) rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycK l K r) rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 (cycK l K r) rho (MonoidHom.id _))

def LocalEulerCharK : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho →
    Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ Module.finrank ℚ_[l] K

end Local

end Formalism.GaloisCohomology
