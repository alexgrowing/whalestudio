import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.TeichNotLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlOfOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.SplitIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.PotQOf

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Z.Win.A4

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}

def SafeRA (l : ℕ) [Fact l.Prime] (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  (l ∣ M ∧ UnlAll r) ∨ ∀ i j, m i ≠ m j + 1

def SafePA (l : ℕ) [Fact l.Prime] (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  (l ∣ M ∧ PotAll r) ∨ ∀ i j, m i ≠ m j + 1

example : type_of% @Keep.SafeU := @SafeRA
example : type_of% @Keep.SafeP := @SafePA

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem safeUGap' (_ : Level l M m r) (h : ∀ i j, m i ≠ m j + 1) : SafeRA l M m r := Or.inr h

theorem safeRes' (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] (h : SafePA l M m r) :
    SafePA l M m (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
  h.imp_left fun ⟨h1, h2⟩ => ⟨h1, fun w hw => (((flagLaws F Ω l n r).2.2.2 K).2.2 w hw).1 (h2 _ (by
    change algebraMap (𝓞 F) (𝓞 K) (l : 𝓞 F) ∈ w.asIdeal
    rwa [map_natCast]))⟩

theorem unlAll_of (h : Th.Unl l M m r) : UnlAll r := fun v hv => by
  obtain ⟨A, hA, κ, ⟨-, -, hf, -⟩, hu⟩ := h v hv
  exact unlOfOne F Ω l n r v A hA κ hf hu
end

theorem safe4' {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good)
    (N : ℕ) (hN : 1 ≤ N) (h1 : Af.KillsMu N D.ψ) (h2 : Af.KillsMu N D.ξ) (h3 : Af.KillsMu N D.om) (r : G ℚ Ω →* M4 (PadicAlgCl l))
    (hr : D.EPt r) : SafeRA l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits :=
  Or.inl ⟨Lev.teichDvd D hD N hN h3, unlAll_of (Th.spUnl D hD N hN h1 h2 h3 r hr)⟩

end UpperTheory.V.Z.Win.A4
