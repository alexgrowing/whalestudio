import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.UnlAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def NoLink (x : GL (Fin n) (Qbar l)) (Q : ℕ) : Prop :=
  ∀ α β : Qbar l, (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α → (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β →
    ∀ k : ℕ, 1 ≤ k → α ^ k ≠ ((Q : Qbar l) * β) ^ k

def UnlinkAt (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) : Prop :=
  ∃ (s : G F Ω) (j : ℕ), 1 ≤ j ∧ IsFrob A (normV w ^ j) s ∧ NoLink (r s) (normV w ^ j)

def Unlinked (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite → UnlinkAt r w A

def Wit [IsCMField F] (_ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := Unlinked r

omit [NumberField F] in

def WitQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

def AutPol [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π

def AutCsd0 [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π

omit [NumberField F] in

def IsAutomorphicOverImagQuad (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π

def IsAutCsdN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → Wit ι r)

omit [NumberField F] in

def IsAutQN (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      (∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π) ∧
        Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem mkCsd [IsCMField F] (h : AutCsd0 ι r) (_ : Continuous r → Wit ι r) : IsAutCsd ι r := h
theorem mkCsd' [IsCMField F] (h : AutCsd0 ι r) (u : Continuous r → Wit ι r) : IsAutCsdN ι r := ⟨h, u⟩
theorem csd0 [IsCMField F] (h : IsAutCsd ι r) : AutCsd0 ι r := h
theorem csd0' [IsCMField F] (h : IsAutCsdN ι r) : AutCsd0 ι r := h.1
omit [NumberField F] in
theorem automorphicQ_of_witness (h : IsAutQ ι r) : IsAutomorphicOverImagQuad ι r := h
omit [NumberField F] in
theorem autQ0' (h : IsAutQN ι r) : IsAutomorphicOverImagQuad ι r := fun hc K _ _ _ _ _ _ h2 hi => (h hc K h2 hi).1
omit [NumberField F] in
theorem mkQ (h : IsAutomorphicOverImagQuad ι r) (_ : Continuous r → WitQ ι r) : IsAutQ ι r := h
omit [NumberField F] in
theorem mkQ' (h : IsAutomorphicOverImagQuad ι r) (u : Continuous r → WitQ ι r) : IsAutQN ι r :=
  fun hc K _ _ _ _ _ _ h2 hi => ⟨h hc K h2 hi, u hc K h2 hi⟩

theorem UnlinkAt.unlAt {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : UnlinkAt r w A) : UnlAt ι r w A := by
  obtain ⟨s, j, hj, hs, hn⟩ := h
  refine ⟨s, j, hj, hs, fun α hα hβ => ?_⟩
  have back : ∀ z : ℂ, ((r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot z →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot (ι.symm z) := fun z hz => by
    rw [← ι.apply_symm_apply z] at hz
    exact (Polynomial.isRoot_map_iff (f := ι.toRingHom) ι.injective).1 hz
  refine hn _ _ (back _ hβ) (back _ hα) 1 le_rfl ?_
  simp
end Conv

end UpperTheory.GalN.V
