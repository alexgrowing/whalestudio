import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SupTrace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FockWeightWedgeLowerModes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CoordSpan
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open GlobalTheory.HCChar (dsChar)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEG

open GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def OmDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, ev k Q * ev k (OmP ε).det = physDet ε k

def ClassFn : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε), physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
      trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k)

def GaInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ Λ m : Fin n → ℤ, gaW ε lam = (fun a => (Λ a : ℝ)) ∧ (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) ∧
      (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) ∧
      ∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)

def ToKType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) →
    ∃ T₀ : S7.KType ε γ, ∀ k : S7.KG ε, ReciprocityTheory.ChartRestriction.TR.Weyl.kChar T₀ k = trK T (S7.toMK k)

def VdmSplit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ),
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) = ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t * ((-1) ^ sDeg ε *
      ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2))

def PhysTor : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ),
    physDet ε (Matrix.diagonal (tor θ)) = (-1) ^ (pOf ε * qOf ε) * (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2)) *
      ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) ∧
    physDet ε (Matrix.diagonal (tor θ)) * conj (physDet ε (Matrix.diagonal (tor θ))) = (dMode ε θ : ℂ)

def NumShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ) (t : Fin n → ℂ), (∀ a, t a ≠ 0) →
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a))

def RangeFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∀ d : ℕ,
    ∃ L : Submodule ℂ (smD ε σ), FiniteDimensional ℂ L ∧
      (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD (isDerivedOn_smE hσ) hk x ∈ L) ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∀ u : H,
        ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ L.map (smD ε σ).subtype

def BuildY : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (c : ℂ), (∀ v : D, casimir E v = c • v) →
    ∀ L : Submodule ℂ D, FiniteDimensional ℂ L → (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    ∃ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y ∧ tensFock L ⊓ physicalSubspace ε ≤ Y ∧
      Y ≤ physicalSubspace ε ∧ (∀ y ∈ Y, dD ε E y ∈ Y) ∧ (∀ y ∈ Y, gradT y ∈ Y) ∧
      ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y

def StrKer : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Y : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Y], (∀ y ∈ Y, dD ε E y ∈ Y) → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y),
    ∃ (Z : Submodule ℂ (TensorProduct ℂ D (Fock n))) (_ : FiniteDimensional ℂ Z)
      (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z) (Γ : TSub Z →ₗ[ℂ] TSub Z),
      Z ≤ Y ∧ (∀ y ∈ Z, dD ε E y = 0) ∧ ∀ (k : Mat n) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
          LinearMap.trace ℂ (TSub Z) (Γ ∘ₗ (tOp hD hZK k : TSub Z →ₗ[ℂ] TSub Z))

def StrIdx : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ d : ℕ,
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (L : Submodule ℂ D) [FiniteDimensional ℂ L],
    (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    (∀ Q : Poly n, Q.totalDegree ≤ d → ∀ u : H,
      ∫ k : KG ε, ev (toMK k) Q • σ (toMK k) u ∂(muK ε) ∈ L.map D.subtype) →
    ∀ (Y : Submodule ℂ (TensorProduct ℂ D (Fock n))) [FiniteDimensional ℂ Y], tensFock L ⊓ physicalSubspace ε ≤ Y →
      Y ≤ physicalSubspace ε → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y) (B : H →L[ℂ] H),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) →
      ∃ hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L.map D.subtype,
        LinearMap.trace ℂ (L.map D.subtype) ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) =
          ∫ k : KG ε, ev (toMK k) P * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (k := toMK k) k.2).restrict
            (fun y hy => hG _ (hK _ k.2 y hy))) ∂(muK ε)

def HWVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Z : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Z] (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z)
      (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T → ∀ Φ : W →ₗ[ℂ] TSub Z, Φ ≠ 0 →
      (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = tOp hD hZK k (Φ v)) →
      ∃ z ∈ Z, z ≠ 0 ∧ IsKHWVec ε (diagE ε (eT E) cpT cmT) γ z

def CoordFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))), FiniteDimensional ℂ Z →
    IsKStableSub ε (diagE ε (eT E) cpT cmT) Z →
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z)

def CasCoord : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E → ∀ z : TensorProduct ℂ M (Fock n),
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z → dD ε E z = 0 →
    ∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z

def AlgDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Gap3 ε lam →
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
    IsGlRep E → IsInfUnitary ε E → ∀ z : TensorProduct ℂ M (Fock n), z ≠ 0 → z ∈ physicalSubspace ε →
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z →
    (∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z) →
    ∀ S : Submodule ℂ M, FiniteDimensional ℂ S → IsKStableSub ε E S → (∀ s, tco s z ∈ S) →
    ∃ V : Submodule ℂ M, IsKIrrHW ε E (lowK ε lam) V ∧ V ≠ ⊥ ∧ ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v

def CptCase : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), pOf ε = 0 ∨ qOf ε = 0 →
    (∀ k, physDet ε k = 1) ∧ sDeg ε = 0 ∧
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
      FiniteDimensional ℂ X ∧ IsKIrr ε (gaW ε lam) D

def GapNum : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ),
    (∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j) →
    Formalism.QuantumDeterminants.IsHCParam (fun a => (lam a : ℝ)) ∧ StdGap ε (fun a => (lam a : ℝ)) ∧ Gap3 ε (fun a => (lam a : ℝ)) ∧
      ∃ h : ℝ, GapAtLeast ε (fun a => (lam a : ℝ)) h ∧ thrStar ε < h

def TorusId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (Λ m : Fin n → ℤ), (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) →
    (∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)) →
    ∀ θ : Fin n → ℝ, Function.Injective (tor θ) → ∀ x : ℂ,
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x = ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) (tor θ) →
      (-1) ^ sDeg ε * x = dsChar ε lam θ * physDet ε (Matrix.diagonal (tor θ))

end GlobalTheory.PsCo.PcEG
