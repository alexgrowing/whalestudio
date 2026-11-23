import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.UnitaryThreeHeightBounds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain

namespace Formalism.MainNotions.V.Pf.V3.LG

open Formalism.MainNotions.UnitaryThreeHeightBounds

variable {D : D7} (V : VData D)

def LocGlob3Pt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    UnitaryThreeData V l e χ K → ∀ g1 : GQ, IsNormElt V l e χ K g1 → UnitaryThreeFiniteness V l e χ K g1 →
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) →
    Continuous (V.rho3 ξ) → IsCSDOne (VData.toRecRep (V.rho3 ξ)) →
    ∀ M : ℕ, 0 < M → condV D ∣ M → OrdFixAbove (VData.toRecRep (V.rho3 ξ)) ![(e : ℤ), 0, -(e : ℤ)] M →
    Ram3 V l K (V.rho3 ξ) M →
    ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π → ∀ (ι : QbarL l ≃+* ℂ) (j : ℤ),
    (∀ (τ : K →+* ℂ) (i : Fin 3), (V.spec K 3).wt π τ i = -(![(e : ℤ), 0, -(e : ℤ)] : Fin 3 → ℤ) i.rev - j) →
    IsRiAt V ι π (VData.toRecRep (twistRep (V.rho3 ξ) (((epsL l).comp K.fixingSubgroup.subtype) ^ j))) →
    (V.spec K 3).level π M

def LocGlob3PtS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    UnitaryThreeData V l e χ K → ∀ g1 : GQ, IsNormElt V l e χ K g1 → UnitaryThreeFiniteness V l e χ K g1 →
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) →
    ∀ M : ℕ, 0 < M → condV D ∣ M →
    ∀ (π : (V.spec K 3).Rep) (ι : QbarL l ≃+* ℂ) (j : ℤ),
    (∀ (τ : K →+* ℂ) (i : Fin 3), (V.spec K 3).wt π τ i = -(![(e : ℤ), 0, -(e : ℤ)] : Fin 3 → ℤ) i.rev - j) →
    IsRiAt V ι π (VData.toRecRep (twistRep (V.rho3 ξ) (((epsL l).comp K.fixingSubgroup.subtype) ^ j))) →
    (V.spec K 3).level π M

variable {V}

variable (D V)

def lit6Pt : Prop := Purity V ∧ LocGlob3Pt V ∧ LocGlobWt3 V ∧ LocGlob2G V

def LitGeoPt : Prop :=
  lit0 D V ∧ lit1 D V ∧ lit2 D V ∧ lit3 D V ∧ lit4 D V ∧ lit5 D V ∧ lit6Pt D V ∧ lit9 D V ∧ LitB D V ∧ DeJongGenericFibrePoints D V

def LitXPt (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) : Prop :=
  LitGeoPt D V ∧ ClozelAutR V ∧ Sig3CountE V C₃ B₃ ∧ Sig2CountE V C₂ B₂

def LiteratureBoundAtPoints (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) (C₁ C₂' : ℝ) : Prop :=
  LitXPt D V C₃ B₃ C₂ B₂ → admitted D V → HeightBoundsFreeExponents D V C₁ C₂' (max B₃ B₂ + 1) (max B₃ B₂) (max B₃ B₂ + 1)

variable {D V}

def LiteratureBoundAbsoluteOnClass (𝒞 : ∀ D : D7, VData D → Prop) : Prop :=
  ∀ (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ), ∃ C₁ C₂' : ℝ, ∀ (D : D7) (V : VData D), 𝒞 D V →
    LiteratureBoundAtPoints D V C₃ B₃ C₂ B₂ C₁ C₂'

def LiteratureBoundAbsoluteAtPoints : Prop :=
  ∀ (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ), ∃ C₁ C₂' : ℝ, ∀ (D : D7) (V : VData D), LiteratureBoundAtPoints D V C₃ B₃ C₂ B₂ C₁ C₂'

theorem LiteratureBoundAbsoluteAtPoints.on (h : LiteratureBoundAbsoluteAtPoints) (𝒞 : ∀ D : D7, VData D → Prop) : LiteratureBoundAbsoluteOnClass 𝒞 :=
  fun C₃ B₃ C₂ B₂ => let ⟨C₁, C₂', h'⟩ := h C₃ B₃ C₂ B₂; ⟨C₁, C₂', fun D V _ => h' D V⟩

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), VData (Fm.D x i))

def LitFXPt (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LitXPt (Fm.D x i) (VF x i) C₃ B₃ C₂ B₂
def LiteratureFamilyBoundAtPoints (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) (C₁ C₂' : ℝ) : Prop :=
  LitFXPt Fm VF C₃ B₃ C₂ B₂ → AdmF Fm VF → FamilyFreeExponentBound Fm VF C₁ C₂' (max B₃ B₂ + 1) (max B₃ B₂) (max B₃ B₂ + 1)

end Fam

end Formalism.MainNotions.V.Pf.V3.LG
