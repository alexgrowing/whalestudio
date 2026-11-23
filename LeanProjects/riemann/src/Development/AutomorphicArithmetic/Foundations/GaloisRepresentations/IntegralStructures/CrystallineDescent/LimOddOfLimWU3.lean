import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRegAlgTwistOfHalfIntegral
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasLevelOffOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.AllCoreOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)

namespace UpperTheory.Gal.Int.Core

def LimOdd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), Odd a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → FrobEig ι r w (algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → CrysDRU U ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, SatU U w B →
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
          (hBw : GlobalTheory.Pst.Induces Bw) (σ : Weil hA),
        ∃ (C : Set (G E Ω →* GL (Fin a) (Qbar l))) (J : (E →+* Qbar l) → Multiset ℤ),
          (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
            ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
              IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) ∧
          GlobalTheory.CongPhi.JointApprox r C (fun n => ι.symm (GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n))
            (fun ρ n => ι.symm (GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (ρ.comp (Dec (F := E) A).subtype)) σ n)))

def LimU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), Odd a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → FrobEig ι r w (algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → CrysDRU U ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, SatU U w B → PhiAt ι r w B)

theorem limU_of_limOdd (hC : GlobalTheory.CongPhi.ClosedPhi) (h : LimOdd) : LimU := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd T hT U hU w₀ v' h1 h2 h3 h4 h5
  obtain ⟨r, hc, hs, f1, f2, f3⟩ := h E Ω l ι a ha d hd T hT U hU w₀ v' h1 h2 h3 h4 h5
  refine ⟨r, hc, hs, f1, f2, fun w hw a1 a2 B hB P AI ht A hA O _ _ _ Bw hBw σ n => ?_⟩
  obtain ⟨C, J, hCJ, hJ⟩ := f3 w hw a1 a2 B hB P AI ht A hA O Bw hBw σ
  have := hC E Ω l ι a ha.pos P AI ht w A hA O Bw hBw J r hc hs C hCJ σ _ hJ n
  rwa [RingEquiv.apply_symm_apply] at this

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

variable (Ω) in

def CoreAtP (p : HeightOneSpectrum (𝓞 E) → Prop) (ι : Qbar l ≃+* ℂ) (m : ℕ) : Prop :=
  ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, p w → GlobalTheory.Row9.SatU U w B → ∀ c, GlobalTheory.Row9.SphG c ι r w B fun τ => infOfWeight (lam τ)

def CoreUd : Prop :=
  ∀ m : ℕ, Odd m → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), GlobalTheory.Row9.FieldOK l E → ∀ d : ℕ, ImQ E d → SqAt d l → CoreAtP Ω (UsPl (E := E) d) ι m

def AllUd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), GlobalTheory.Row9.FieldOK l E → UpperTheory.Gal.TP.InertOK E → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ n : ℕ, 1 ≤ n → CoreAtP Ω (UsPl (E := E) d) ι n

variable (Ω) in

def RowP (p : HeightOneSpectrum (𝓞 E) → Prop) {a : ℕ} (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
    ∀ w B, p w → (CG.mk π).HasSat w B → ∀ c, GlobalTheory.RoadU.SphAt c π ι r w B

def CoreGLu : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), GlobalTheory.Row9.FieldOK l E → UpperTheory.Gal.TP.InertOK E → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) → RowP Ω (UsPl (E := E) d) π ι

def RowCsd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .all l π (quadChar E ^ a) → RowP Ω (fun _ => True) π ι

end UpperTheory.Gal.Int.Core

end
