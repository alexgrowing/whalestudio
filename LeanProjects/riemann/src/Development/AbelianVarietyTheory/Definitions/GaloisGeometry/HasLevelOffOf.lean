import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def PhiAt (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hBw : Pst.Induces Bw),
    ∀ (σ : Weil hA) (n : ℕ), GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (r.comp (Dec (F := E) A).subtype)) σ n =
      GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n

def UnitaryWeightConditionWithWeights (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ → ∀ (U : Submodule ℂ (UA E a → ℂ)) (S Y : Finset (HeightOneSpectrum (𝓞 E))),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → Ty E l a w₀ U' → Wt E l a ι w₀ v' U U' → SphOffU w₀ S U' →
        (∃ B, SatU U' v' B) → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
            ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
          ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → ∀ B, SatU U' w B → PhiAt ι r w B)

def HasLevelOff (w₀ v' : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥

open Classical in

def PowSatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (n : ℤ) : ℂ :=
  if h : ∃ B, SatU U w B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (fun z => z ^ n)).sum else 0

def CongUW3 (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ Kw : Levels E a, HasLevelOff w₀ v' Kw U ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w a) ∧
      ∀ (Z W : Finset (HeightOneSpectrum (𝓞 E))),
        (∀ z ∈ Z, IsSplitAt z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ∃ B, SatU U z B) →
        (∀ w ∈ W, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B) →
      ∃ c : HeightOneSpectrum (𝓞 E) → ℤ → ℂ, (∀ w n, c w n ≠ 0) ∧
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), IsSysU O U θ →
        PolyApprox (Sum.elim θ (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U p.1 p.2)))
          {ϑ | ∃ U' θ', AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ (∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧
            Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Z, GenAtU Gen U' z) ∧ IsSysU O U' θ' ∧
            ϑ = Sum.elim θ' (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U' p.1 p.2))} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

def LimWU3 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → CrysDRU U ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, SatU U w B →
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
          (hBw : Pst.Induces Bw) (σ : Weil hA),
        ∃ (C : Set (G E Ω →* GL (Fin a) (Qbar l))) (J : (E →+* Qbar l) → Multiset ℤ),
          (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
            ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
              IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) ∧
          GlobalTheory.CongPhi.JointApprox r C (fun n => ι.symm (GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n))
            (fun ρ n => ι.symm (GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (ρ.comp (Dec (F := E) A).subtype)) σ n)))

end GlobalTheory.CongL

end
