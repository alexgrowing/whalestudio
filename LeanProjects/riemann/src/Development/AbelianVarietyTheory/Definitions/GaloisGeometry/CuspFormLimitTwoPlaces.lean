import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def SeedWtU : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), (Qbar l ≃+* ℂ) →
    HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Submodule ℂ (UA E a → ℂ) → Prop

def SeedWtU.noCondition : SeedWtU := fun _ _ _ _ _ _ _ _ _ _ _ _ => True

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def OverPl (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x ∈ w.asIdeal, ‖ι.symm (τ (x : E))‖ < 1

def SameWtAt (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SameWtOff (ι : Qbar l ≃+* ℂ) (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, (∀ u : HeightOneSpectrum (𝓞 E), OverPl ι τ u → Apart u w₀ ∧ Apart u v') →
    ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SeedWU2 (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU := SeedWtU.noCondition) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → SameWtOff ι w₀ v' U U' → Wt E l a ι w₀ v' U U' →
      Ty E l a w₀ U' → SphOffU w₀ S U' → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
            ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
          ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w)

def CongUW2 (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ →
    ∃ Kw : Levels E a, HasLevelU w₀ Kw U ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w a) ∧
      ∀ Z : Finset (HeightOneSpectrum (𝓞 E)),
        (∀ z ∈ Z, IsSplitAt z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ∃ B, SatU U z B) →
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), IsSysU O U θ →
        PolyApprox θ {θ' | ∃ U', AutOffT T U' ∧ HasLevelU w₀ Kw U' ∧ SameWtOff ι w₀ v' U U' ∧ Wt E l a ι w₀ v' U U' ∧
          Ty E l a w₀ U' ∧ (∀ z ∈ Z, GenAtU Gen U' z) ∧ IsSysU O U' θ'} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

def LimWU2 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → CrysDRU U ι r w)

def CuspFormLimitTwoPlaces : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, (CG.mk π).HasSat w B) →
        ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w)

theorem sameWtOff_of_eq (ι : Qbar l ≃+* ℂ) (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ))
    (h : ∀ τ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam) : SameWtOff ι w₀ v' U U' :=
  fun τ _ lam => h τ lam

theorem sameWtAt_of_off (ι : Qbar l ≃+* ℂ) {w₀ v' w : HeightOneSpectrum (𝓞 E)} {U U' : Submodule ℂ (UA E a → ℂ)}
    (h : SameWtOff ι w₀ v' U U') (hw : ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ u, OverPl ι τ u → u = w)
    (h₀ : Apart w w₀) (h' : Apart w v') : SameWtAt ι w U U' :=
  fun τ hτ lam => h τ (fun u hu => by rw [hw τ hτ u hu]; exact ⟨h₀, h'⟩) lam

def SeedWtU.ofWeightPredicate
    (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), (Qbar l ≃+* ℂ) →
      HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Prop) : SeedWtU :=
  fun E _ _ _ l _ a ι _ v' _ U' => P E l a ι v' U'

theorem SeedWU2.mono {Ty : UnitaryAutomorphicTypeClass} {Gen : ℕ → ℕ → Multiset ℂˣ → Prop} {Wt Wt' : SeedWtU}
    (h : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ) (ι : Qbar l ≃+* ℂ)
      (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)), Wt' E l a ι w₀ v' U U' → Wt E l a ι w₀ v' U U')
    (hS : SeedWU2 Ty Gen Wt) : SeedWU2 Ty Gen Wt' := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd T hT U hU w₀ v' hw₀ hs hv' hap S Y
  obtain ⟨Z₀, hZ, hr⟩ := hS E Ω l ι a ha d hd T hT U hU w₀ v' hw₀ hs hv' hap S Y
  exact ⟨Z₀, hZ, fun U' hA hoff hW => hr U' hA hoff (h E l a ι w₀ v' U U' hW)⟩

theorem CongUW2.mono {Ty : UnitaryAutomorphicTypeClass} {Gen : ℕ → ℕ → Multiset ℂˣ → Prop} {Wt Wt' : SeedWtU}
    (h : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ) (ι : Qbar l ≃+* ℂ)
      (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)), Wt' E l a ι w₀ v' U U' → Wt E l a ι w₀ v' U U')
    (hC : CongUW2 Ty Gen Wt') : CongUW2 Ty Gen Wt := by
  intro E _ _ _ l _ ι a ha T hT U hU w₀ v' hw₀ hs hv' hap
  obtain ⟨Kw, h1, h2, h3, h4⟩ := hC E l ι a ha T hT U hU w₀ v' hw₀ hs hv' hap
  refine ⟨Kw, h1, h2, h3, fun Z hZ J O θ hθ => ?_⟩
  obtain ⟨hP, hL⟩ := h4 Z hZ J O θ hθ
  refine ⟨GlobalTheory.Cong.PolyApprox.mono hP ?_, hL⟩
  rintro θ' ⟨U', g1, g2, g3, g4, g5⟩
  exact ⟨U', g1, g2, g3, h E l a ι w₀ v' U U' g4, g5⟩

theorem SeedWU2.of_any {Ty : UnitaryAutomorphicTypeClass} {Gen : ℕ → ℕ → Multiset ℂˣ → Prop} (Wt : SeedWtU) (hS : SeedWU2 Ty Gen) :
    SeedWU2 Ty Gen Wt :=
  SeedWU2.mono (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hS

example (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) :
    SeedWU2 Ty Gen (fun _ _ _ _ _ _ _ _ _ _ _ _ => False) := by
  intro E Ω _ _ _ _ _ _ l _ ι a _ d _ T _ U _ w₀ v' _ _ _ _ S Y
  exact ⟨∅, by simp, fun _ _ _ hW => hW.elim⟩

end GlobalTheory.CongL

end
