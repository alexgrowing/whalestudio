import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.RoadW

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SatAtU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧
    GlobalTheory.LGrp.HasSatakeGL σ.ρ B

def HasRepU (ι : Qbar l ≃+* ℂ) (U : Submodule ℂ (UA E a → ℂ)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → w ∉ S → ∀ B : Multiset ℂˣ, SatAtU U w B →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
    (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → SstAt r w ∧ GlobalTheory.CongL.CrysDRU U ι r w ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
        (hj : Pst.Induces Bw), (IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) ∧
        ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g)

def RowStarCoreU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def UnitaryBaseConditions : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    w₀ ∈ S → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) → ScU U w₀ →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def RowStarCoreAtU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → (∀ w, ¬ Apart w w₀ → w ∈ S) →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def LimitStepU : Prop := CongU → UnitaryBaseConditions → RowStarCoreAtU

def SplitPlaceUnramifiedGalois : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B →
        GlobalTheory.RoadU.SphAt .unr π ι r w B

theorem HasRepU.mono {ι : Qbar l ≃+* ℂ} {U : Submodule ℂ (UA E a → ℂ)} {S S' : Finset (HeightOneSpectrum (𝓞 E))} (hS : S ⊆ S')
    {r : G E Ω →* GL (Fin a) (Qbar l)} (h : HasRepU ι U S r) : HasRepU ι U S' r :=
  ⟨h.1, h.2.1, fun w hw hn => h.2.2 w hw fun hm => hn (hS hm)⟩

theorem finite_not_apart (w₀ : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 E) | ¬ Apart w w₀}.Finite := by
  set p := w₀.under (𝓞 (maximalRealSubfield E))
  haveI := p.isMaximal
  have hf : (p.asIdeal.primesOver (𝓞 E)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 E)
  refine (hf.preimage (f := fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal)
    (fun x _ y _ e => HeightOneSpectrum.ext e)).subset fun w hw => ?_
  have e : w.under (𝓞 (maximalRealSubfield E)) = p := not_not.1 hw
  exact ⟨w.isPrime, ⟨by rw [← e]; rfl⟩⟩

def nearPlaces (w₀ : HeightOneSpectrum (𝓞 E)) : Finset (HeightOneSpectrum (𝓞 E)) :=
  (finite_not_apart w₀).toFinset

theorem mem_nearPlaces {w w₀ : HeightOneSpectrum (𝓞 E)} : w ∈ nearPlaces w₀ ↔ ¬ Apart w w₀ :=
  Set.Finite.mem_toFinset _

theorem isSplitAt_of_not_apart {w w₀ : HeightOneSpectrum (𝓞 E)} (h₀ : IsSplitAt w₀) (h : ¬ Apart w w₀) : IsSplitAt w := by
  have e := not_not.1 h
  by_cases hw : w = w₀
  · exact hw ▸ h₀
  · exact ⟨w₀, Ne.symm hw, e.symm⟩

theorem RowStarCoreAtU.near (h : RowStarCoreAtU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (hT : NonSplitSet T) {w₀ : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal) (h₀ : IsSplitAt w₀)
    {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (hu : ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U (nearPlaces w₀) r :=
  h E Ω l ι a ha _ T hT (fun _ hw => isSplitAt_of_not_apart h₀ (mem_nearPlaces.1 hw)) w₀ hl h₀
    (fun _ hw => mem_nearPlaces.2 hw) U hU hu

example (w₀ : HeightOneSpectrum (𝓞 E)) : w₀ ∈ nearPlaces w₀ := mem_nearPlaces.2 (not_apart_self w₀)

example (h : RowStarCoreU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) : ∃ r : G E Ω →* GL (Fin a) (Qbar l),
    HasRepU ι (Submodule.span ℂ {(fun _ => 1 : UA E a → ℂ)}) ∅ r :=
  h E Ω l ι a ha ∅ ∅ nonSplitSet_empty (fun _ hw => absurd hw (Finset.notMem_empty _)) _ isAutRepU_const
    fun w _ _ => isUnramU_const w

example (h : RowStarCoreAtU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) {w₀ : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (h₀ : IsSplitAt w₀) : ∃ r : G E Ω →* GL (Fin a) (Qbar l),
      HasRepU ι (Submodule.span ℂ {(fun _ => 1 : UA E a → ℂ)}) (nearPlaces w₀) r :=
  h.near ι ha nonSplitSet_empty hl h₀ isAutRepU_const fun w _ _ => isUnramU_const w

end GlobalTheory.RoadW

end
