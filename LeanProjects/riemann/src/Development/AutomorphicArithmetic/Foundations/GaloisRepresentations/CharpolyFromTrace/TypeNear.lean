import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori

namespace UpperTheory.Gal.NearKilling

def TypeNear (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      NearTr r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun i s => ι.symm (η (blockOf d hd i) (art (ineIncl h s)))) ∧
      ∀ b₀, NearKills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun s => ι.symm (η b₀ (art (ineIncl h s))))
        fun b s => ι.symm (η (b₀.succAbove b) (art (ineIncl h s)))

def IAType (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ∀ hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal,
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      InePol (wdOf h hl ι r) (fun i s => η (blockOf d hd i) (art (ineIncl h s))) ∧
      ∀ b₀, (∀ b, b ≠ b₀ → θ b ≠ θ b₀) → EigZero (wdOf h hl ι r) fun s => η b₀ (art (ineIncl h s))

def IA : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → UpperTheory.GalS.TmW (rc (algNorm σ)) →
      IneRel (wdOf h hl ι r) (rc (algNorm σ))

end UpperTheory.Gal.NearKilling
