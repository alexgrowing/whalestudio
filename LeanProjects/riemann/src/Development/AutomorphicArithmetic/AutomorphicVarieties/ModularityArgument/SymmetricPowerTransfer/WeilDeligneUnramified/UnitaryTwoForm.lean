import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

open UpperTheory.V.Z.Win UpperTheory.GalN.V

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def NoLk (a : kˣ →* ℂˣ) : Prop := ∀ j : ℕ, j = 1 ∨ j = 2 → ∀ e : ℤ, e = 1 ∨ e = -1 → a ^ j ≠ absPow k (e : ℂ)

abbrev PT (τ : SmIrr (GL (Fin n) k)) : Prop := GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred)

def psPol (ψ : Fin n → kˣ →* ℂˣ) (x : kˣ) : ℂ[X] :=
  ∏ j, (Polynomial.X - Polynomial.C ((ψ j x * absPow k (-(((n : ℂ) - 1) / 2)) x : ℂˣ) : ℂ))

end Loc

section

variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]

structure AdInW (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)) : Prop where
  cont : Continuous r
  aut : AutCsd0 ι r
  wit : WitA ι r
  unl : Unlinked (ad0 r)
  pair : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar L Ω l ^ (1 - ((2 : ℕ) : ℤ))) P
  irr : IrrOpen r
  gap : 2 ≤ m
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, r s = 1
  away : ∃ τ : Fin 2 → G L Ω →* (Qbar l)ˣ, (∀ i, Continuous (τ i)) ∧ TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k

theorem AdInW.toIn {ι : Qbar l ≃+* ℂ} {M m : ℕ} {r : G L Ω →* GL (Fin 2) (Qbar l)} (h : AdInW ι M m r) : AdIn ι M m r :=
  ⟨h.cont, Birth.mkCsdW h.aut fun _ => h.wit, h.irr, h.gap, h.unr, h.away, h.above⟩

structure GalT {n : ℕ} (ι : Qbar l ≃+* ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (r : G L Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  comp : ∀ w, IsSplitAt w → ∃ τ, Comp σ w τ
  loc : ∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → LocGlobT ι r w τ
  pair : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar L Ω l ^ (1 - (n : ℤ))) P

structure Lifts {n : ℕ} (σ : Submodule ℂ (UA L n → ℂ)) (π : CuspSub L n) : Prop where
  unr : ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B
  comp : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (Kw w)), π.IsLocComp w τ → Comp σ w τ

end

structure PrW : Prop where
  af : Af.Hypotheses₂
  gal : GalUnitaryT
  compat : CompatT
  same : Z.Desc.W.Same
  plain : PlainRec
  desc : Z.Desc.DescUse

def PlainOf : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    (∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1) → PT τ

def PsOf : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L))), PT τ →
    ∃ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      ∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1

def EigW : Prop :=
  Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G L Ω →* GL (Fin n) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∀ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    ∀ s : Weil h, (r (s : G L Ω)).val.charpoly.map ι.toRingHom =
      psPol ψ (a s)

def AboveW : Prop :=
  Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ m : ℕ, 2 ≤ m →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ HT, HasHTAt r HT w → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    (∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    (∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)) ∧
      ∃ b : ℤ, ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = {b, b + m}

def AwayW : Prop :=
  Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → Unlinked (ad0 r) →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)

def GoodW : Prop :=
  Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := L) A, r s = 1) → (∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)

def LocSubD : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Sig.Lev k)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ (V.J n) →
    (∀ d, Sig.SDom d → Hi.dc τ (V.J n) (V.J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ)

def GalExW : Prop :=
  PrW → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∃ r : G L Ω →* GL (Fin n) (Qbar l), GalT ι σ r ∧
      (IsIrr r → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧ Lifts σ π)

def UnitaryTwoForm : Prop :=
  PrW → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ M m : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M → ∀ r : G L Ω →* GL (Fin 2) (Qbar l), AdInW ι M m r →
    ∃ (σ : Submodule ℂ (UA L 2 → ℂ)) (HT : (L →+* Qbar l) → Multiset ℤ), IsAutRepU σ ∧ GalT ι σ r ∧
      (∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → PT τ ∧ HasHTAt r HT w) ∧ (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → IsUnramU σ w) ∧
      ∀ v : InfinitePlace L, ∃ lam, HasWeightAt σ v.embedding lam ∧ lam.w 0 - lam.w 1 = ((m - 1 : ℕ) : ℤ)

def Branch1W : Prop :=
  PrW → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ₃ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ₃ → (∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ₃ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) →
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧ Lifts σ₃ π

def Branch2W : Prop :=
  PrW → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ' : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ' →
    (∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ' w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2) → False

def SelectW : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (X : Set (Plc L)), ∀ w₀ ∈ X, ∃ P ⊆ X, w₀ ∈ P ∧
    Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) P ∧ ∀ w ∈ X, ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))

def PlainAtW : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (σ : Submodule ℂ (UA L 3 → ℂ)) (π : CuspSub L 3), IsAutRepU σ →
    Lifts σ π → ∀ w, IsSplitAt w → ∀ a : (Kw w)ˣ →* ℂˣ, NoLk a → CompSub σ w ![a, 1, a⁻¹] → ∀ τ, π.IsLocComp w τ → PT τ

def GlueW : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (R : G L Ω →* GL (Fin 3) (Qbar l)),
    (∀ w : Plc L, ∃ π : CuspSub L 3, AttC ι R π ∧ ((∃ B, (CG.mk π).HasSat w B) ∨ ∀ τ, π.IsLocComp w τ → PT τ)) → Birth.AllW ι R

def AdLiftW : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ (S₀ : Finset (Plc L)) (P : Set (Plc L)),
    Disjoint (S₀ : Set (Plc L)) P → Places ((S₀ : Set (Plc L)) ∪ P) → HasTwo S₀ →
    ∀ π : Submodule ℂ (UA L 2 → ℂ), IsAutRepU π → ∀ j : ℕ, 1 ≤ j →
    (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
    (∀ w : Plc L, (∀ w' ∈ S₀, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU π w) →
    ∀ ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ w ∈ (S₀ : Set (Plc L)) ∪ P, CompEq π w (ψ w)) →
    (∀ w ∈ P, (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ w i u = 1) ∧ Reg (ψ w 0 / ψ w 1)) →
    (∃ σ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ ∧
      (∀ w : Plc L, (∀ w' ∈ S₀, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU σ w) ∧
      (∀ w ∈ S₀, CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) ∧
      ∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) ∨
    ∃ σ : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ ∧
      ∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2

def AdAutW : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ M m : ℕ, M ≠ 0 → 2 * l ∣ M → UnrSplit L M → ∀ r : G L Ω →* GL (Fin 2) (Qbar l), AdInW ι M m r →
    AutCsd0 ι (tw (ad0 r) (cycBar L Ω l)⁻¹) ∧ Birth.AllW ι (tw (ad0 r) (cycBar L Ω l)⁻¹)

def PropEGW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ Birth.PR ι ρ ∧ Unlinked (ad0 ρ)

def SeedInW : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ)
    (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), FieldPairCharacterTripleConditions K L c N w χ' η θ j → ∀ M : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ' (Base.galEmb ℚ L Ω s) = 1) →
    ∀ (m : ℕ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)), 2 ≤ m → EisRep ι (χ' * η) θ (m + 1) ρ → IrrOpen ρ → Birth.PR ι ρ → Unlinked (ad0 ρ) →
    (χ' * η) c = (-1) ^ (m + 1) → ∃ κ : G L Ω →* (Qbar l)ˣ, AdInW ι M m (tw (ρ.comp (Base.galEmb ℚ L Ω)) κ)

end UpperTheory.V.Z.Sym.W

end
