import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
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
end Loc
section
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
theorem AdInW.toIn_alt {ι : Qbar l ≃+* ℂ} {M m : ℕ} {r : G L Ω →* GL (Fin 2) (Qbar l)} (h : AdInW ι M m r) : _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r :=
  ⟨h.cont, _root_.UpperTheory.V.Z.Win.Birth.mkCsdW' h.aut fun _ => h.wit, h.irr, h.gap, h.unr, h.away, h.above⟩
end
structure PureWeightCompatibility : Prop where
  af : _root_.UpperTheory.V.Af.Hypotheses'
  gal : GalUnitaryT
  compat : CompatT
  same : Z.Desc.W.Same
  plain : PlainRec
  desc : Z.Desc.DescUse
def PlainOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    (∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1) → PT τ
def PsOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L))), PT τ →
    ∃ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      ∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1
def EigWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G L Ω →* GL (Fin n) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∀ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    ∀ s : Weil h, (r (s : G L Ω)).val.charpoly.map ι.toRingHom =
      psPol ψ (a s)
def AboveWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ m : ℕ, 2 ≤ m →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ HT, HasHTAt r HT w → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    (∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    (∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)) ∧
      ∃ b : ℤ, ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = {b, b + m}
def AwayWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → Unlinked (ad0 r) →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)
def GoodWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := L) A, r s = 1) → (∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)
def LocSubDAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Sig.Lev k)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ (V.J n) →
    (∀ d, Sig.SDom d → Hi.dc τ (V.J n) (V.J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ)
def GalExWAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∃ r : G L Ω →* GL (Fin n) (Qbar l), GalT ι σ r ∧
      (IsIrr r → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧ Lifts σ π)
def AboveWeightAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ M m : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M → ∀ r : G L Ω →* GL (Fin 2) (Qbar l), AdInW ι M m r →
    ∃ (σ : Submodule ℂ (UA L 2 → ℂ)) (HT : (L →+* Qbar l) → Multiset ℤ), IsAutRepU σ ∧ GalT ι σ r ∧
      (∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → PT τ ∧ HasHTAt r HT w) ∧ (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → IsUnramU σ w) ∧
      ∀ v : InfinitePlace L, ∃ lam, HasWeightAt σ v.embedding lam ∧ lam.w 0 - lam.w 1 = ((m - 1 : ℕ) : ℤ)
def Branch1WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ₃ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ₃ → (∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ₃ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) →
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧ Lifts σ₃ π
def Branch2WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ' : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ' →
    (∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ' w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2) → False
def PlainAtWAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (σ : Submodule ℂ (UA L 3 → ℂ)) (π : CuspSub L 3), IsAutRepU σ →
    Lifts σ π → ∀ w, IsSplitAt w → ∀ a : (Kw w)ˣ →* ℂˣ, NoLk a → CompSub σ w ![a, 1, a⁻¹] → ∀ τ, π.IsLocComp w τ → PT τ
end UpperTheory.V.Z.Sym.W
end
end
