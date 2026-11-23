import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Pa
section Lv
variable (l : ℕ) {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → Plc L)
end Lv
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D)
  {V : s.Lev} (h : (globOf r V).Hom (globOf r V0)) {q : ℕ} (w : Fin q → Plc L)
variable {b h w}
structure LevPtAlt (A : LevMod b h w) (ι : Qbar l ≃+* ℂ) : Type 1 where
  θ : A.R →+* Qbar l
  rep : (globOf r V).G₀ →* GL (Fin n) (Qbar l)
  cont : Continuous rep
  det : A.p.D.map θ = GDet.ofRep (mat rep)
  Y : Type
  [add : AddCommGroup Y]
  [mod : Module ℂ Y]
  π : Representation ℂ (GV n w) Y
  sp : A.P →+ Y
  sp_smul : ∀ (t : A.R) m, sp (t • m) = ι (θ t) • sp m
  sp_act : ∀ g m, sp (A.ρ g m) = π g (sp m)
  σ : ∀ j, SmIrr (GLw n (w j))
  iso : ∀ j, IsoSum (π.comp (atJ n w j)) ⊤ (σ j)
  lg : ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL ((w j).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (rep.comp V.pr) (rc (algNorm (σ j)))
attribute [instance] LevPtAlt.add LevPtAlt.mod
def LevMod.ClassicalAlt (A : LevMod b h w) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, ∀ m : A.P, (∀ x : _root_.UpperTheory.V.Pa.LevPtAlt A ι, x.sp m = 0) → m = 0
variable (B J) in
def LevelAlt : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)),
    ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
      (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
      V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
      (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
structure LocPAlt : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  gl : GlobalTheory.Published.GeometricLemma
  tame : GlobalTheory.Published.TameLocal
def HasAutOfAlt : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), V0.S' = s.S → _root_.UpperTheory.V.Pa.LevelAlt B J → HasAut B J
end UpperTheory.V.Pa
end
end
