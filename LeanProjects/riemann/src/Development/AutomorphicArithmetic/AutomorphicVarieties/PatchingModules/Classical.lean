import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa

def ellC (l : ℕ) (G : Type) [CommGroup G] : Subgroup G where
  carrier := {x | (orderOf x).Coprime l}
  one_mem' := by simp
  mul_mem' {x y} hx hy := Nat.Coprime.coprime_dvd_left (Commute.all x y).orderOf_mul_dvd_mul_orderOf (Nat.Coprime.mul_left hx hy)
  inv_mem' {x} hx := by simpa using hx

section Lv

variable (l : ℕ) {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → Plc L)

def UK : Subgroup (GV n w) := Subgroup.pi Set.univ fun j => KO ((w j).adicCompletion L) (Fin n)

def UIw : Subgroup (GV n w) := Subgroup.pi Set.univ fun j => iwC ((w j).adicCompletion L) n ⊤

def UIw1 : Subgroup (GV n w) := Subgroup.pi Set.univ fun j => iwC ((w j).adicCompletion L) n (ellC l _)

def atJ (j : Fin q) : GLw n (w j) →* GV n w := MonoidHom.mulSingle (fun j => GLw n (w j)) j

end Lv

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D)
  {V : s.Lev} (h : (globOf r V).Hom (globOf r V0)) {q : ℕ} (w : Fin q → Plc L)

structure LevMod : Type 1 where
  rN : Resid (globOf r V).frame O n
  compat : Glob.Compat h rN (residOf r)
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]
  p : Pair rN R
  [algL : Algebra (abelian₂ O Empty D) R]
  [towO : IsScalarTower O (abelian₂ O Empty D) R]
  segmentWeightExponent : ∀ k, algebraMap (abelian₂ O Empty D) R (MvPowerSeries.X (.inr k)) =
    algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1
  β : R →ₐ[O] B.B
  β_pair : p.Maps β.toRingHom ((pairOf B.u).D.comap h.p₀) (pairOf B.u).ψ
  P : Type
  [add : AddCommGroup P]
  [mod : Module R P]
  [modL : Module (abelian₂ O Empty D) P]
  [tow : IsScalarTower (abelian₂ O Empty D) R P]
  ρ : Representation R (GV n w) P
  fin : Module.Finite (abelian₂ O Empty D) (fixd ρ (UIw1 l n w))
  proj : ∃ (_ : ((UIw1 l n w).subgroupOf (UIw n w)).Normal)
    (ρ' : Representation (abelian₂ O Empty D) (UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)) (fixd ρ (UIw1 l n w))),
    (∀ (u : UIw n w) f, (ρ' (u : UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)) f : P) = ρ u f) ∧
      Module.Projective (MonoidAlgebra (abelian₂ O Empty D) (UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w))) ρ'.asModule
  eM : fixd ρ (UK n w) ≃+ b.M
  eM_smul : ∀ (t : R) m, eM (t • m) = β t • eM m

attribute [instance] LevMod.ring LevMod.alg LevMod.co LevMod.algL LevMod.towO LevMod.add LevMod.mod LevMod.modL LevMod.tow

variable {b h w}

structure LevPt (A : LevMod b h w) (ι : Qbar l ≃+* ℂ) : Type 1 where
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
  lg : ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL ((w j).adicCompletion L) → WD hB), IsRec hB rc →
    UpperTheory.V.Lev.WO ι (rep.comp V.pr) (rc (algNorm (σ j)))

attribute [instance] LevPt.add LevPt.mod

def LevMod.Classical (A : LevMod b h w) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, ∀ m : A.P, (∀ x : LevPt A ι, x.sp m = 0) → m = 0

variable (B J) in

def Level : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)),
    ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
      (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
      V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
      (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.Classical

structure LocP : Prop where
  ll : GlobalTheory.Published.LocalLanglandsGL
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  gl : GlobalTheory.Published.GeometricLemma
  tame : GlobalTheory.Published.TameLocal

def HasAutOf : Prop :=
  LocP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), V0.S' = s.S → Level B J → HasAut B J

end UpperTheory.V.Pa
