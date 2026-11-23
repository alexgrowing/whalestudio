import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
variable {l : ℕ} [Fact l.Prime]
section Pt
variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
variable {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)
variable (T : TWGrp G0)
end Pt
section Mod
variable {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) (x : B →ₐ[O] O)
variable {b} {G : Glob l L} {h : G.Hom G0} {q N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ)
end Mod
section Bar
variable (F : GFrame l) {n : ℕ} (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)]
  (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))
end Bar
section Ar
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev}
def LevelAtOrdinaryDeterminantRing {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r}
    {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D) : Prop :=
  ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
    (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
    V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
    (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
variable {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
def LevelIdealCondition (J : Ideal B.B) : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b ∧ (∀ k, b.wt.γ k ∈ V0.frame.Iv (b.wt.v k)) ∧
    ∀ (x : B.B →ₐ[c.O] c.O) (h : s.Wt n), (barPt B x).Arith h → CtrlH b x
end Ar
def HidaFamilyCondition : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (n : ℕ), 1 ≤ n →
    ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ), ∃ J : Ideal B.B, B.PointTheoremBaseObject ι J ∧ _root_.UpperTheory.V.Th.LevelIdealCondition B J
def HasHeckeOperatorDense : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ)
    (b : TWBase (pairOf B.u) J Empty D), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b → ∀ T : TWGrp (globOf r V0), TWPl r T → OpAt b T
def OrdinaryMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B)
    (y : Pt (globOf r V0).frame c.O n) (x : B.B →ₐ[c.O] c.O) (h : s.Wt n) (q : ℕ) (sg : Fin q → V0.frame.G₀)
    (al : Fin q → Fin n → c.O), V0.S' = s.S → 1 ≤ n → _root_.UpperTheory.V.Th.LevelIdealCondition B J → J ≤ RingHom.ker x → (barPt B x).Arith h →
    B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → y.N4 V0.frame.D0 →
    (∀ j, sg j ∈ V0.frame.G' ∧ Function.Injective (al j) ∧
      (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range sg) →
    ∀ δ : B.B →ₗ[c.O] c.O, IsDer x δ → (∀ v i, ∀ g ∈ V0.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) →
      ∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = 0
end UpperTheory.V.Th
end
end
