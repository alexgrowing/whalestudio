import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprodStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev PlF (E : Type) [Field E] [NumberField E] [IsCMField E] : Type := HeightOneSpectrum (𝓞 (maximalRealSubfield E))

abbrev Above (v : PlF E) : Type := {w : Pl E // w.under (𝓞 (maximalRealSubfield E)) = v}

abbrev Av (v : PlF E) : Type := ∀ w : Above v, w.1.adicCompletion E

def projv (v : PlF E) : Af E →+* Av v := RingHom.pi fun w => pLoc E w.1

abbrev Yv (a b : ℕ) (v : PlF E) : Type := GL (Fin a) (Av v) × GL (Fin b) (Av v)

def pv (a b : ℕ) (v : PlF E) : Gf E a b →* Yv a b v :=
  (GeneralLinearGroup.map (projv v)).prodMap (GeneralLinearGroup.map (projv v))

def evw {v : PlF E} (w : Above v) (y : Yv a b v) : GLw a w.1 × GLw b w.1 :=
  (GeneralLinearGroup.map (Pi.evalRingHom _ w) y.1, GeneralLinearGroup.map (Pi.evalRingHom _ w) y.2)

def Kv (a b : ℕ) (v : PlF E) : Subgroup (Yv a b v) :=
  ⨅ w : Above v, (K2 (E := E) a b w.1).comap ((GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)).prodMap
    (GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)))

def CjEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : PlF E), ∃ c : Av v →+* Av v, Continuous c ∧
  ∀ x : Af E, projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = c (projv v x)

def cjv (v : PlF E) : Av v →+* Av v :=
  if h : ∃ c : Av v →+* Av v, Continuous c ∧ ∀ x : Af E, projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = c (projv v x)
  then h.choose else RingHom.id _

def thv (a b : ℕ) (v : PlF E) : Yv a b v →* Yv a b v := (thetaGL a (cjv v)).prodMap (thetaGL b (cjv v))

def fv (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (v : PlF E) (y : Yv a b v) : ℂ :=
  ∏ᶠ (w : Above v) (_ : w.1 ∈ S), φ₁ w.1 (evw w y) * if IsSplitAt w.1 then φ₂ w.1 (evw w (thv a b v y)) else 1

def RestrV : Prop := CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (pv (E := E) a b) (Kv a b) ∧
  (∀ v x, pv a b v (thP E a b x) = thv a b v (pv a b v x)) ∧ (∀ v, ∀ k ∈ Kv (E := E) a b v, thv a b v k ∈ Kv a b v) ∧
  ∀ x, x ∈ (Kf E a).prod (Kf E b) ↔ ∀ v, pv a b v x ∈ Kv a b v

def Regroup : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ y, finFn S φ₁ φ₂ y = ∏ᶠ v, fv S φ₁ φ₂ v (pv a b v y)

def LocCompare : Prop := CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b → ∀ (w : Pl E), w ∈ S →
    twOrb (thv a b (w.under (𝓞 (maximalRealSubfield E)))) (Kv a b _) (pv a b _ (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ _) =
      twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)

def LocCompareInert : Prop := CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b → ∀ (w : Pl E), w ∈ S → ¬ IsSplitAt w →
    twOrb (thv a b (w.under (𝓞 (maximalRealSubfield E)))) (Kv a b _) (pv a b _ (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ _) =
      twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)

def LocCompareSplit : Prop := CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b → ∀ (w : Pl E), w ∈ S → IsSplitAt w →
    twOrb (thv a b (w.under (𝓞 (maximalRealSubfield E)))) (Kv a b _) (pv a b _ (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ _) =
      twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)

def LocCompareOf : Prop := LocCompareInert → LocCompareSplit → LocCompare

def LocHyp : Prop := CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
  let δ : Gf E a b := (ratF E a δ₁, ratF E b δ₂)
  (∀ v, ∀ x ∈ twCent (thv a b v) (pv a b v δ), ∀ y ∈ twCent (thv a b v) (pv a b v δ), x * y = y * x) ∧
  (∀ v (y : Yv a b v), (rStab fun k : Kv a b v => fv S φ₁ φ₂ v ((y * k)⁻¹ * pv a b v δ * thv a b v (y * k))).index ≠ 0) ∧
  (∀ v, {q : DoubleCoset.Quotient (twCent (thv a b v) (pv a b v δ) : Set (Yv a b v)) (Kv a b v : Set (Yv a b v)) |
    ∃ k ∈ Kv a b v, fv S φ₁ φ₂ v ((Quotient.out q * k)⁻¹ * pv a b v δ * thv a b v (Quotient.out q * k)) ≠ 0}.Finite) ∧
  (∀ v (y : Yv a b v), twCent (thv a b v) (pv a b v δ) ⊓ (Kv a b v).map (MulAut.conj y).toMonoidHom ≤
      cptPart (twCent (thv a b v) (pv a b v δ)) ∧
    (twCent (thv a b v) (pv a b v δ) ⊓ (Kv a b v).map (MulAut.conj y).toMonoidHom).relIndex
      (cptPart (twCent (thv a b v) (pv a b v δ))) ≠ 0) ∧
  ∀ᶠ v in cofinite, fv S φ₁ φ₂ v = (Kv a b v : Set (Yv a b v)).indicator 1 ∧ pv a b v δ ∈ Kv a b v ∧
    cptPart (twCent (thv a b v) (pv a b v δ)) ≤ Kv a b v ∧
    ∀ y, y⁻¹ * pv a b v δ * thv a b v y ∈ Kv a b v → ∃ t ∈ twCent (thv a b v) (pv a b v δ), ∃ k ∈ Kv a b v, y = t * k

def secPl (S : Set (Pl E)) (v : PlF E) : Option (Pl E) :=
  if h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v then some h.choose else none

def Reindex : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ g : Pl E → ℂ,
  ∏ᶠ w ∈ S, g w = ∏ᶠ v : PlF E, (secPl S v).elim 1 g

def EulerFinOf' : Prop := CjEx → RestrV → Regroup → LocCompare → LocHyp → Reindex → EulerFin

end PositivityTheory.Rg.BcB.G8.Fin

end
