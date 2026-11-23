import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero

noncomputable section

open scoped ComplexConjugate
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D} (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (m : Measure (GA D A))

def thetaLift (Φ : WO A B → ℂ) (f : GA D A → ℂ) : GA D B → ℂ :=
  fun h => petersson A m (fun g => thetaKO ω g h Φ) f

def LiftConv (Φ : WO A B → ℂ) (f : GA D A → ℂ) : Prop :=
  ∀ h, Integrable (descend (GQ A) fun g => thetaKO ω g h Φ * conj (f g)) (autMeasure A m)

def LowerLiftsZero (ψ : AddChar (AF D.host.F) ℂ) (B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (π : Submodule ℂ (GA D A → ℂ)) : Prop :=
  ∀ (i : ℕ) (B' : HSp D), 1 ≤ i → IsWittLower B B' i → B'.SigOK →
    ∀ ω' : GA D A × GA D B' →* Module.End ℂ (WO A B' → ℂ), IsWeilDatumO ψ A B' χA χB ω' →
      ∀ Φ, IsThetaFunO ψ A B' Φ → ∀ f ∈ π, LiftConv ω' m Φ f → thetaLift ω' m Φ f = 0

end GlobalTheory.RallisIP

namespace GlobalTheory.Published

open GlobalTheory.RallisIP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause)

def RallisInnerProductConvergent : Prop :=
  ∀ (D : D7) (A B : HSp D), A.rank < B.rank → B.rank ≤ 2 * A.rank →
    (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
    (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
    (ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ A B χA χB ω → IsWeilDatumO ψ (dblSp A) B 1 χB ωd → ThetaClause ψ A B χB ω ωd →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ (θ : InfF D) (C : CptF A), IsInfFam θ → A.SigOK → IsCartanFrame A C →
  ∀ (m : Measure (GA D A)) [m.IsHaarMeasure] [m.IsMulRightInvariant] (mH : Measure (GA D B)), mH.IsHaarMeasure →
  ∀ U : Submodule ℂ (DividedPowerChartLift A m), IsIrredSubrep (RG A m) U → U ≤ L2cusp A m →
    LowerLiftsZero m ψ B χA χB (AutMult.formsIn A m (A0 θ A C) U) →
  ∀ Φ₁ Φ₂, IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → IsKFinVec ωd (Khat A a) (delta A B Φ₁ Φ₂) →
  ∀ f₁ ∈ AutMult.formsIn A m (A0 θ A C) U, ∀ f₂ ∈ AutMult.formsIn A m (A0 θ A C) U,
    (LiftConv ω m Φ₁ f₁ ∧ MemL2Quotient (GQ B) mH (thetaLift ω m Φ₁ f₁)) ∧
    (LiftConv ω m Φ₂ f₂ ∧ MemL2Quotient (GQ B) mH (thetaLift ω m Φ₂ f₂)) ∧
    ZetaValueAt A χB⁻¹ m (flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B)) f₁ f₂ (sZero A B)
      ((((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ * petersson B mH (thetaLift ω m Φ₁ f₁) (thetaLift ω m Φ₂ f₂))

end GlobalTheory.Published

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D}

theorem wittIdx_eq_wittIndex (B : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx B = wittIndex B := by
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx wittIndex
  congr 1
  ext k
  refine exists_congr fun W => and_comm.trans (and_congr_left' ⟨fun h y hy => mem_perp.2 fun x hx => ?_, fun h x hx y hy => ?_⟩)
  · exact h x hx y hy
  · exact mem_perp.1 (h hy) x hx

theorem exists_lower_iff {i : ℕ} : (∃ B' : HSp D, IsWittLower B B' i ∧ B'.SigOK) ↔ i ≤ Formalism.MainNotions.SchurIrreducible.wittIdx B := by
  rw [wittIdx_eq_wittIndex]; exact exists_isWittLower_iff

theorem lowerLiftsZero_of_wittIdx_eq_zero (h : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0) (m : Measure (GA D A)) (ψ : AddChar (AF D.host.F) ℂ)
    (χA χB : (AE D)ˣ →* Circle) (π : Submodule ℂ (GA D A → ℂ)) : LowerLiftsZero m ψ B χA χB π := fun i B' hi h1 h2 => by
  have := exists_lower_iff.1 ⟨B', h1, h2⟩
  omega

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)} {Φ : WO A B → ℂ} {f : GA D A → ℂ}

theorem thetaLift_smul (c : ℂ) : thetaLift ω m Φ (c • f) = conj c • thetaLift ω m Φ f := funext fun h => by
  simp only [thetaLift, Pi.smul_apply, smul_eq_mul]
  rw [← petersson_conj_symm, petersson_smul_left, map_mul, petersson_conj_symm]

example (D : D7) : ∃ A B : HSp D, A.SigOK ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
    A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧ ∀ τ, B.SigOK ∧ B.sig τ = (8, 1) := by
  have h := Examples₂.lorentzSpace_signature_ok (E := D.host.E) Examples₂.star_isIntegral
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral) ≤ 1 :=
    (WittSignature.wittIdx_le_signature _ _ h D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  exact ⟨Examples₂.posSpace Examples₂.star_isIntegral 5, Examples₂.lorentzSpace Examples₂.star_isIntegral, Examples₂.posSpace_sigOK _ 5, (by decide : 5 < 8 + 1), (by decide : 8 + 1 ≤ 2 * 5),
    (Nat.add_le_add_left h1 5).trans_lt (by decide : 5 + 1 < 8 + 1), fun _ => ⟨h, rfl⟩⟩

end GlobalTheory.RallisIP

end
