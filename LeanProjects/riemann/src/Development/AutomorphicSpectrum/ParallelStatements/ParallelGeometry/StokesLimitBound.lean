import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.StokesLimitBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Integrals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def PtsIntegrable {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  (∃ L : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P L) ∧
    ∀ L : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P L →
      Integrable (fun y : Fin e → ℂ => ∑ᶠ w ∈ fibre P L y, sheetDensity P L φ g y w)

end Integrals

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D)
  {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
  {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd))

def Ties : Prop :=
  S.IsTied ∧ S'.IsTied ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), S'.ref.h z = S.ref.h z

def CuspWeightDefined : Prop :=
  ∀ z ∈ D.Xo, BddAbove {x : ℝ | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧
    x = -Real.log (Cd.Nz z I)}

def MeanDefined : Prop :=
  PtsIntegrable (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) (fun _ => 1) ∧ 0 < degMu H ∧
    PtsIntegrable (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight

def SmoothAtSmallScale (B : ℕ) : Prop :=
  (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg H S B t)) ∧
    ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ), IsSmoothHerm (MUc H S' B p q t')

def RegBoundAt (B : ℕ) (a : ℝ) (p q : ℕ) (t' : ℝ) : Prop :=
  ((D.n : ℝ) + 1) * (a - (p : ℝ) / (q : ℝ) * D.KA) * geomDegMUc H S' B p q t' ≤ topMUc H S' B p q t'

def RegBound (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ), RegBoundAt H Cd S' B a p q t'

def RegBoundUnit (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∀ t' : ℝ, 0 < t' → t' ≤ 1 → RegBoundAt H Cd S' B a p q t'

def LimitBound (B : ℕ) (a : ℝ) : Prop :=
  ((D.n : ℝ) + 1) * (a - meanU H Cd / 2) * degMu H ≤ arLim H S B

theorem RegBoundUnit.regBound {B : ℕ} {a : ℝ} (h : RegBoundUnit H Cd S' B a) : RegBound H Cd S' B a := by
  intro p q hp hpq
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact h p q hp hpq t ht.1 ht.2

theorem limitBound_iff (hd : 0 < degMu H) (B : ℕ) (a : ℝ) :
    LimitBound H Cd S B a ↔ ((D.n : ℝ) + 1) * (a * degMu H -
      ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight / 2) ≤ arLim H S B := by
  have : ((D.n : ℝ) + 1) * (a - meanU H Cd / 2) * degMu H = ((D.n : ℝ) + 1) * (a * degMu H -
      ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight / 2) := by
    unfold meanU
    field_simp
  rw [LimitBound, this]

end Clauses

def StokesLimit : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D)
    (O abelian₂ : Type) [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)),
    Ties H Cd S S' → CuspWeightDefined Cd → MeanDefined H Cd →
    ∀ (B : ℕ) (a : ℝ), 4 * D.f + 2 ≤ B → SmoothAtSmallScale H Cd S S' B → ArLimExists H S B →
      RegBound H Cd S' B a → LimitBound H Cd S B a

def StokesLimitUnguarded : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D)
    (O abelian₂ : Type) [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)),
    S.IsTied → S'.IsTied →
    ∀ (B : ℕ) (a : ℝ), 4 * D.f + 2 ≤ B → ArLimExists H S B →
      RegBound H Cd S' B a → LimitBound H Cd S B a

theorem StokesLimitUnguarded.stokesLimit (h : StokesLimitUnguarded) : StokesLimit :=
  fun II hII Ψ _ K _ ι _ Ω _ _ E _ _ D H O abelian₂ _ _ _ Cd M S S' hT _ _ B a hB _ hL hR =>
    h II hII Ψ K ι Ω E D H O abelian₂ Cd M S S' hT.1 hT.2.1 B a hB hL hR

example (II : IntersectionSystem) (hII) :
    Ties (Line.lineHodge II hII) (Line.gaussCusp II hII) (Line.lineRegT II hII) (Line.lineBRegC II hII) ∧
      CuspWeightDefined (Line.gaussCusp II hII) := by
  refine ⟨⟨Line.lineRegT_tied II hII, Line.lineBRegC_tied II hII, fun _ _ => rfl⟩, fun z _ => ⟨0, ?_⟩⟩
  rintro x ⟨I, hI, -, hiso, -⟩
  exact absurd ((Submodule.eq_bot_iff I).2 fun v hv => Line.eq_zero_of_isIsoSub hiso hv) hI

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.StokesLimitBound
