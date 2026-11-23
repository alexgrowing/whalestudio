import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnitPairEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReindexIff

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open GlobalTheory.FinPl (SplitPt grpAt grpOff)
open GlobalTheory.SymCompare (sE)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes (places IsUnitPair put biPut volK IsCptOpen RowComb)

namespace GlobalTheory.QCmp

section Many
variable {D : D7} {I : Type} [Fintype I] [DecidableEq I] {k : I → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
  [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
variable {Y Y' : I → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] [∀ i, Fintype (Y' i)] [∀ i, DecidableEq (Y' i)]

def Emb (q : ∀ i, SplitPt D (k i)) (V : HSp D) (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i))
    (ι : (∀ i, GL (Y i) (k i)) → GA D V) : Prop :=
  ∀ x, ι x ∈ grpAt V (places q) ∧ ∀ i, (mt V (ι x)).map (q i).pr = (F i).β * (x i).val * (F i).γ

def intP {V : HSp D} (ι : (∀ i, GL (Y i) (k i)) → GA D V) : Set (GA D V) := {h | ∃ x, (∀ i, x i ∈ KO (k i) (Y i)) ∧ ι x = h}

def prodC {V : HSp D} (ι : (∀ i, GL (Y i) (k i)) → GA D V) (e : ∀ i, GL (Y i) (k i) →₀ ℂ) (h : ∀ i, GL (Y i) (k i)) :
    GA D V →₀ ℂ :=
  ∑ g ∈ Fintype.piFinset fun i => (e i).support, Finsupp.single (ι (g * h)) (∏ i, e i (g i))

def Vacs (q : ∀ i, SplitPt D (k i)) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}
    (FS : ∀ i, GlobalTheory.LocMod.Frame (k i) S.rank (Y' i)) (FT : ∀ i, GlobalTheory.LocMod.Frame (k i) T.rank (Y i)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ i, ∃ Tm, (ofSplit (q i)).IsModel ψ (FS i) (FT i) Tm ∧ ∀ O, IsOne O → Tm O = f

end Many

def AtOneIdx (D : D7) (I : Type) [Fintype I] [DecidableEq I] (n₀ n₁ n₂ : I → Type) [∀ i, Fintype (n₀ i)]
    [∀ i, DecidableEq (n₀ i)] [∀ i, Fintype (n₁ i)] [∀ i, DecidableEq (n₁ i)] [∀ i, Fintype (n₂ i)] [∀ i, DecidableEq (n₂ i)]
    (c : I → ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (χ₁ χ₂ χz : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omb : Om J.W₀ B'.A),
    s₁.χV = χ₁ * χz → s₁.χW = χ₁ → s₂.χV = χ₂ → s₂.χW = χ₂ * χz →
    IsWeilDatumO ψ B.A J.W₀ χ₁ χ₁ oma → IsWeilDatumO ψ J.W₀ B'.A χ₂ χ₂ omb →

  ∀ (k : I → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] [∀ i, MeasurableSpace (k i)] [∀ i, BorelSpace (k i)]
    (q : ∀ i, SplitPt D (k i)), (Function.Injective fun i => (q i).v) →
  ∀ (ψk : ∀ i, AddChar (k i) Circle) (ν : ∀ i, Measure (k i)) (μ₁ μ₂ : ∀ i, (k i)ˣ →* ℂˣ),
    (∀ i, (ofSplit (q i)).IsChar ψ (ψk i) ∧ HasConductor (ψk i) 1 ∧ IsUnitVol (ν i) ∧
      (ofSplit (q i)).IsComp χ₁⁻¹ (μ₁ i) ∧ (ofSplit (q i)).IsComp χ₂⁻¹ (μ₂ i)) →

  ∀ (F : ∀ i, Dbl (ofSplit (q i)) B J B' (n₀ i) (n₁ i) (n₂ i) (c i))
    (ι₀ : (∀ i, GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)) → GA D B.V) (ι₁ : (∀ i, GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i)) → GA D J.W)
    (ι₂ : (∀ i, GL (n₂ i ⊕ Fin (c i + 1)) (k i)) → GA D B'.V),
    Emb q B.V (fun i => (F i).G₀) ι₀ → Emb q J.W (fun i => (F i).G₁) ι₁ → Emb q B'.V (fun i => (F i).G₂) ι₂ →
  ∀ (m₁ : Measure (grpAt J.W (places q))) (ρ₁ : Measure ((jacGrp J.d).subgroupOf (grpAt J.W (places q))))
    (m₂ : Measure (grpAt B'.V (places q))) (ρ₂ : Measure ((besGrp B'.d B'.o).subgroupOf (grpAt B'.V (places q)))),
    IsUnitPair _ (jacGrp J.d) (intP ι₁) ρ₁ m₁ → IsUnitPair _ (besGrp B'.d B'.o) (intP ι₂) ρ₂ m₂ →

  ∀ (P₀ : ∀ i, GlobalTheory.StepData.Level (GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)))
    (P₁ : ∀ i, GlobalTheory.StepData.Level (GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i)))
    (P₂ : ∀ i, GlobalTheory.StepData.Level (GL (n₂ i ⊕ Fin (c i + 1)) (k i)))
    (Φ₁ : ∀ i, SB (Matrix (n₁ i ⊕ Fin (c i + 1 + 1)) (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)))
    (Φ₂ : ∀ i, SB (Matrix (n₂ i ⊕ Fin (c i + 1)) (n₁ i ⊕ Fin (c i + 1 + 1)) (k i))),
    (∀ i, ((P₁ i).J ≤ KO (k i) _ ∧ (P₂ i).J ≤ KO (k i) _) ∧ IsCptOpen (P₁ i).J ∧ IsCptOpen (P₂ i).J ∧
      GlobalTheory.StepData.HasTypes (μ₁ i) (P₀ i) (P₁ i) (Φ₁ i).1 ∧
      GlobalTheory.StepData.HasTypes (μ₂ i) (P₁ i) (P₂ i) (Φ₂ i).1) →
  ∀ (f₁ : WO B.V J.W → ℂ) (f₂ : WO J.W B'.V → ℂ) (d₁ : I → WO B.V J.W →₀ ℂ) (d₂ : I → WO J.W B'.V →₀ ℂ),
    Vacs q ψ (fun i => (F i).G₀) (fun i => (F i).G₁) f₁ → Vacs q ψ (fun i => (F i).G₁) (fun i => (F i).G₂) f₂ →
    (∀ i, (ofSplit (q i)).IsCombAt ψ (F i).G₀ (F i).G₁ (d₁ i) (Φ₁ i).1 ∧
      (ofSplit (q i)).IsCombAt ψ (F i).G₁ (F i).G₂ (d₂ i) (Φ₂ i).1) →

  ∀ (a : ∀ i, GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)) (e₀ : ∀ i, GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i) →₀ ℂ),
    (∀ i, RowComb (ψk i) (ν i) (σ + 2) (P₀ i) (a i) (e₀ i)) →

  ∀ (T₁ : ∀ i, Finset (GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i))) (T₂ : ∀ i, Finset (GL (n₂ i ⊕ Fin (c i + 1)) (k i))),
    (∀ i, GlobalTheory.PosOne.Covers 1 (P₁ i).J (T₁ i) (GlobalTheory.StepData.flat (ψk i) (ν i) (μ₁ i) (Φ₁ i).1 (a i)) ∧
      ∀ β ∈ T₁ i, GlobalTheory.PosOne.Covers 1 (P₂ i).J (T₂ i) (GlobalTheory.StepData.flat (ψk i) (ν i) (μ₂ i) (Φ₂ i).1 β)) →

  ∀ (x₁ : ∀ i, GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i) → WO B.A J.W₀ →₀ ℂ)
    (x₂ : ∀ i, GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i) → GL (n₂ i ⊕ Fin (c i + 1)) (k i) → WO J.W₀ B'.A →₀ ℂ)
    (e₂ : ∀ i, GL (n₂ i ⊕ Fin (c i + 1)) (k i) → GL (n₂ i ⊕ Fin (c i + 1)) (k i) →₀ ℂ),
    (∀ i, ∀ β ∈ T₁ i, (ofSplit (q i)).IsCombAt ψ (F i).F₀ (F i).F₁ (x₁ i β)
      (GlobalTheory.StepData.xi (ψk i) (ν i) (μ₁ i) (Φ₁ i).1 (P₁ i).J 1 (a i) β)) →
    (∀ i, ∀ β ∈ T₁ i, ∀ γ ∈ T₂ i, (ofSplit (q i)).IsCombAt ψ (F i).F₁ (F i).F₂ (x₂ i β γ)
      (GlobalTheory.StepData.xi (ψk i) (ν i) (μ₂ i) (Φ₂ i).1 (P₂ i).J 1 β γ)) →
    (∀ i, ∀ γ ∈ T₂ i, RowComb (ψk i) (ν i) (σ + 1) (P₂ i) γ (e₂ i γ)) →

  ∀ (φ : GA D B.A → ℂ) (f : GA D B'.V → ℂ), IsContAut B.A φ → IsContAut B'.V f →
    (∀ x : ∀ i, (P₂ i).J, rTrans (ι₂ fun i => (x i).1) f = (∏ i, ((P₂ i).lam (x i) : ℂ)) • f) →
    Iter2 ρ₁ m₁ ρ₂ m₂
      (fun h₁ h₂ => (prodC ι₀ e₀ a).sum fun g w => w *
        B'.per ψ (biLift oma omb B.vA J.v0 φ (GlobalTheory.Unf.contr l J.W₀ vL
          (flatBF s₁ (s₁.om (g, h₁.1) (put ψ d₁ f₁))) (flatFB s₂ (s₂.om (h₁.1, h₂.1) (put ψ d₂ f₂))))) (rTrans h₂.1 f))
      ((∏ i, ((volK (P₁ i).J * volK (P₂ i).J : ℝ) : ℂ)) *
        ∑ β ∈ Fintype.piFinset T₁, ∑ γ ∈ Fintype.piFinset T₂,
          (∏ i, (((volK (GlobalTheory.StepData.prX (GlobalTheory.StepData.Cgrp (P₁ i).J (β i))))⁻¹ *
            (volK (GlobalTheory.StepData.prX (GlobalTheory.StepData.Cgrp (P₂ i).J (γ i))))⁻¹ : ℝ) : ℂ)) *
          B'.per ψ (biLift oma omb B.vA J.v0 φ (biPut ψ (fun i => x₁ i (β i)) (fun i => x₂ i (β i) (γ i))
              (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ f₁) (flatFB s₂ f₂))))
            (trc (prodC ι₂ (fun i => e₂ i (γ i)) γ) f))

def AtOneInt (D : D7) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (c : ℕ), AtOneIdx D I (fun _ => n₀) (fun _ => n₁) (fun _ => n₂) fun _ => c

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def BaseAt {r : ℕ} (Q : Fin r → QStep S) : Prop :=
  ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ v, P v ↔ ∃ i, (Q i).q.v = v) →
  ∀ (μ₁ : Measure (grpAt S.J.W P)) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W P)))
    (μ₂ : Measure (grpAt S.B'.V P)) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V P))),
    μ₁.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₂.IsHaarMeasure → ρ₂.IsHaarMeasure →
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 → ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 →
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 → ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1 →
  ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → (∀ i, (Q i).Vac f₁ f₂) →
  ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → (∀ i, (Q i).Typed f) →
    Iter2 ρ₁ μ₁ ρ₂ μ₂
      (fun x y => GlobalTheory.QVal.integrand Q (Finsupp.single 0 1) (Finsupp.single 0 1) f₁ f₂ φ f 1 1 1 x.1 y.1)
      (GlobalTheory.QVal.value Q (Finsupp.single 0 1) (Finsupp.single 0 1) f₁ f₂ φ f 1 1 1)

def Same (Q Q' : QStep S) : Prop :=
  Q'.q.v = Q.q.v ∧ (∀ x, IntAt Q'.q.v Q'.gl₁ x ↔ IntAt Q.q.v Q.gl₁ x) ∧ (∀ x, IntAt Q'.q.v Q'.gl₂ x ↔ IntAt Q.q.v Q.gl₂ x) ∧
    Q'.D₁ = Q.D₁ ∧ Q'.D₂ = Q.D₂ ∧ Q'.e₀.mapDomain Q'.gl₀ = Q.e₀.mapDomain Q.gl₀ ∧ Q'.volJ = Q.volJ ∧
    (∀ f₁ f₂, Q.Vac f₁ f₂ → Q'.Vac f₁ f₂) ∧ (∀ f, Q.Typed f → Q'.Typed f) ∧
    ∃ (a : Q.A₁ ≃ Q'.A₁) (b : Q.A₂ ≃ Q'.A₂), (∀ γ, Q'.w₁ (a γ) = Q.w₁ γ ∧ Q'.d₁ (a γ) = Q.d₁ γ) ∧
      (∀ β, Q'.w₂ (b β) = Q.w₂ β ∧ (Q'.e₂ (b β)).mapDomain Q'.gl₂ = (Q.e₂ β).mapDomain Q.gl₂) ∧
      ∀ γ β, Q'.d₂ (a γ) (b β) = Q.d₂ γ β

theorem Same.refl (Q : QStep S) : Same Q Q :=
  ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, fun _ h => h, Equiv.refl _, Equiv.refl _,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

def reFrame {k : Type} [Field k] {N : ℕ} {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (F : GlobalTheory.LocMod.Frame k N Y) (e : Y ≃ Z) : GlobalTheory.LocMod.Frame k N Z where
  β := F.β.submatrix id e.symm
  γ := F.γ.submatrix e.symm id
  βγ := by rw [submatrix_mul_equiv, F.βγ, submatrix_id_id]
  γβ := by
    rw [show F.γ.submatrix e.symm id * F.β.submatrix id e.symm = (F.γ * F.β).submatrix e.symm e.symm from
      submatrix_mul_equiv _ _ _ (Equiv.refl _) _, F.γβ, submatrix_one_equiv]

end GlobalTheory.QCmp
end
