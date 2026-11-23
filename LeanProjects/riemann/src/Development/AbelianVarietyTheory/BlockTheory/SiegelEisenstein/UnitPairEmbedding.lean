import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod (Place Dbl IsOne ofSplit)
open GlobalTheory.FinPl (SplitPt grpAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes

section One
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def volK {a : Type} [Fintype a] [DecidableEq a] (J : Subgroup (GL a k)) : ℝ :=
  ((KO k a).relIndex J : ℝ) / (J.relIndex (KO k a) : ℝ)

def IsCptOpen {a : Type} [Fintype a] [DecidableEq a] (J : Subgroup (GL a k)) : Prop :=
  IsOpen (J : Set (GL a k)) ∧ IsCompact (J : Set (GL a k))

variable [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def RowComb (ψ : AddChar k Circle) (ν : Measure k) (P : ℕ) (Q : GlobalTheory.StepData.Level (GL (n ⊕ Fin c) k))
    (h : GL (n ⊕ Fin c) k) (e : GL (n ⊕ Fin c) k →₀ ℂ) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A), IsSmoothRep σ →
    ∀ L : A →ₗ[ℂ] ℂ, GlobalTheory.RootEx.IsNEquiv ψ P σ L → ∀ v : A, (∀ x : Q.J, σ x v = (Q.lam x : ℂ) • v) →
      GlobalTheory.PosOne.toOne ν σ P L (σ h v) = GlobalTheory.PosOne.comb e fun g => L (σ (g * h) v)

example {a : Type} [Fintype a] [DecidableEq a] : volK (KO k a) = 1 := by simp [volK]

example (ψ : AddChar k Circle) (ν : Measure k) (Q : GlobalTheory.StepData.Level (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) :
    RowComb ψ ν 1 Q h (Finsupp.single 1 1) := fun A _ _ σ _ L _ v _ => by
  rw [GlobalTheory.PosOne.toOne_one, GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]
  simp

end One

section Many
variable {D : D7} {I : Type} [Fintype I] [DecidableEq I] {k : I → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
  [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def places (q : ∀ i, SplitPt D (k i)) (v : GlobalTheory.FinPl.Pl D) : Prop := ∃ i, (q i).v = v

def IsEmb (q : ∀ i, SplitPt D (k i)) (V : HSp D) (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank Y)
    (ι : (∀ i, GL Y (k i)) → GA D V) : Prop :=
  ∀ x, ι x ∈ grpAt V (places q) ∧ ∀ i, (mt V (ι x)).map (q i).pr = (F i).β * (x i).val * (F i).γ

def intPts {V : HSp D} (ι : (∀ i, GL Y (k i)) → GA D V) : Set (GA D V) := {h | ∃ x, (∀ i, x i ∈ KO (k i) Y) ∧ ι x = h}

def IsUnitPair {V : HSp D} (G R : Subgroup (GA D V)) (K : Set (GA D V)) (ρ : Measure (R.subgroupOf G)) (μ : Measure G) : Prop :=
  μ.IsHaarMeasure ∧ μ {h | h.1 ∈ K} = 1 ∧ ρ.IsHaarMeasure ∧ ρ {r | r.1.1 ∈ K} = 1

def prodComb {V : HSp D} (ι : (∀ i, GL Y (k i)) → GA D V) (e : ∀ i, GL Y (k i) →₀ ℂ) (h : ∀ i, GL Y (k i)) : GA D V →₀ ℂ :=
  ∑ g ∈ Fintype.piFinset fun i => (e i).support, Finsupp.single (ι (g * h)) (∏ i, e i (g i))

def IsVac (q : ∀ i, SplitPt D (k i)) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}
    (FS : ∀ i, GlobalTheory.LocMod.Frame (k i) S.rank Y') (FT : ∀ i, GlobalTheory.LocMod.Frame (k i) T.rank Y) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ i, ∃ Tm, (ofSplit (q i)).IsModel ψ (FS i) (FT i) Tm ∧ ∀ O, IsOne O → Tm O = f

def put (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (d : I → WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  (Finset.univ : Finset I).toList.foldr (fun i f' => GlobalTheory.SeeSaw.comb ψ S T (d i) f') f

def biPut (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (d : I → WO A S →₀ ℂ) (d' : I → WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  (Finset.univ : Finset I).toList.foldr (fun i C' => biComb ψ A S A' (d i) (d' i) C') C

end Many

def DoubleAtOne (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (χ₁ χ₂ χz : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omb : Om J.W₀ B'.A),
    s₁.χV = χ₁ * χz → s₁.χW = χ₁ → s₂.χV = χ₂ → s₂.χW = χ₂ * χz →
    IsWeilDatumO ψ B.A J.W₀ χ₁ χ₁ oma → IsWeilDatumO ψ J.W₀ B'.A χ₂ χ₂ omb →

  ∀ (I : Type) [Fintype I] [DecidableEq I] (k : I → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] [∀ i, MeasurableSpace (k i)] [∀ i, BorelSpace (k i)]
    (q : ∀ i, SplitPt D (k i)), (Function.Injective fun i => (q i).v) →
  ∀ (ψk : ∀ i, AddChar (k i) Circle) (ν : ∀ i, Measure (k i)) (μ₁ μ₂ : ∀ i, (k i)ˣ →* ℂˣ),
    (∀ i, (ofSplit (q i)).IsChar ψ (ψk i) ∧ HasConductor (ψk i) 1 ∧ IsUnitVol (ν i) ∧
      (ofSplit (q i)).IsComp χ₁⁻¹ (μ₁ i) ∧ (ofSplit (q i)).IsComp χ₂⁻¹ (μ₂ i)) →

  ∀ (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c : ℕ)
    (F : ∀ i, Dbl (ofSplit (q i)) B J B' n₀ n₁ n₂ c)
    (ι₀ : (∀ i, GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) (k i)) → GA D B.V) (ι₁ : (∀ i, GL (n₁ ⊕ Fin (c + 1 + 1)) (k i)) → GA D J.W)
    (ι₂ : (∀ i, GL (n₂ ⊕ Fin (c + 1)) (k i)) → GA D B'.V),
    IsEmb q B.V (fun i => (F i).G₀) ι₀ → IsEmb q J.W (fun i => (F i).G₁) ι₁ → IsEmb q B'.V (fun i => (F i).G₂) ι₂ →
  ∀ (m₁ : Measure (grpAt J.W (places q))) (ρ₁ : Measure ((jacGrp J.d).subgroupOf (grpAt J.W (places q))))
    (m₂ : Measure (grpAt B'.V (places q))) (ρ₂ : Measure ((besGrp B'.d B'.o).subgroupOf (grpAt B'.V (places q)))),
    IsUnitPair _ (jacGrp J.d) (intPts ι₁) ρ₁ m₁ → IsUnitPair _ (besGrp B'.d B'.o) (intPts ι₂) ρ₂ m₂ →

  ∀ (P₀ : ∀ i, GlobalTheory.StepData.Level (GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) (k i)))
    (P₁ : ∀ i, GlobalTheory.StepData.Level (GL (n₁ ⊕ Fin (c + 1 + 1)) (k i)))
    (P₂ : ∀ i, GlobalTheory.StepData.Level (GL (n₂ ⊕ Fin (c + 1)) (k i)))
    (Φ₁ : ∀ i, SB (Matrix (n₁ ⊕ Fin (c + 1 + 1)) (n₀ ⊕ Fin (c + 1 + 1 + 1)) (k i)))
    (Φ₂ : ∀ i, SB (Matrix (n₂ ⊕ Fin (c + 1)) (n₁ ⊕ Fin (c + 1 + 1)) (k i))),
    (∀ i, IsCptOpen (P₁ i).J ∧ IsCptOpen (P₂ i).J ∧ GlobalTheory.StepData.HasTypes (μ₁ i) (P₀ i) (P₁ i) (Φ₁ i).1 ∧
      GlobalTheory.StepData.HasTypes (μ₂ i) (P₁ i) (P₂ i) (Φ₂ i).1) →
  ∀ (f₁ : WO B.V J.W → ℂ) (f₂ : WO J.W B'.V → ℂ) (d₁ : I → WO B.V J.W →₀ ℂ) (d₂ : I → WO J.W B'.V →₀ ℂ),
    IsVac q ψ (fun i => (F i).G₀) (fun i => (F i).G₁) f₁ → IsVac q ψ (fun i => (F i).G₁) (fun i => (F i).G₂) f₂ →
    (∀ i, (ofSplit (q i)).IsCombAt ψ (F i).G₀ (F i).G₁ (d₁ i) (Φ₁ i).1 ∧
      (ofSplit (q i)).IsCombAt ψ (F i).G₁ (F i).G₂ (d₂ i) (Φ₂ i).1) →

  ∀ (a : ∀ i, GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) (k i)) (e₀ : ∀ i, GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) (k i) →₀ ℂ),
    (∀ i, ∃ ρ', GlobalTheory.PosOne.IsSrc (μ₁ i) ρ' ∧ GlobalTheory.PosOne.SrcComb (ψk i) (ν i) (σ + 2) ρ' (ρ' (a i) (Φ₁ i)) (e₀ i)) →

  ∀ (T₁ : ∀ i, Finset (GL (n₁ ⊕ Fin (c + 1 + 1)) (k i))) (T₂ : ∀ i, Finset (GL (n₂ ⊕ Fin (c + 1)) (k i))),
    (∀ i, GlobalTheory.PosOne.Covers 1 (P₁ i).J (T₁ i) (GlobalTheory.StepData.flat (ψk i) (ν i) (μ₁ i) (Φ₁ i).1 (a i)) ∧
      ∀ β ∈ T₁ i, GlobalTheory.PosOne.Covers 1 (P₂ i).J (T₂ i) (GlobalTheory.StepData.flat (ψk i) (ν i) (μ₂ i) (Φ₂ i).1 β)) →

  ∀ (x₁ : ∀ i, GL (n₁ ⊕ Fin (c + 1 + 1)) (k i) → WO B.A J.W₀ →₀ ℂ)
    (x₂ : ∀ i, GL (n₁ ⊕ Fin (c + 1 + 1)) (k i) → GL (n₂ ⊕ Fin (c + 1)) (k i) → WO J.W₀ B'.A →₀ ℂ)
    (e₂ : ∀ i, GL (n₂ ⊕ Fin (c + 1)) (k i) → GL (n₂ ⊕ Fin (c + 1)) (k i) →₀ ℂ),
    (∀ i, ∀ β ∈ T₁ i, (ofSplit (q i)).IsCombAt ψ (F i).F₀ (F i).F₁ (x₁ i β)
      (GlobalTheory.StepData.xi (ψk i) (ν i) (μ₁ i) (Φ₁ i).1 (P₁ i).J 1 (a i) β)) →
    (∀ i, ∀ β ∈ T₁ i, ∀ γ ∈ T₂ i, (ofSplit (q i)).IsCombAt ψ (F i).F₁ (F i).F₂ (x₂ i β γ)
      (GlobalTheory.StepData.xi (ψk i) (ν i) (μ₂ i) (Φ₂ i).1 (P₂ i).J 1 β γ)) →
    (∀ i, ∀ γ ∈ T₂ i, RowComb (ψk i) (ν i) (σ + 1) (P₂ i) γ (e₂ i γ)) →

  ∀ (φ : GA D B.A → ℂ) (f : GA D B'.V → ℂ), IsContAut B.A φ → IsContAut B'.V f →
    (∀ x : ∀ i, (P₂ i).J, rTrans (ι₂ fun i => (x i).1) f = (∏ i, ((P₂ i).lam (x i) : ℂ)) • f) →
    Iter2 ρ₁ m₁ ρ₂ m₂
      (fun h₁ h₂ => (prodComb ι₀ e₀ a).sum fun g w => w *
        B'.per ψ (biLift oma omb B.vA J.v0 φ (GlobalTheory.Unf.contr l J.W₀ vL
          (flatBF s₁ (s₁.om (g, h₁.1) (put ψ d₁ f₁))) (flatFB s₂ (s₂.om (h₁.1, h₂.1) (put ψ d₂ f₂))))) (rTrans h₂.1 f))
      ((∏ i, ((volK (P₁ i).J * volK (P₂ i).J : ℝ) : ℂ)) *
        ∑ β ∈ Fintype.piFinset T₁, ∑ γ ∈ Fintype.piFinset T₂,
          (∏ i, (((volK (GlobalTheory.StepData.prX (GlobalTheory.StepData.Cgrp (P₁ i).J (β i))))⁻¹ *
            (volK (GlobalTheory.StepData.prX (GlobalTheory.StepData.Cgrp (P₂ i).J (γ i))))⁻¹ : ℝ) : ℂ)) *
          B'.per ψ (biLift oma omb B.vA J.v0 φ (biPut ψ (fun i => x₁ i (β i)) (fun i => x₂ i (β i) (γ i))
              (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ f₁) (flatFB s₂ f₂))))
            (trc (prodComb ι₂ (fun i => e₂ i (γ i)) γ) f))

end GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes
end
