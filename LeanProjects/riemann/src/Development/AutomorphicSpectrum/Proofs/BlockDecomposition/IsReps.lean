import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.FourierExpansionCentral
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

variable {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} {v : Pl}

def K1 (K : Type) [Field K] [NumberField K] : Subgroup Kˣ := (Units.map (Algebra.norm ℚ : K →* ℚ)).ker

def atW (w : PlK K) (κ : Kˣ) : (Kv K w)ˣ := Units.map (algebraMap K (Kv K w)).toMonoidHom κ

def cK (c : HeckeCharacter K) (w : PlK K) (κ : Kˣ) : ℂ := ((localChar c w (atW w κ) : ℂˣ) : ℂ)

def nv (v : Pl) (κ : Kˣ) : (Qv v)ˣ := Ad3.R.lc v (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ))

def embU (κ : Kˣ) : ℂˣ := Units.map ((Classical.arbitrary (InfinitePlace K)).embedding).toMonoidHom κ

def e1 : LM c v → K → Qv v
  | LM.sp w₁ _ _ => fun ξ => dg1 v w₁ ξ
  | LM.ns .. => fun _ => 1

open Classical in

def k1 (L : LM c v) (κ : Kˣ) : (Qv v)ˣ := if h : e1 L (κ : K) = 0 then 1 else Units.mk0 _ h

def cW : LM c v → Kˣ → ℂ
  | LM.sp w₁ w₂ _ => fun κ => cK c w₁ κ * cK c w₂ κ
  | LM.ns w .. => fun κ => cK c w κ

def c0 : LM c v → Kˣ → ℂ
  | LM.sp w₁ _ _ => fun κ => ((cAt c v w₁ (nv v κ) : ℂˣ) : ℂ)
  | LM.ns w .. => fun κ => cK c w κ

def fL (L : LM c v) (g : GL (Fin 2) (Qv v)) (ξ : K) (x : (Qv v)ˣ) : ℂ := L.ct x * (L.tw x).val g ξ

def locI (L : LM c v) (g : GL (Fin 2) (Qv v)) (ξ : K) : ℂ :=
  match L with
  | LM.sp .. => ∫ x, fL L g ξ x ∂multHaar (Qv v)
  | LM.ns .. => L.val g ξ

open Classical in

def locF (Sp : Pl → Prop) (f : ∀ v : Pl, (Qv v)ˣ → ℂ) (v : Pl) : ℂ :=
  if Sp v then ∫ x, f v x ∂multHaar (Qv v) else f v 1

open Classical in

def vK (M : ∀ v : Pl, LM c v) (κ : Kˣ) : Pl →₀ ℤ :=
  if h : (Function.support fun v : Pl => ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)).Finite then
    Finsupp.ofSupportFinite _ h else 0

def Tm (M : ∀ v : Pl, LM c v) : AddSubgroup (Pl →₀ ℤ) where
  carrier := {m | ∀ v, m v ≠ 0 → (M v).IsSp}
  zero_mem' := fun v h => absurd rfl h
  add_mem' := by
    intro a b ha hb v h
    by_cases h1 : a v = 0
    · exact hb v (fun h2 => h (by simp [h1, h2]))
    · exact ha v h1
  neg_mem' := by
    intro a ha v h
    exact ha v (fun h1 => h (by simp [h1]))

def IsReps (M : ∀ v : Pl, LM c v) (R : Finset (Pl →₀ ℤ)) : Prop :=
  (∀ r ∈ R, r ∈ Tm M) ∧ ∀ m ∈ Tm M, ∃! r, r ∈ R ∧ ∃ κ ∈ K1 K, m = r + vK M κ

def GoodSv (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) : Prop :=
  (∀ v ∈ Sv, (M v).IsSp) ∧ ∀ v ∉ Sv, (M v).IsSp → Unr c v ∧ (M v).std

def aT (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (g : G2) (m : Pl →₀ ℤ) (ξ : K) : ℂ :=
  ∫ u, ctM M Sv m u * thT n t (twM M Sv m u) g ξ ∂muU Sv

end GlobalTheory.CompanionTheory.FexTheta
