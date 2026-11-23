import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv pri dia2)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

def piRc (cf : ℂˣ → ℂ) (g : GL (Fin 2) ℝ) (Φ : ℂ → ℂ) (x : ℂ) : ℂ :=
  if h : 0 < (g.val).det then
    cf (Units.mk0 ((Real.sqrt (g.val).det : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr h).ne')) *
      ((Real.sqrt (g.val).det : ℝ) : ℂ) *
      rWR (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun y => Φ (y * ((Real.sqrt (g.val).det : ℝ) : ℂ))) x
  else 0

variable (K) in

def embC (ξ : K) : ℂ := (Classical.arbitrary (InfinitePlace K)).embedding ξ

def dg1 (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] (ξ : K) : Qv v :=
  Function.invFun (algebraMap (Qv v) (Kv K w)) (algebraMap K (Kv K w) ξ)

inductive LM (c : HeckeCharacter K) (v : Pl) : Type
  | sp (w₁ w₂ : PlK K) [h₁ : w₁.asIdeal.LiesOver v.asIdeal] [h₂ : w₂.asIdeal.LiesOver v.asIdeal]
      (Φ : Qv v × Qv v → ℂ) : LM c v
  | ns (w : PlK K) [h : w.asIdeal.LiesOver v.asIdeal] (σ : Kv K w ≃ₐ[Qv v] Kv K w) (η : (Qv v)ˣ →* ℂˣ)
      (Φ : Kv K w → ℂ) : LM c v

namespace LM

variable {c : HeckeCharacter K} {v : Pl}

def ok : LM c v → Prop
  | sp w₁ w₂ Φ => w₁ ≠ w₂ ∧ IsLocallyConstant Φ ∧ HasCompactSupport Φ
  | ns w σ η Φ => (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) ∧ σ ≠ AlgEquiv.refl ∧
      (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg (Kv K w) (a : Qv v)) ∧ Φ ∈ GL2LocalData.SBc (Qv v) (Kv K w) (localChar c w)

def std : LM c v → Prop
  | sp _ _ Φ => Φ = Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1
  | ns w _ _ Φ => Φ = Set.indicator {x : Kv K w | x ∈ 𝒪[Kv K w]} 1

def IsSp : LM c v → Prop
  | sp .. => True
  | ns .. => False

def W : LM c v → GL (Fin 2) (Qv v) → ℂ
  | sp w₁ w₂ Φ => GL2LocalData.WcS (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) Φ
  | ns w σ η Φ => GL2LocalData.Wc (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
      (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) Φ

def val : LM c v → GL (Fin 2) (Qv v) → K → ℂ
  | sp w₁ w₂ Φ => fun g ξ => GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g Φ (dg1 v w₁ ξ, dg1 v w₂ ξ)
  | ns w σ η Φ => fun g ξ => GL2LocalData.piG (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
      (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) g Φ (algebraMap K (Kv K w) ξ)

def plus : LM c v → GL (Fin 2) (Qv v) → Prop
  | sp .. => fun _ => True
  | ns w _ _ _ => fun g => ∃ t : (Kv K w)ˣ, Algebra.norm (Qv v) (t : Kv K w) = (g.val).det

def tw : LM c v → (Qv v)ˣ → LM c v
  | sp w₁ w₂ Φ => fun u => sp w₁ w₂ (fun x => Φ (x * ((u : Qv v), ((u⁻¹ : (Qv v)ˣ) : Qv v))))
  | ns w σ η Φ => fun _ => ns w σ η Φ

def ct : LM c v → (Qv v)ˣ → ℂ
  | sp w₁ w₂ _ => fun u => ((cAt c v w₁ u * (cAt c v w₂ u)⁻¹ : ℂˣ) : ℂ)
  | ns .. => fun _ => 1

end LM

def Gp {c : HeckeCharacter K} (M : ∀ v : Pl, LM c v) : Set G2 :=
  {g | (∀ v, (M v).plus (finAt v g)) ∧ 0 < ((GL2Classical.realPart g).val).det}

def thT {c : HeckeCharacter K} (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (g : G2) (ξ : K) : ℂ :=
  piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K ξ) * ∏ᶠ v, (M v).val (finAt v g) ξ

def thP {c : HeckeCharacter K} (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (g : G2) : ℂ :=
  ∑' ξ : K, thT n t M g ξ

def AdmM {c : HeckeCharacter K} (M : ∀ v : Pl, LM c v) : Prop :=
  (∀ v, (M v).ok) ∧ ∃ S0 : Finset Pl, ∀ v ∉ S0, Unr c v ∧ (M v).std

variable (K) in

def THS : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M →
    ∀ γ : GL (Fin 2) ℚ, (γ.val).det = 1 → ∀ g ∈ Gp M, thP n t M (dia2 γ * g) = thP n t M g

def unQ (v : Pl) : Set (Qv v)ˣ := {u | (u : Qv v) ∈ 𝒪[Qv v] ∧ ((u⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v]}

def muU (Sv : Finset Pl) : Measure (∀ v : Sv, (Qv v.1)ˣ) := Measure.pi fun v => (multHaar (Qv v.1)).restrict (unQ v.1)

open Classical in

def tu (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (v : Pl) : (Qv v)ˣ :=
  unifUnit (Qv v) ^ (m v) * (if h : v ∈ Sv then u ⟨v, h⟩ else 1)

def twM {c : HeckeCharacter K} (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) :
    ∀ v : Pl, LM c v := fun v => (M v).tw (tu Sv m u v)

open Classical in

def ctM {c : HeckeCharacter K} (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) : ℂ :=
  ∏ v ∈ m.support ∪ Sv, (M v).ct (tu Sv m u v)

def thA {c : HeckeCharacter K} (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v)
    (g : G2) : ℂ :=
  ∑ m ∈ R, ∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv

def th0 {c : HeckeCharacter K} (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v)
    (g : G2) : ℂ :=
  ∑ m ∈ R, ∫ u, ctM M Sv m u * thT n t (twM M Sv m u) g 0 ∂muU Sv

def WM {c : HeckeCharacter K} (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) : G2 → ℂ :=
  pw2 (WcR (chC n (Complex.I * t)) (PhiInf n)) (fun v => (M v).W)

variable (K) in

def MEX : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ)
  (S0 : Finset Pl), (∀ v ∈ S0, PureTh c v (Wtf v)) → (∀ v ∉ S0, Unr c v ∧ StdTh c v (Wtf v)) →
    ∃ M : ∀ v : Pl, LM c v, AdmM M ∧ ∀ v, (M v).W = Wtf v

variable (K) in

def AVG : Prop := THS K → Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ R Sv, ∀ γ : GL (Fin 2) ℚ, (γ.val).det = 1 → ∀ g ∈ Gp M,
    thA R Sv n t M (dia2 γ * g) = thA R Sv n t M g

variable (K) in

def FEX : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∃ (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (κ₀ : ℂ), κ₀ ≠ 0 ∧ ∀ g ∈ Gp M,
    HasSum (fun α : ℚˣ => κ₀ * WM n t M (dg2 (pri α) 1 * g)) (thA R Sv n t M g - th0 R Sv n t M g) ∧
    (∀ x : 𝔸[ℚ], th0 R Sv n t M (uni2 x * g) = th0 R Sv n t M g) ∧
    (∀ κ : Kˣ, th0 R Sv n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) = th0 R Sv n t M g) ∧
    (∀ z : ℚˣ, th0 R Sv n t M (dg2 (pri z) (pri z) * g) = th0 R Sv n t M g)

end Ad3.K.QuadraticBaseChangeGL3.Th
