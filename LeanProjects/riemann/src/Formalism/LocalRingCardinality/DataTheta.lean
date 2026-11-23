import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG

noncomputable section

namespace Formalism.BasicNotions.TH

open Matrix MeasureTheory

abbrev Ix (p q : ℕ) := Fin p ⊕ Fin q

abbrev Mat (p q : ℕ) := Matrix (Ix p q) (Ix p q) ℂ

def Jm (p q : ℕ) : Mat p q := Formalism.UG.Jpq p q

def upq (p q : ℕ) : Set (Mat p q) := {X | Xᴴ * Jm p q + Jm p q * X = 0}

def sameBlock {p q : ℕ} : Ix p q → Ix p q → Prop
  | .inl _, .inl _ => True
  | .inr _, .inr _ => True
  | _, _ => False

instance {p q : ℕ} (a b : Ix p q) : Decidable (sameBlock a b) := by
  cases a <;> cases b <;> simp only [sameBlock] <;> infer_instance

def IsKC {p q : ℕ} (X : Mat p q) : Prop := ∀ a b, ¬ sameBlock a b → X a b = 0

def IsPC {p q : ℕ} (X : Mat p q) : Prop := ∀ a b, sameBlock a b → X a b = 0

def pR (p q : ℕ) : Set (Mat p q) := {X | X ∈ upq p q ∧ IsPC X}

def posC {p q : ℕ} : Ix p q → Ix p q → Prop
  | .inl i, .inl j => i < j
  | .inr i, .inr j => i < j
  | _, _ => False

def Eab {p q : ℕ} (a b : Ix p q) : Mat p q := Matrix.single a b 1

def hsNorm {p q : ℕ} (X : Mat p q) : ℝ := Real.sqrt (∑ a, ∑ b, ‖X a b‖ ^ 2)

def adjZ {p q : ℕ} (Z : Mat p q) : Mat p q := Jm p q * Zᴴ * Jm p q

def conjR {p q : ℕ} (Z : Mat p q) : Mat p q := -(adjZ Z)

section Modules

variable {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

def IsLieAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∀ X Y, act (X * Y - Y * X) = act X * act Y - act Y * act X

def wtSub (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) : Submodule ℂ V :=
  ⨅ a, LinearMap.ker (act (Eab a a) - ((μ a : ℚ) : ℂ) • LinearMap.id)

def hwSub (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) : Submodule ℂ V :=
  wtSub act μ ⊓ ⨅ a, ⨅ b, ⨅ (_ : posC a b), LinearMap.ker (act (Eab a b))

def IsHW (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ hwSub act μ

def KStable (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) : Prop :=
  ∀ X, IsKC X → ∀ w ∈ W, act X w ∈ W

def OfType (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) : Prop :=
  ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ v ∈ W ∧ KStable act W ∧
    ∀ (ν : Ix p q → ℚ) (w : V), w ∈ W → IsHW act ν w → ν = μ

def casimir (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Module.End ℂ V :=
  ∑ a, ∑ b, act (Eab a b) * act (Eab b a)

end Modules

structure GKMod (p q : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]
  act : Mat p q →ₗ[ℂ] Module.End ℂ V
  lie : IsLieAct act
  kfin : ∀ v, ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ v ∈ W ∧ KStable act W
  wts : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ

attribute [instance] GKMod.acg GKMod.mod

structure UGKMod (p q : ℕ) where
  M : GKMod p q
  ip : M.V →ₗ⋆[ℂ] M.V →ₗ[ℂ] ℂ
  herm : ∀ x y, star (ip x y) = ip y x
  pos : ∀ x, x ≠ 0 → 0 < (ip x x).re
  adj : ∀ Z x y, ip (M.act Z x) y = ip x (M.act (adjZ Z) y)

structure GrpData (p q : ℕ) where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  [tgrp : IsTopologicalGroup G]
  [ms : MeasurableSpace G]
  [bs : BorelSpace G]

  haar : Measure G
  [isHaar : haar.IsHaarMeasure]

  cov : G →* GL (Ix p q) ℂ

  sq : G →* ℂˣ
  cov_mem : ∀ x, cov x ∈ Formalism.UG.Upq p q
  sq_sq : ∀ x, ((sq x : ℂˣ) : ℂ) ^ 2 = ((cov x : GL (Ix p q) ℂ) : Mat p q).det

  bij : ∀ g ∈ Formalism.UG.Upq p q, ∀ w : ℂˣ, (w : ℂ) ^ 2 = ((g : GL (Ix p q) ℂ) : Mat p q).det →
    ∃! x, cov x = g ∧ sq x = w

  emb : Topology.IsEmbedding (fun x : G => (cov x, sq x))

  expt : Mat p q → G
  expt_cov : ∀ X ∈ upq p q, ((cov (expt X) : GL (Ix p q) ℂ) : Mat p q) = NormedSpace.exp X
  expt_cont : ContinuousOn expt (upq p q)
  expt_zero : expt 0 = 1
  expt_add : ∀ X ∈ upq p q, ∀ s t : ℝ, expt ((s + t) • X) = expt (s • X) * expt (t • X)

attribute [instance] GrpData.grp GrpData.top GrpData.tgrp GrpData.ms GrpData.bs GrpData.isHaar

def GrpData.Kset {p q : ℕ} (T : GrpData p q) : Set T.G :=
  {x | IsKC ((T.cov x : GL (Ix p q) ℂ) : Mat p q)}

structure URep {p q : ℕ} (T : GrpData p q) where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  π : T.G →* (H →L[ℂ] H)
  isom : ∀ g x, ‖π g x‖ = ‖x‖
  cont : ∀ x, Continuous fun g => π g x

attribute [instance] URep.nacg URep.ips URep.cs

section Analytic

variable {p q : ℕ} (T : GrpData p q) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def KFin (π : T.G → H →L[ℂ] H) (x : H) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : T.Kset => π k x))

def IsDer (π : T.G → H →L[ℂ] H) (X : Mat p q) (x y : H) : Prop :=
  X ∈ upq p q ∧ HasDerivAt (fun t : ℝ => π (T.expt (t • X)) x) y 0

def IsDerC (π : T.G → H →L[ℂ] H) (Z : Mat p q) (x y : H) : Prop :=
  ∃ y₁ y₂, IsDer T π ((1 / 2 : ℂ) • (Z + conjR Z)) x y₁ ∧
    IsDer T π ((1 / (2 * Complex.I)) • (Z - conjR Z)) x y₂ ∧ y = y₁ + Complex.I • y₂

def Smooth (π : T.G → H →L[ℂ] H) (x : H) : Prop :=
  ∃ W : Submodule ℂ H, x ∈ W ∧ ∀ w ∈ W, ∀ X ∈ upq p q, ∃ y ∈ W, IsDer T π X w y

def CasEig (π : T.G → H →L[ℂ] H) (x : H) (c : ℂ) : Prop :=
  ∃ y z : Ix p q → Ix p q → H, (∀ a b, IsDerC T π (Eab b a) x (y a b) ∧
    IsDerC T π (Eab a b) (y a b) (z a b)) ∧ ∑ a, ∑ b, z a b = c • x

def UgSpan (π : T.G → H →L[ℂ] H) (u : H) : Set H :=
  {w | ∀ W : Submodule ℂ H, u ∈ W → (∀ w' ∈ W, ∀ X y, IsDer T π X w' y → y ∈ W) → w ∈ W}

def opE (π : T.G → H →L[ℂ] H) (e : T.G → ℂ) (x : H) : H := ∫ g, e g • π g x ∂T.haar

end Analytic

structure DSRep {p q : ℕ} (T : GrpData p q) where
  U : URep T
  nontriv : Nontrivial U.H
  irred : ∀ S : Submodule ℂ U.H, IsClosed (S : Set U.H) → (∀ g, ∀ x ∈ S, U.π g x ∈ S) →
    S = ⊥ ∨ S = ⊤
  fdeg : ℝ
  fdeg_pos : 0 < fdeg
  schur : ∀ x y : U.H, Integrable (fun g => ‖inner ℂ y (U.π g x)‖ ^ 2) T.haar ∧
    ∫ g, ‖inner ℂ y (U.π g x)‖ ^ 2 ∂T.haar = ‖x‖ ^ 2 * ‖y‖ ^ 2 / fdeg
  HK : GKMod p q
  ι : HK.V →ₗ[ℂ] U.H
  ι_inj : Function.Injective ι
  ι_range : ∀ x, x ∈ Set.range ι ↔ KFin T U.π x
  der : ∀ X ∈ upq p q, ∀ v, HasDerivAt (fun t : ℝ => U.π (T.expt (t • X)) (ι v)) (ι (HK.act X v)) 0

abbrev Ln (p q r s : ℕ) := Ix p q × Ix r s

abbrev Pol (p q r s : ℕ) := MvPolynomial (Ix p q × Ix r s) ℂ

def lineSign {p q r s : ℕ} : Ix p q → Ix r s → ℂ
  | .inl _, .inl _ => 1
  | .inr _, .inr _ => 1
  | _, _ => -1

def linePos {p q r s : ℕ} : Ln p q r s → Bool
  | (.inl _, .inl _) => true
  | (.inr _, .inr _) => true
  | _ => false

def lowB {p q r s : ℕ} (l : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  if linePos l then (MvPolynomial.pderiv l).toLinearMap
  else LinearMap.mulLeft ℂ (MvPolynomial.X l)

def raiB {p q r s : ℕ} (l : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  if linePos l then LinearMap.mulLeft ℂ (MvPolynomial.X l)
  else -(MvPolynomial.pderiv l).toLinearMap

def omE {p q r s : ℕ} (l l' : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  raiB l * lowB l' + if l = l' then (1 / 2 : ℂ) • 1 else 0

def omAct (p q r s : ℕ) :
    Matrix (Ln p q r s) (Ln p q r s) ℂ →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  ∑ l, ∑ l', (Matrix.entryLinearMap ℂ ℂ l l').smulRight (omE l l')

def fockAct1 (p q r s : ℕ) : Mat p q →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  omAct p q r s ∘ₗ (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s)

def fockAct2 (p q r s : ℕ) : Mat r s →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  omAct p q r s ∘ₗ (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat p q)

def lineEquiv (p q r s : ℕ) : Ln p q r s ≃ Ix (p * r + q * s) (p * s + q * r) :=
  (Equiv.sumProdDistrib _ _ _).trans <|
  (Equiv.sumCongr (Equiv.prodSumDistrib _ _ _)
    ((Equiv.prodSumDistrib _ _ _).trans (Equiv.sumComm _ _))).trans <|
  (Equiv.sumSumSumComm _ _ _ _).trans <|
  Equiv.sumCongr ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)

theorem lineEquiv_isLeft {p q r s : ℕ} (l : Ln p q r s) :
    (lineEquiv p q r s l).isLeft = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> simp [lineEquiv, linePos]

section RuleR

open MvPolynomial

theorem omAct_apply {p q r s : ℕ} (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s Z = ∑ l, ∑ l', Z l l' • omE l l' := by
  simp [omAct, LinearMap.sum_apply]

theorem fockAct1_Eab {p q r s : ℕ} (a b : Ix p q) :
    fockAct1 p q r s (Eab a b) = ∑ c, omE (a, c) (b, c) := by
  simp only [fockAct1, LinearMap.comp_apply, LinearMap.flip_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply',
    Fintype.sum_prod_type, Eab, Matrix.single_apply, Matrix.one_apply]
  simp [ite_and, Finset.sum_ite_eq, ite_smul]

theorem fockAct2_Eab {p q r s : ℕ} (c d : Ix r s) :
    fockAct2 p q r s (Eab c d) = ∑ a, omE (a, c) (a, d) := by
  simp only [fockAct2, LinearMap.comp_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply',
    Fintype.sum_prod_type, Eab, Matrix.single_apply, Matrix.one_apply]
  simp [ite_and, Finset.sum_ite_eq, ite_smul]

theorem X_mul_pderiv_monomial {σ : Type*} [DecidableEq σ] (l : σ) (α : σ →₀ ℕ) :
    (X l : MvPolynomial σ ℂ) * pderiv l (monomial α 1) = ((α l : ℕ) : ℂ) • monomial α 1 := by
  rw [pderiv_monomial]
  by_cases h : α l = 0
  · simp [h]
  · have hα : Finsupp.single l 1 + (α - Finsupp.single l 1) = α := by
      ext i
      by_cases hi : i = l
      · subst hi; simp; omega
      · simp [Ne.symm hi]
    rw [X, monomial_mul, smul_monomial, hα]
    simp

theorem omE_pos {p q r s : ℕ} (l : Ln p q r s) (hl : linePos l = true) (α : Ln p q r s →₀ ℕ) :
    omE l l (monomial α 1) = (((α l : ℕ) : ℂ) + 1 / 2) • monomial α 1 := by
  simp only [omE, raiB, lowB, hl, if_true]
  show (X l : Pol p q r s) * pderiv l (monomial α (1 : ℂ)) + (1 / 2 : ℂ) • monomial α (1 : ℂ) = _
  rw [X_mul_pderiv_monomial, add_smul]

theorem omE_neg {p q r s : ℕ} (l : Ln p q r s) (hl : linePos l = false) (α : Ln p q r s →₀ ℕ) :
    omE l l (monomial α 1) = (-(((α l : ℕ) : ℂ) + 1 / 2)) • monomial α 1 := by
  simp only [omE, raiB, lowB, hl, if_true, Bool.false_eq_true, if_false]
  show -(pderiv l ((X l : Pol p q r s) * monomial α (1 : ℂ))) + (1 / 2 : ℂ) • monomial α (1 : ℂ) = _
  rw [Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, X_mul_pderiv_monomial, mul_one]
  module

theorem omE_diag {p q r s : ℕ} (a : Ix p q) (c : Ix r s) (α : Ln p q r s →₀ ℕ) :
    omE (a, c) (a, c) (monomial α 1) =
      (lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) • monomial α 1 := by
  rcases a with a | a <;> rcases c with c | c
  · rw [omE_pos _ rfl]; simp [lineSign]
  · rw [omE_neg _ rfl]; simp [lineSign]
  · rw [omE_neg _ rfl]; simp [lineSign]
  · rw [omE_pos _ rfl]; simp [lineSign]

theorem cartan1 {p q r s : ℕ} (a : Ix p q) (α : Ln p q r s →₀ ℕ) :
    fockAct1 p q r s (Eab a a) (monomial α 1) =
      (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) • monomial α 1 := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => omE_diag a c α

theorem cartan2 {p q r s : ℕ} (c : Ix r s) (α : Ln p q r s →₀ ℕ) :
    fockAct2 p q r s (Eab c c) (monomial α 1) =
      (∑ a, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) • monomial α 1 := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun a _ => omE_diag a c α

end RuleR

section Grading

variable {σ : Type*}

def plusPart (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ᶠ d : ℕ, MvPolynomial.homogeneousComponent (d + 2) (A (MvPolynomial.homogeneousComponent d P))

def minusPart (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ᶠ d : ℕ, MvPolynomial.homogeneousComponent d (A (MvPolynomial.homogeneousComponent (d + 2) P))

abbrev homog (σ : Type*) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  MvPolynomial.homogeneousSubmodule σ ℂ d

end Grading

structure FockData {p q r s : ℕ} (T0 : GrpData (p * r + q * s) (p * s + q * r))
    (T1 : GrpData p q) (T2 : GrpData r s) where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]

  Om : T0.G →* (H →L[ℂ] H)
  isom : ∀ g x, ‖Om g x‖ = ‖x‖
  cont : ∀ x, Continuous fun g => Om g x
  ι : Pol p q r s →ₗ[ℂ] H
  ι_inj : Function.Injective ι
  dense : Dense (Set.range ι)

  fockIP : ∀ α β, inner ℂ (ι (MvPolynomial.monomial α 1)) (ι (MvPolynomial.monomial β 1)) =
    if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0

  der : ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ P,
    HasDerivAt (fun t : ℝ => Om (T0.expt (t • Z)) (ι P))
      (ι (omAct p q r s
        (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) P)) 0

  emb : T1.G × T2.G →* T0.G
  emb_cov : ∀ g h, ((T0.cov (emb (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) =
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Matrix.kroneckerMap (· * ·) ((T1.cov g : GL _ ℂ) : Mat p q) ((T2.cov h : GL _ ℂ) : Mat r s))
  emb_sq : ∀ g h, T0.sq (emb (g, h)) = T1.sq g ^ (r + s) * T2.sq h ^ (p + q)

attribute [instance] FockData.nacg FockData.ips FockData.cs

section FockDefs

variable {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
  {T2 : GrpData r s}

def FockData.π (F : FockData T0 T1 T2) : T1.G × T2.G →* (F.H →L[ℂ] F.H) := F.Om.comp F.emb

def FockData.act1 (_F : FockData T0 T1 T2) : Mat p q →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  fockAct1 p q r s

def FockData.act2 (_F : FockData T0 T1 T2) : Mat r s →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  fockAct2 p q r s

end FockDefs

def FockData.J {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) :
    Set (Pol p q r s) :=
  {P | (∀ X, IsPC X → minusPart (F.act1 X) P = 0) ∧ (∀ Y, IsPC Y → minusPart (F.act2 Y) P = 0)}

def IsIntw {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2)
    (M1 : GKMod p q) (M2 : GKMod r s)
    (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V) : Prop :=
  (∀ X, f ∘ₗ F.act1 X = TensorProduct.map (M1.act X) LinearMap.id ∘ₗ f) ∧
  (∀ Y, f ∘ₗ F.act2 Y = TensorProduct.map LinearMap.id (M2.act Y) ∘ₗ f)

def rhoNC {p q : ℕ} (lam : Ix p q → ℚ) (a : Ix p q) : ℚ :=
  (((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card : ℚ) -
    ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card : ℚ)) / 2 -
  (((Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card : ℚ) -
    ((Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card : ℚ)) / 2

def blattner {p q : ℕ} (lam : Ix p q → ℚ) : Ix p q → ℚ := fun a => lam a + rhoNC lam a

def rhoSq (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (((n : ℚ) - 1) / 2 - (i : ℚ)) ^ 2

def normSq {p q : ℕ} (lam : Ix p q → ℚ) : ℚ := ∑ a, lam a ^ 2

def IsParam {p q : ℕ} (lam : Ix p q → ℚ) : Prop :=
  Function.Injective lam ∧ (∀ a b, posC a b → lam b < lam a) ∧
  (∀ a, ∃ k : ℤ, 2 * lam a = k) ∧ (∀ a b, ∃ k : ℤ, lam a - lam b = k)

def GapGe {p q : ℕ} (lam : Ix p q → ℚ) (h : ℝ) : Prop :=
  ∀ a b, ¬ sameBlock a b → h ≤ |((lam a - lam b : ℚ) : ℝ)|

def GapGt {p q : ℕ} (lam : Ix p q → ℚ) (h : ℝ) : Prop :=
  ∀ a b, ¬ sameBlock a b → h < |((lam a - lam b : ℚ) : ℝ)|

def shiftNu {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) : Ix p q → ℚ
  | .inl i => μ (.inl i) - c
  | .inr j => μ (.inr j) + c

def degW {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) : ℚ := ∑ a, |shiftNu c μ a|

def cPair (r s : ℕ) : ℚ := ((r : ℚ) - (s : ℚ)) / 2

def ofBlocks {p q : ℕ} (l₁ l₂ : List ℚ) : Ix p q → ℚ
  | .inl i => l₁.getD i 0
  | .inr j => l₂.getD j 0

def pad (x : List ℤ) (k : ℕ) (y : List ℤ) : List ℚ :=
  (x ++ List.replicate k 0 ++ y).map (fun v : ℤ => (v : ℚ))

def JointShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  ∃ a b c d : List ℤ,
    (∀ v ∈ a, 0 < v) ∧ (∀ v ∈ c, 0 < v) ∧ (∀ v ∈ b, v < 0) ∧ (∀ v ∈ d, v < 0) ∧
    a.Pairwise (· ≥ ·) ∧ b.Pairwise (· ≥ ·) ∧ c.Pairwise (· ≥ ·) ∧ d.Pairwise (· ≥ ·) ∧
    a.length + b.length ≤ p ∧ c.length + d.length ≤ q ∧
    a.length + d.length ≤ r ∧ c.length + b.length ≤ s ∧
    shiftNu (cPair r s) μ =
      ofBlocks (pad a (p - a.length - b.length) b) (pad c (q - c.length - d.length) d) ∧
    shiftNu (cPair p q) μ' =
      ofBlocks (pad a (r - a.length - d.length) d) (pad c (s - c.length - b.length) b)

def block (t : ℕ) : List ℚ := (List.range t).map fun m => ((t : ℚ) - 1) / 2 - (m : ℚ)

def lamA (al be ga de : List ℚ) : Ix (al.length + be.length) (ga.length + de.length) → ℚ :=
  ofBlocks (al ++ be) (ga ++ de)

def lamA' (t : ℕ) (al be ga de : List ℚ) :
    Ix (al.length + de.length + t) (ga.length + be.length) → ℚ :=
  ofBlocks (al ++ block t ++ de) (ga ++ be)

def lamM' (t : ℕ) (al be ga de : List ℚ) :
    Ix (al.length + de.length) (ga.length + be.length + t) → ℚ :=
  ofBlocks (al ++ de) (ga ++ block t ++ be)

def HypA (t : ℕ) (al be ga de : List ℚ) : Prop :=
  1 ≤ t ∧ 1 ≤ al.length + be.length + ga.length + de.length ∧
  al.Pairwise (· > ·) ∧ be.Pairwise (· > ·) ∧ ga.Pairwise (· > ·) ∧ de.Pairwise (· > ·) ∧
  (al ++ be ++ ga ++ de).Nodup ∧
  (∀ e ∈ al ++ ga, 0 < e) ∧ (∀ e ∈ be ++ de, e < 0) ∧
  (∀ e ∈ al ++ be ++ ga ++ de, ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k) ∧
  (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 1) / 2 ≤ |e|)

def HypG (t : ℕ) (al be ga de : List ℚ) : Prop :=
  GapGt (lamA al be ga de)
      (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) ∧
  GapGt (lamA' t al be ga de)
      (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) ∧
  GapGe (lamA al be ga de)
    (120 * ((al.length + be.length + ga.length + de.length : ℕ) : ℝ) *
      ((min (al.length + be.length) (ga.length + de.length) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))

def HypGm (t : ℕ) (al be ga de : List ℚ) : Prop :=
  GapGt (lamA al be ga de)
      (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) ∧
  GapGt (lamM' t al be ga de)
      (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) ∧
  GapGe (lamA al be ga de)
    (120 * ((al.length + be.length + ga.length + de.length : ℕ) : ℝ) *
      ((min (al.length + be.length) (ga.length + de.length) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))

def UnitHW {p q : ℕ} {T : GrpData p q} (D : DSRep T) (Λ : Ix p q → ℚ) (v : D.HK.V) : Prop :=
  IsHW D.HK.act Λ v ∧ ‖D.ι v‖ = 1

def JointHW {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2)
    (Λ : Ix p q → ℚ) (Λ' : Ix r s → ℚ) (Φ : Pol p q r s) : Prop :=
  Φ ∈ F.J ∧ IsHW F.act1 Λ Φ ∧ IsHW F.act2 Λ' Φ ∧ ‖F.ι Φ‖ = 1

def mcoef {p q : ℕ} {T : GrpData p q} (D : DSRep T) (v : D.HK.V) (g : T.G) : ℂ :=
  inner ℂ (D.ι v) (D.U.π g (D.ι v))

def eFun {p q : ℕ} {T : GrpData p q} (D : DSRep T) (v : D.HK.V) (g : T.G) : ℂ :=
  (D.fdeg : ℂ) * star (mcoef D v g)

structure ProvA where

  grp : ∀ p q : ℕ, GrpData p q

  fock : ∀ p q r s : ℕ, FockData (grp (p * r + q * s) (p * s + q * r)) (grp p q) (grp r s)

  ds : ∀ p q : ℕ, (Ix p q → ℚ) → DSRep (grp p q)

end Formalism.BasicNotions.TH

namespace Formalism.BasicNotions

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace TH

abbrev HSp (D : D7) : Type 1 := HSpace D.host.E

def tauE (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau τ).1

def gramAt (D : D7) (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (HSpace.gram V).map (tauE D τ)

def GrpData.covU {p q : ℕ} (T : GrpData p q) (x : T.G) : UpqT p q :=
  (⟨T.cov x, T.cov_mem x⟩ : Formalism.UG.Upq p q)

abbrev SPar : Type := Finset (ℚ × Bool)

structure TPar (D : D7) where
  t : ℕ
  t_odd : Odd t
  t_ge : D.R.r + 5 ≤ t
  u : D.what₂.Tau → Fin D.R.k → ℚ
  v : D.what₂.Tau → Fin (D.R.k - 1) → ℚ
  b : D.what₂.Tau → Fin D.R.m → ℚ
  e : D.what₂.Tau → Fin D.R.m → ℚ

  eta : D.what₂.Tau → ℚ
  eta_half : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2)

namespace TPar

variable {D : D7} (P : TPar D)

def ofWord (D : D7) (w : D.what₂.Word) (eta : D.what₂.Tau → ℚ)
    (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2)) : TPar D where
  t := D.R.t
  t_odd := D.R.t_odd
  t_ge := D.R.rank_add_five_le
  u := fun τ => (D.hcW w τ).u
  v := fun τ => (D.hcW w τ).v
  b := fun τ => (D.hcW w τ).b
  e := fun τ => (D.hcW w τ).e
  eta := eta
  eta_half := h

def Interlace : Prop :=
  ∀ τ, (∀ i : Fin (D.R.k - 1), P.v τ i < P.u τ ⟨i.1, by omega⟩ ∧ P.u τ ⟨i.1 + 1, by omega⟩ < P.v τ i) ∧
    (∀ (h : 0 < D.R.k) (h' : 0 < D.R.m), -P.b τ ⟨0, h'⟩ < P.u τ ⟨D.R.k - 1, by omega⟩) ∧
    (∀ j : Fin D.R.m, P.b τ j < P.e τ j) ∧
    (∀ j : Fin D.R.m, ∀ h : j.1 + 1 < D.R.m, P.e τ j < P.b τ ⟨j.1 + 1, h⟩)

def block (c : ℚ) (len : ℕ) : Finset ℚ :=
  (Finset.range len).image fun a : ℕ => c + ((len : ℚ) - 1) / 2 - (a : ℚ)

def Dpar (j : ℕ) (τ : D.what₂.Tau) : SPar :=
  ((Finset.univ.image fun i : Fin (D.R.k - 1) => (P.v τ i, true)) ∪
  (Finset.univ.image fun i : Fin D.R.m => (-P.b τ i, decide (i.1 ≤ j ∨ Even (i.1 - j)))) ∪
  ((Finset.univ.filter fun i : Fin D.R.m => i.1 < j).biUnion fun i =>
    (block (-P.e τ i) P.t).image fun x => (x, true))).image
      fun x => (x.1 + (if Odd j then P.eta τ else 0), x.2)

def Xpar (j : ℕ) (τ : D.what₂.Tau) : SPar :=
  (Finset.univ.image fun i : Fin D.R.k => (P.u τ i, true)) ∪
  ((Finset.univ.filter fun i : Fin D.R.m => i.1 < j).biUnion fun i =>
    (block (-P.e τ i) (P.t + 1)).image fun x => (x, true))

def Centred : Prop :=
  ∀ τ (j : Fin D.R.m),
    (∀ i, ((P.t : ℚ) + 3) / 2 ≤ |P.u τ i + P.e τ j|) ∧ (∀ i, ((P.t : ℚ) + 3) / 2 ≤ |P.v τ i + P.e τ j|) ∧
    (∀ i, ((P.t : ℚ) + 3) / 2 ≤ |P.e τ j - P.b τ i|) ∧
    (∀ j' : Fin D.R.m, j' ≠ j → ∀ x ∈ block (-P.e τ j') P.t, ((P.t : ℚ) + 3) / 2 ≤ |x + P.e τ j|)

end TPar

end TH

open TH

def TH.HaarCd (D : D7) (A : TH.ProvA) : Prop :=
  ∀ p q, Measure.map (A.grp p q).covU (A.grp p q).haar = D.cd.cd p q

def TH.parIdx (q : ℝ) (r s : ℕ) : ℝ :=
  q ^ (r * s) * (∏ i ∈ Finset.Icc 1 (r + s), (1 - q ^ (-(i : ℤ)))) /
    ((∏ i ∈ Finset.Icc 1 r, (1 - q ^ (-(i : ℤ)))) * ∏ i ∈ Finset.Icc 1 s, (1 - q ^ (-(i : ℤ))))

structure ThetaX (D : D7) : Type 1 where

  AF : HSp D → Type
  [afAdd : ∀ V, AddCommGroup (AF V)]
  [afMod : ∀ V, Module ℂ (AF V)]

  cusp : ∀ V, Submodule ℂ (AF V)

  pet : ∀ V, AF V → cusp V → ℂ
  pet_add_left : ∀ V F F' G, pet V (F + F') G = pet V F G + pet V F' G
  pet_smul_left : ∀ V (c : ℂ) F G, pet V (c • F) G = star c * pet V F G
  pet_right : ∀ V F, IsLinearMap ℂ (pet V F)
  pet_symm : ∀ V (F G : cusp V), pet V (F : AF V) G = star (pet V (G : AF V) F)
  pet_pos : ∀ V (F : cusp V), F ≠ 0 → 0 < (pet V (F : AF V) F).re

  actR : ∀ V (τ : D.what₂.Tau), Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (AF V)
  actR_one : ∀ V τ, actR V τ 1 = 1
  actR_mul : ∀ V τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    actR V τ (g * h) = actR V τ g * actR V τ h
  actR_cusp : ∀ V τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ F ∈ cusp V, actR V τ g F ∈ cusp V

  Gf : HSp D → Type
  [gfGrp : ∀ V, Group (Gf V)]
  actF : ∀ V, Gf V →* Module.End ℂ (AF V)
  actF_cusp : ∀ V g, ∀ F ∈ cusp V, actF V g F ∈ cusp V

  actF_actR : ∀ V g τ h, actF V g * actR V τ h = actR V τ h * actF V g

  Ksph : ∀ V, Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) →
    Subgroup (Gf V)
  Ksph_mono : ∀ V S S', S ⊆ S' → Ksph V S' ≤ Ksph V S

  typ : ∀ V, (D.what₂.Tau → SPar) → Submodule ℂ (AF V)

  Chr : Type
  [chrGrp : CommGroup Chr]

  infTy : Chr → D.what₂.Tau → ℚ
  infTy_mul : ∀ χ χ' τ, infTy (χ * χ') τ = infTy χ τ + infTy χ' τ

  chrOf : D.what₂.Tup → ℕ → Chr
  chrOf_inf : ∀ μ (j : Fin D.R.m) τ, infTy (chrOf μ (j.1 + 1)) τ = -(D.hc τ).e j

  etaT : Chr
  etaT_inf : ∀ τ, infTy etaT τ = 1 / 2 ∨ infTy etaT τ = -(1 / 2)
  etaT_pos : ∀ τ, infTy etaT τ = 1 / 2

  Sch : HSp D → HSp D → Type
  [schAdd : ∀ V W, AddCommGroup (Sch V W)]
  [schMod : ∀ V W, Module ℂ (Sch V W)]

  fact : ∀ V W, Set (Sch V W)

  kfin : ∀ V W, Submodule ℂ (Sch V W)

  th : ∀ V W, Chr → Chr → Sch V W →ₗ[ℂ] cusp V →ₗ[ℂ] AF W

  Xs : ℕ → ℕ → HSp D
  Xs_rank : ∀ t j, j ≤ D.R.m → (Xs t j).rank = D.R.k + j * (t + 1)
  Xs_sig : ∀ t j, j ≤ D.R.m → (Xs t j).SigOK ∧ (Xs t j).IsDefinite

  Ys : ℕ → ℕ → HSp D
  Ys_rank : ∀ t j, j ≤ D.R.m → (Ys t j).rank = D.R.r + j * t
  Ys_sig : ∀ t j, j ≤ D.R.m → (Ys t j).SigOK

  iXYs : ∀ t j, (Xs t j).V →ₗ[D.host.E] (Ys t j).V
  iXYs_isom : ∀ t j, j < D.R.m → HSpace.IsIsomEmb (Xs t j) (Ys t j) (iXYs t j)
  iYXm : ∀ t, (Ys t D.R.m).V →ₗ[D.host.E] (Xs t D.R.m).V
  iYXm_isom : ∀ t, HSpace.IsIsomEmb (Ys t D.R.m) (Xs t D.R.m) (iYXm t)

  YsLow : ℕ → ℕ → ℕ → HSp D
  YsLow_zero : ∀ t j, YsLow t j 0 = Ys t j

  Xs_rec : ∀ j, j ≤ D.R.m → Xs D.R.t j = D.sp.X j
  Ys_rec : ∀ j, j ≤ D.R.m → Ys D.R.t j = D.sp.Y j

  conjAF : ∀ V, AF V → AF V
  conjAF_add : ∀ V F F', conjAF V (F + F') = conjAF V F + conjAF V F'
  conjAF_smul : ∀ V (c : ℂ) F, conjAF V (c • F) = star c • conjAF V F
  conjAF_conjAF : ∀ V F, conjAF V (conjAF V F) = F
  conjAF_cusp : ∀ V, ∀ F ∈ cusp V, conjAF V F ∈ cusp V

  Pos : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type

  FJd : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  [fjAdd : ∀ A B ι, AddCommGroup (FJd A B ι)]
  [fjMod : ∀ A B ι, Module ℂ (FJd A B ι)]

  Bper : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), Pos A B ι → FJd A B ι → AF A → cusp B → ℂ
  Bper_right : ∀ A B ι p s φ, IsLinearMap ℂ (Bper A B ι p s φ)
  Bper_add_left : ∀ A B ι p s φ φ' F,
    Bper A B ι p s (φ + φ') F = Bper A B ι p s φ F + Bper A B ι p s φ' F
  Bper_smul_left : ∀ A B ι p s (c : ℂ) φ F, Bper A B ι p s (c • φ) F = star c * Bper A B ι p s φ F

  Bper_odd : ∀ A B ι p, Odd (B.rank - A.rank) → ∀ s s' φ F, Bper A B ι p s φ F = Bper A B ι p s' φ F

  Btop : ∀ (A B : HSp D), (B.V →ₗ[D.host.E] A.V) → AF A → cusp B → ℂ
  Btop_right : ∀ A B ι φ, IsLinearMap ℂ (Btop A B ι φ)
  Btop_add_left : ∀ A B ι φ φ' F, Btop A B ι (φ + φ') F = Btop A B ι φ F + Btop A B ι φ' F
  Btop_smul_left : ∀ A B ι (c : ℂ) φ F, Btop A B ι (c • φ) F = star c * Btop A B ι φ F

  pos1 : D.what₂.Word → Pos (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)
  posSym : D.what₂.Word → Pos (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)

  colAF : ∀ (u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), D.what₂.Mu u →ₗ[ℂ] cusp (D.sp.X j)

  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] cusp (D.sp.Y j)

  PhiY : ∀ (_μ : D.what₂.Tup) (j : ℕ), Sch (D.sp.Y (j + 1)) (D.sp.Y j)

  PhiYup : ∀ (_μ : D.what₂.Tup) (j : ℕ), Sch (D.sp.Y j) (D.sp.Y (j + 1))

  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j

  adelicDataRowMeasureScale_trivialTuple : ∀ j, mY D.what₂.mu0 j = 1

  mY_zero : ∀ μ, mY μ 0 = 1

attribute [instance] ThetaX.afAdd ThetaX.afMod ThetaX.gfGrp ThetaX.chrGrp ThetaX.schAdd ThetaX.schMod
  ThetaX.fjAdd ThetaX.fjMod

namespace ThetaX

variable {D : D7} (X : ThetaX D)

def IsStable (V : HSp D) (π : Submodule ℂ (X.AF V)) : Prop :=
  (∀ g, ∀ F ∈ π, X.actF V g F ∈ π) ∧
  ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ F ∈ π, X.actR V τ h F ∈ π

def sphOff (V : HSp D)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F))) :
    Submodule ℂ (X.AF V) where
  carrier := {F | ∀ g ∈ X.Ksph V S, X.actF V g F = F}
  add_mem' := by
    intro a b ha hb g hg
    rw [map_add, ha g hg, hb g hg]
  zero_mem' := by intro g _; exact map_zero _
  smul_mem' := by
    intro c a ha g hg
    rw [map_smul, ha g hg]

def cuspD (P : TPar D) (j : ℕ) : Submodule ℂ (X.AF (X.Ys P.t j)) :=
  X.cusp _ ⊓ X.typ _ (P.Dpar j)

def typeX (P : TPar D) (j : ℕ) : Submodule ℂ (X.AF (X.Xs P.t j)) := X.typ _ (P.Xpar j)

def Bj (t j : ℕ) := X.Bper (X.Xs t j) (X.Ys t j) (X.iXYs t j)

def Bm (t : ℕ) := X.Btop (X.Xs t D.R.m) (X.Ys t D.R.m) (X.iYXm t)

def parOf (w : D.what₂.Word) : TPar D :=
  TPar.ofWord D w (fun τ => -X.infTy X.etaT τ) (by
    intro τ
    rcases X.etaT_inf τ with h | h
    · right; rw [h]
    · left; rw [h]; ring)

def carY (μ : D.what₂.Tup) (s i : ℕ) : X.Chr :=
  if Even i then X.chrOf μ s * X.etaT⁻¹ else X.chrOf μ s

def petY (μ : D.what₂.Tup) (j : ℕ) (F : X.AF (D.sp.Y j)) (G : X.cusp (D.sp.Y j)) : ℂ :=
  (X.mY μ j : ℂ) * X.pet _ F G

def dnY (μ : D.what₂.Tup) (j : ℕ) : X.cusp (D.sp.Y (j + 1)) →ₗ[ℂ] X.AF (D.sp.Y j) :=
  (X.mY μ (j + 1) : ℂ) • X.th _ _ (X.carY μ (j + 1) (j + 1)) (X.carY μ (j + 1) j) (X.PhiY μ j)

def TieMY {Q : D.what₂.Tup → Type} [∀ μ, Fintype (Q μ)] (qv : ∀ μ, Q μ → ℕ) : Prop :=
  ∀ μ j, j ≤ D.R.m → X.mY μ j = ∏ v : Q μ, TH.parIdx (qv μ v) D.R.r (j * D.R.t)

def TieRowIsom : Prop :=
  ∀ μ j, j ≤ D.R.m → ∀ (x y : D.what₂.Mult μ j),
    X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y

def TieIo : Prop :=
  ∀ μ j, j < D.R.m → ∀ (y : D.what₂.Mult μ (j + 1)) (x : D.what₂.Mult μ j),
    X.petY μ j (X.dnY μ j (X.rowAF μ (j + 1) y)) (X.rowAF μ j x) = inner ℂ (D.what₂.io μ j y) x

def TieBm : Prop :=
  ∀ u μ (φ : D.what₂.Mu u) (F : D.what₂.Amb μ),
    D.what₂.perCol u μ φ F =
      (X.mY μ D.R.m : ℂ) * X.Btop (D.sp.X D.R.m) (D.sp.Y D.R.m) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap)
        (X.conjAF _ ((X.colAF u μ D.R.m φ : X.cusp _) : X.AF _))
        (X.rowAF μ D.R.m ((D.what₂.multTop μ).symm F))

end ThetaX

end Formalism.BasicNotions

end
