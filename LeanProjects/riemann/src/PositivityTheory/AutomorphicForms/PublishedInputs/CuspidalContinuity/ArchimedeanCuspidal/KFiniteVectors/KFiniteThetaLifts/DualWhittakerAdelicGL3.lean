import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.AdmInv
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.LocalFunctionalEquationGL3GL2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership
import GroundTheory.GlobalFields.CompletionAtPlace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable {K : Type} [Field K] [NumberField K]

def nrm (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : (Kv K w)ˣ →* (Qv v)ˣ :=
  Units.map (Algebra.norm (Qv v) : Kv K w →* Qv v)

structure IsBC (D : Dat) (DK : DatK K) : Prop where
  k : DK.k = D.k
  nu : ∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], DK.ν w = (D.ν v).comp (nrm v w)
  bad : ∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal],
    w ∈ DK.bad ↔ (v ∈ D.bad ∨ w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1)

def cAt (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : (Qv v)ˣ →* ℂˣ :=
  (localChar c w).comp (Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom)

def InThE (c : HeckeCharacter K) (v : Pl) (W' : GL (Fin 2) (Qv v) → ℂ) (e : ℂ) : Prop :=
  (∃ (w₁ w₂ : PlK K) (_ : w₁.asIdeal.LiesOver v.asIdeal) (_ : w₂.asIdeal.LiesOver v.asIdeal), w₁ ≠ w₂ ∧
    W' ∈ GL2LocalData.VWS (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) ∧ e = 1) ∨
  (∃ (w : PlK K) (_ : w.asIdeal.LiesOver v.asIdeal), (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) ∧
    ∃ (σ : Kv K w ≃ₐ[Qv v] Kv K w) (η : (Qv v)ˣ →* ℂˣ), σ ≠ AlgEquiv.refl ∧
      (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg (Kv K w) (a : Qv v)) ∧
      W' ∈ GL2LocalData.VW (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
        (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) ∧
      e = GL2LocalData.nsg (Kv K w) (-1 : Qv v) * GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η ^ 3)

def gamV (DK : DatK K) (c : HeckeCharacter K) (v : Pl) (s : ℂ) : ℂ :=
  ∏ᶠ w : {w : PlK K // w.asIdeal.LiesOver v.asIdeal}, gam3 (localAdelicChar K w.1) (DK.ν w.1) (localChar c w.1) s

def lfV (DK : DatK K) (c : HeckeCharacter K) (v : Pl) (s : ℂ) : ℂ :=
  ∏ᶠ w : {w : PlK K // w.asIdeal.LiesOver v.asIdeal}, lf3 (DK.ν w.1) (localChar c w.1) s

def thR (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) : ℂ := GL2LocalData.WthR n g * ((|(g.val).det| : ℝ) : ℂ) ^ (Complex.I * t)

def SphN {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (W' : GL (Fin 2) F → ℂ) :
    Prop :=
  (∀ k ∈ integralGL F 2, ∀ g, W' (g * k) = W' g) ∧ W' 1 = 1

def zU {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (s : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ, W (dg (unifUnit F ^ (p.1 + p.2)) (unifUnit F ^ p.2) 1) * W' (d2 (unifUnit F ^ (p.1 + p.2)) (unifUnit F ^ p.2)) *
    ((residueCard F : ℂ) ^ (-(p.1 : ℂ) * (s - 3 / 2))) * ((residueCard F : ℂ) ^ (-(p.2 : ℂ) * (2 * s - 1)))

open Ad3.R (G2 Jd md Dt KA) in

abbrev e3A : G2 →* G3 := e3

open Ad3.R (G2 Dt) in

def IG (μ : Measure G2) (𝓕 : Set G2) (φ : G3 → ℂ) (θ : G2 → ℂ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕, φ (e3A g) * θ g * ((Dt g : ℝ) : ℂ) ^ (s - 1 / 2) ∂μ

open Ad3.R (G2) in

def pw2 (Wi : GL (Fin 2) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (h : G2) : ℂ :=
  Wi (GroundTheory.Automorphic.GL2Classical.realPart h) * ∏ᶠ v, Wf v (finAt v h)

open Ad3.R (G2 Jd md KA) in

def JG (mK : Measure KA) (W : G3 → ℂ) (Wt : G2 → ℂ) (s : ℂ) : ℂ :=
  ∫ κ, ∫ z, ∫ a, W (e3A (dg2 a 1 * dg2 z z * κ.1)) * Wt (dg2 a 1 * dg2 z z * κ.1) * ((md a : ℝ) : ℂ) ^ (s - 3 / 2) *
    ((md z : ℝ) : ℂ) ^ (2 * s - 1) ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK

def dualWhittakerAdelicGL3 (W : G3 → ℂ) (g : G3) : ℂ := W (w3 * ti g)
open Ad3.R (G2) in
def dualWhittakerAdelic (W : G2 → ℂ) (h : G2) : ℂ := W (w2 * ti h)

def IsLiftU (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3) : Prop :=
  (∀ W : V, AutomorphicForm.IsLeftInvariant (U W : G3 → ℂ) ∧ AutomorphicForm.HasModerateGrowth (U W : G3 → ℂ) ∧
      AutomorphicForm.IsCuspidal (U W : G3 → ℂ) ∧ FourierWhittaker.whittaker (U W : G3 → ℂ) = W) ∧
    (∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : G3 → ℂ) g = (U W : G3 → ℂ) (g * h)) ∧
    ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = EA i j (U W)

open Ad3.R (G2 Jd md KA pt) in

def ModG (θ : G2 → ℂ) : Prop := ∃ (C : ℝ) (N : ℕ), ∀ (x : 𝔸[ℚ]) (a z : Jd) (κ : KA),
  ‖θ (pt x a z κ.1)‖ ≤ C * ((md a + (md a)⁻¹) * (md z + (md z)⁻¹)) ^ N

open Ad3.R (G2 Jd md KA pt) in

def DecG (F : G2 → ℂ) : Prop := ∀ (M : ℕ) (c₀ : ℝ), 0 < c₀ → ∃ C : ℝ, ∀ (x : 𝔸[ℚ]) (a z : Jd) (κ : KA), c₀ ≤ md a →
  ‖F (pt x a z κ.1)‖ ≤ C * (md a)⁻¹ ^ M * min (md z) (md z)⁻¹ ^ M

open Ad3.R (G2 Jd md KA) in

def Gau2 (Wt : G2 → ℂ) : Prop := ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ (a z : Jd) (κ : KA),
  ‖Wt (dg2 a 1 * dg2 z z * κ.1)‖ ≤ C * ((md a + (md a)⁻¹) * (md z + (md z)⁻¹)) ^ T / (1 + md a) ^ N

open Ad3.R (G2 LInv pri) in

structure ThX (θ Cst Wt : G2 → ℂ) : Prop where
  cont : Continuous θ ∧ Continuous Cst ∧ Continuous Wt
  left : LInv θ
  mod : ModG θ
  mod' : ModG (fun h => θ (ti h))
  cst : ∀ (x : 𝔸[ℚ]) h, Cst (uni2 x * h) = Cst h
  sum : ∀ h, Summable (fun α : ℚˣ => ‖Wt (dg2 (pri α) 1 * h)‖)
  exp : ∀ h, HasSum (fun α : ℚˣ => Wt (dg2 (pri α) 1 * h)) (θ h - Cst h)
  psi : ∀ (x : 𝔸[ℚ]) h, Wt (uni2 x * h) = (adelicChar ℚ (-x) : ℂ) * Wt h
  gau : Gau2 Wt

end Ad3.K.QuadraticBaseChangeGL3
