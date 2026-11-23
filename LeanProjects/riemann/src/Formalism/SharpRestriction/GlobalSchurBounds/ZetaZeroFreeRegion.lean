import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Finset
open scoped Pointwise ComplexConjugate

open Classical

abbrev Chr (D : D7) : Type := D.R.GG →* ℂˣ

def sgnC : ℤˣ →* ℂˣ := Units.map (Int.castRingHom ℂ).toMonoidHom

abbrev chC (D : D7) : Chr D := D.R.chC

def psC (D : D7) : Chr D := sgnC.comp D.R.chQ

def Unram (D : D7) (p : ℕ) : Prop := p.Prime ∧ ¬ ((p : ℤ) ∣ discr D.host.E)

def InertK (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ (D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass)

def Reads (D : D7) (ψ : Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N) : Prop :=
  χ.2.IsPrimitive ∧ ∀ p : ℕ, Unram D p → χ.2 (p : ZMod χ.1) = ((ψ (frob D p) : ℂˣ) : ℂ)

def prim (D : D7) (ψ : Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  if h : ∃ χ, Reads D ψ χ then h.choose else ⟨1, 1⟩

def Gc (D : D7) (ψ : Chr D) (y : ℝ) : ℂ := gChi (prim D ψ).2 y

def Lp (D : D7) (ψ : Chr D) : ℂ := logDerivativeAtOne (prim D ψ).2

def PhiF (D : D7) : Finset (D.R.GG) := univ.filter (fun g => g ∈ D.R.Psi)

def notPhiF (D : D7) : Finset (D.R.GG) := univ.filter (fun g => g ∉ D.R.Psi)

def iner (D : D7) : D.R.GG := (sgc0, 1)

def inerP (D : D7) (P : Ideal (𝓞 D.host.E)) : Finset (D.R.GG) :=
  univ.filter (fun g => ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E,
    D.host.galE σ = g ∧ ∀ x : 𝓞 D.host.E, σ • x - x ∈ P)

def thickAt (D : D7) (u0 : HH D) : Finset (D.R.GG) :=
  D.host.T2.image (fun s => D.R.tau2 (D.R.dig s + u0))

def askP (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) (p : ℕ) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i ∧ frob D p ^ i ∉ D.R.Psi then
    max (a / (p : ℝ) ^ i - w (rho D τ (frob D p ^ i))) 0 else 0

def gD (D : D7) (i : ℕ) : D.R.GG :=
  if frob D D.host.d ^ i ∉ D.R.Psi then frob D D.host.d ^ i else frob D D.host.d ^ i * iner D

def askD (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i then max (a / (D.host.d : ℝ) ^ i - w (rho D τ (gD D i))) 0 else 0

def ASKjt (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  (∑' p : ℕ, if InertK D p then 2 * Real.log p * askP D a w τ p else 0) +
    Real.log D.host.d * askD D a w τ

def MAINjt (D : D7) (a : ℝ) (w : D.R.GG → ℝ) : ℂ :=
  (a : ℂ) * (((Real.log a - 1 - Real.eulerMascheroniConstant : ℝ) : ℂ) + Lp D (chC D) -
    (((1 : ℝ) / D.R.f * ∑ ρ ∈ PhiF D, Real.log (w ρ) : ℝ) : ℂ))

def Dejt (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℂ :=
  (1 / (D.R.f : ℂ)) * ∑ g ∈ notPhiF D, ∑ᶠ ψ : Chr D,
    conj ((ψ g : ℂˣ) : ℂ) * ((w (rho D τ g) : ℝ) : ℂ) * Gc D ψ (a / w (rho D τ g))

def GivenU (D : D7) (s : Scale) (η : ℝ) (u0 : HH D) (a : HH D → ℤ) (w : ℕ → D.R.GG → ℝ) :
    Prop :=
  0 < η ∧ Real.log η ≤ s.x ^ (s.eps / 4) ∧
  (∀ t ∈ D.host.TT, |(a t : ℝ) / s.b - s.x| ≤ 1) ∧
  ∀ j ∈ SizeData₂.lifts D, ∀ ρ ∈ D.R.Psi, 0 < w j ρ ∧
    (ρ ∈ thickAt D u0 → s.b ≤ w j ρ ∧ w j ρ ≤ s.b + η + 1) ∧
    (ρ ∉ thickAt D u0 → w j ρ ≤ 2 * s.b')

def GivenAll (D : D7) (s : Scale) (η : ℝ) (a : HH D → ℤ) (w : HH D → ℕ → D.R.GG → ℝ) : Prop :=
  ∀ u0, GivenU D s η u0 a (w u0)

def ASKtot (D : D7) (a : HH D → ℤ) (w : ℕ → D.R.GG → ℝ) : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ∑ t ∈ D.host.TT, ASKjt D (a t) (w j) (D.R.tau1 t)

def MAINtot (D : D7) (a : HH D → ℤ) (w : ℕ → D.R.GG → ℝ) : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ∑ t ∈ D.host.TT, (a t : ℝ) * (Real.log (a t) - 1 -
    Real.eulerMascheroniConstant + (Lp D (chC D)).re -
    (1 : ℝ) / D.R.f * ∑ ρ ∈ PhiF D, Real.log (w j ρ))

def Err (D : D7) (s : Scale) (C : ℝ) : ℝ :=
  s.x ^ (C * s.eps) * ((D.host.TT.card : ℝ) * s.a * (1 + (D.R.m : ℝ) ^ 2 / D.R.k) +
    (D.R.m : ℝ) * (sizeBudget D.R s.x s.eps + budgetNc D.R s.x s.eps D.host.T2.card))

def TOPineq (D : D7) (s : Scale) (C : ℝ) (a : HH D → ℤ) (w : HH D → ℕ → D.R.GG → ℝ) : Prop :=
  (1 : ℝ) / D.R.n * ∑ u0 : HH D, ASKtot D a (w u0) ≤
    (1 : ℝ) / D.R.n * ∑ u0 : HH D, MAINtot D a (w u0) + Err D s C

def adm1 (D : D7) : Prop :=
  IsCMField D.host.E ∧
  Module.finrank ℚ D.host.E = 2 * D.R.f ∧
  (∀ p : ℕ, p.Prime → (((p : ℤ) ∣ discr D.host.E) ↔ p ∣ D.host.condN)) ∧
  (∀ x : D.host.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm D.host.K x = 1) ∧
  (∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 D.host.E, D.host.conj • x - x ∈ P) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.condN → ∀ P : Ideal (𝓞 D.host.E), P.IsPrime →
    P.LiesOver (Ideal.span {(p : ℤ)}) → D.host.conj • P ≠ P) ∧
  D.host.rdE = rdF D

def adm2 (D : D7) : Prop :=
  (PhiEmb D = D.host.cmType ∧
    ∀ φ : D.host.E →+* ℂ, φ ∈ PhiEmb D ↔ (starRingEnd ℂ).comp φ ∉ PhiEmb D) ∧
  (∀ τ ∈ D.R.Psi, Set.BijOn (rho D τ) ((D.R.Psi : Set (D.R.GG))ᶜ) (D.R.Psi)) ∧
  (∀ t h : HH D,
    rho D (D.R.tau1 t) (gOf D c0 h) = D.R.tau1 (t + h) ∧
    rho D (D.R.tau2 t) (gOf D c0 h) = D.R.tau2 (t + h) ∧
    rho D (D.R.tau1 t) (gOf D sgc0 h) = D.R.tau2 (t + h) ∧
    rho D (D.R.tau2 t) (gOf D sgc0 h) = D.R.tau1 (t + h)) ∧
  (∀ ψ : Chr D, ∑ g ∈ notPhiF D, conj ((ψ g : ℂˣ) : ℂ) =
    if ψ = 1 then (D.R.f : ℂ) else if ψ = chC D then -(D.R.f : ℂ) else 0) ∧
  (∀ g : D.R.GG, 2 * (if g.1 = sgc0 then (1 : ℝ) else 0) =
    (1 - ((D.R.chD g : ℤ) : ℝ)) * (1 + ((D.R.chQ g : ℤ) : ℝ)) / 2)

def adm3 (D : D7) : Prop :=
  (∀ p : ℕ, p.Prime → p ∣ D.host.QS * D.host.q → ∀ P : Ideal (𝓞 D.host.E), P.IsPrime →
    P.LiesOver (Ideal.span {(p : ℤ)}) → ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ • P = P →
      D.host.galE σ ∈ D.R.Psi) ∧
  (∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (Ideal.span {(D.host.d : ℤ)}) →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, ((∀ x : 𝓞 D.host.E, σ • x - x ∈ P) ↔
      (D.host.galE σ = 1 ∨
        D.host.galE σ = iner D)))

def ArchimedeanSignatureMatching (D : D7) (s : Scale) (C : ℝ) : Prop :=
  ∀ ψ : Chr D,
    (∀ y : ℝ, 1 ≤ y → Gc D ψ y =
      -(y : ℂ) * ∫ u in Set.Ioi y, psi0 (prim D ψ).2 u / (u : ℂ) ^ 2) ∧
    (ψ ≠ 1 → Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M,
        ((cn s.x n : ℝ) : ℂ) * (prim D ψ).2 (n : ZMod (prim D ψ).1))
      Filter.atTop (nhds (-Gc D ψ s.x))) ∧
    (∀ y : ℝ, 1 ≤ y → ψ ≠ 1 → ‖deriv (fun y : ℝ => Gc D ψ y) y‖ ≤ Real.log y + C + ‖Lp D ψ‖) ∧
    (∀ y : ℝ, 1 ≤ y → ψ = 1 → ‖deriv (fun y : ℝ => Gc D ψ y) y‖ ≤ C) ∧
    (∀ y₁ y₂ : ℝ, 1 ≤ y₁ → 1 ≤ y₂ → ψ ≠ 1 →
      ‖Gc D ψ y₂ - Gc D ψ y₁‖ ≤ (Real.log (max y₁ y₂) + C + ‖Lp D ψ‖) * |y₂ - y₁|) ∧
    (∀ y₁ y₂ : ℝ, 1 ≤ y₁ → 1 ≤ y₂ → ψ = 1 → ‖Gc D ψ y₂ - Gc D ψ y₁‖ ≤ C * |y₂ - y₁|) ∧
    (∀ a w₁ w₂ : ℝ, 0 < a → 0 < w₁ → w₁ ≤ w₂ →
      ‖(w₂ : ℂ) * Gc D ψ (a / w₂) - (w₁ : ℂ) * Gc D ψ (a / w₁)‖ ≤ 3 * a * Real.log (w₂ / w₁))

def adm5 (D : D7) (s : Scale) (c : ℝ) : Prop :=
  ∀ ψ : Chr D, ∀ y : ℝ, s.X' / 3 ≤ y → ‖Gc D ψ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))

def adm6 (D : D7) (s : Scale) (C : ℝ) : Prop :=
  ∀ ψ ∈ ({psC D, chC D, chC D * psC D} : Finset (Chr D)),
    ‖Gc D ψ s.x‖ ≤ s.x ^ ((1 : ℝ) / 2 + s.eps) ∧ ‖Lp D ψ‖ ≤ C * Real.log s.x

def adm7 (D : D7) (s : Scale) (C : ℝ) : Prop :=
  ∃ (η : ℝ) (a : HH D → ℤ) (w : HH D → ℕ → D.R.GG → ℝ),
    GivenAll D s η a w ∧ TOPineq D s C a w

def adm8 : Prop :=
  ∀ (f : ℝ → ℝ) (y0 σ0 : ℝ), (∀ R : ℝ, ∃ M : ℝ, ∀ y ∈ Set.Icc 1 R, |f y| ≤ M) →
    (∀ y : ℝ, y0 ≤ y → 0 ≤ f y) →
    (∀ σ : ℝ, σ0 < σ → MeasureTheory.IntegrableOn (fun y : ℝ => f y * y ^ (-σ - 1)) (Set.Ioi 1)) →
    (∀ σ : ℝ, σ < σ0 →
      ¬ MeasureTheory.IntegrableOn (fun y : ℝ => f y * y ^ (-σ - 1)) (Set.Ioi 1)) →
    ¬ ∃ (g : ℂ → ℂ) (r : ℝ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball (σ0 : ℂ) r) ∧
      ∀ s ∈ Metric.ball (σ0 : ℂ) r, σ0 < s.re →
        g s = ∫ y in Set.Ioi (1 : ℝ), (f y : ℂ) * (y : ℂ) ^ (-s - 1)

def adm9 : Prop :=
  ∀ s : ℂ, (∀ n : ℕ, s ≠ -n) → s ≠ 1 →
    riemannZeta (1 - s) = 2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (Real.pi * s / 2) * riemannZeta s

theorem content_divisibility_clause : adm9 := by
  intro s hs hs'
  exact riemannZeta_one_sub hs hs'

def adm10 (D : D7) : Prop := ∀ ψ : Chr D, ∃ χ, Reads D ψ χ

def adm11 (D : D7) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ D.host.condN → ∀ P : Ideal (𝓞 D.host.E), P.IsPrime →
    P.LiesOver (Ideal.span {(p : ℤ)}) → ∀ i : ℕ, 1 ≤ i → ∀ ψ : Chr D,
      (prim D ψ).2 ((p ^ i : ℕ) : ZMod (prim D ψ).1) =
        (1 / ((inerP D P).card : ℂ)) *
          ∑ g ∈ (inerP D P).image (fun g => frob D p ^ i * g), ((ψ g : ℂˣ) : ℂ)

def admitted (D : D7) : Prop := adm1 D ∧ adm2 D ∧ adm3 D ∧ adm8 ∧ adm9 ∧ adm10 D ∧ adm11 D

def Conclusion1 (D : D7) (s : Scale) : Prop :=
  ∀ (η : ℝ) (u0 : HH D) (a : HH D → ℤ) (w : ℕ → D.R.GG → ℝ), GivenU D s η u0 a w →
    ∀ j ∈ SizeData₂.lifts D, ∀ t ∈ D.host.TT,
      ((ASKjt D (a t) (w j) (D.R.tau1 t) : ℝ) : ℂ) - MAINjt D (a t) (w j) =
        Dejt D (a t) (w j) (D.R.tau1 t)

def Conclusion2 (x eps C : ℝ) : Prop := G x ≤ x ^ ((1 : ℝ) / 2 + C * eps)

def PointsLemma : Prop :=
  ∀ θ y0 : ℝ, 0 < θ → θ < 1 → (∀ y : ℝ, y0 ≤ y → G y ≤ y ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def Conclusion₂ (D : D7) (s : Scale) : Prop := Conclusion1 D s ∧ PointsLemma

def Stmt (D : D7) (s : Scale) : Prop := admitted D → Conclusion₂ D s

def SizesAt (D : D7) (s : Scale) (δ : ℝ) : Prop :=
  s.x ^ (2 + 8 * s.eps - δ) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ s.x ^ (2 + 8 * s.eps + δ) ∧
  (s.x * s.delta1) ^ ((1 : ℝ) / 2 - δ) ≤ (D.R.m : ℝ) ∧
    (D.R.m : ℝ) ≤ (s.x * s.delta1) ^ ((1 : ℝ) / 2 + δ) ∧
  s.x ^ ((9 : ℝ) / 2 + 10 * s.eps - δ) ≤ (D.R.k : ℝ) ∧
    (D.R.k : ℝ) ≤ s.x ^ ((9 : ℝ) / 2 + 10 * s.eps + δ)

def PlacesAt (D : D7) (s : Scale) : Prop :=
  s.delta1 * D.R.n / 2 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ 2 * s.delta1 * D.R.n ∧
  s.x ^ (-s.eps) ≤ (D.host.T2.card : ℝ) / D.R.n

def AllLarge (Fm : DFamP) (ε0 : ℝ) (P : D7 → Scale → Prop) : Prop :=
  ∀ ε (h0 : 0 < ε) (h1 : ε < 1 / 52), ε < ε0 → ∃ x0 : ℝ, 1 < x0 ∧
    ∀ x : ℝ, x0 ≤ x → ∀ i : (Fm ε h0 h1).Ix x, P ((Fm ε h0 h1).D x i) ((Fm ε h0 h1).L x i).sc

def AllLargeC (Fm : DFamP) (ε0 : ℝ) (P : D7 → Scale → ℝ → Prop) : Prop :=
  ∀ ε (h0 : 0 < ε) (h1 : ε < 1 / 52), ε < ε0 → ∃ C x0 : ℝ, 0 < C ∧ 1 < x0 ∧
    ∀ x : ℝ, x0 ≤ x → ∀ i : (Fm ε h0 h1).Ix x, P ((Fm ε h0 h1).D x i) ((Fm ε h0 h1).L x i).sc C

def AllLargeAt (Fm : DFamP) (ε0 : ℝ) (P : D7 → Scale → ℝ → Prop) (C : ℝ) : Prop :=
  ∀ ε (h0 : 0 < ε) (h1 : ε < 1 / 52), ε < ε0 → ∃ x0 : ℝ, 1 < x0 ∧
    ∀ x : ℝ, x0 ≤ x → ∃ i : (Fm ε h0 h1).Ix x, P ((Fm ε h0 h1).D x i) ((Fm ε h0 h1).L x i).sc C

def FamilyLemmaOneOne (Fm : DFamP) (ε0 : ℝ) : Prop := AllLarge Fm ε0 (fun D _ => adm1 D)

def FamilyLemmaOneTwo (Fm : DFamP) (ε0 : ℝ) : Prop := AllLarge Fm ε0 (fun D _ => adm2 D)

def FamilyFactsAfterLemmaOneTwo (Fm : DFamP) (ε0 : ℝ) : Prop := AllLarge Fm ε0 (fun D _ => adm3 D)

def FamilyLemmaTwoOne (Fm : DFamP) (ε0 : ℝ) : Prop := AllLargeC Fm ε0 ArchimedeanSignatureMatching

def FamilyPropTwoSix (Fm : DFamP) (ε0 : ℝ) : Prop := AllLargeC Fm ε0 adm5

def FamilyCharacterSumBounds (Fm : DFamP) (ε0 : ℝ) : Prop := AllLargeC Fm ε0 adm6

def TOPF (Fm : DFamP) (ε0 C : ℝ) : Prop := AllLargeAt Fm ε0 adm7 C

def FamilyTopBoundAbsolute (Fm : DFamP) (ε0 : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ TOPF Fm ε0 C

def FamilyCharacterReading (Fm : DFamP) (ε0 : ℝ) : Prop := AllLarge Fm ε0 (fun D _ => adm10 D)

def FamilyRamifiedPrimeValues (Fm : DFamP) (ε0 : ℝ) : Prop := AllLarge Fm ε0 (fun D _ => adm11 D)

def AdmFe (Fm : DFamP) (ε0 : ℝ) : Prop :=
  FamilyLemmaOneOne Fm ε0 ∧ FamilyLemmaOneTwo Fm ε0 ∧ FamilyFactsAfterLemmaOneTwo Fm ε0 ∧ FamilyLemmaTwoOne Fm ε0 ∧ FamilyPropTwoSix Fm ε0 ∧ FamilyCharacterSumBounds Fm ε0 ∧
    FamilyTopBoundAbsolute Fm ε0 ∧ adm8 ∧ adm9 ∧ FamilyCharacterReading Fm ε0 ∧ FamilyRamifiedPrimeValues Fm ε0

def AdmF (Fm : DFamP) : Prop := AdmFe Fm (1 / 52)

def SizesFe (Fm : DFamP) (ε0 : ℝ) : Prop :=
  ∀ ε (h0 : 0 < ε) (h1 : ε < 1 / 52), ε < ε0 → ∀ δ : ℝ, 0 < δ → ∃ x0 : ℝ, 1 < x0 ∧
    ∀ x : ℝ, x0 ≤ x → ∀ i : (Fm ε h0 h1).Ix x,
      SizesAt ((Fm ε h0 h1).D x i) ((Fm ε h0 h1).L x i).sc δ ∧
      PlacesAt ((Fm ε h0 h1).D x i) ((Fm ε h0 h1).L x i).sc

def Conclusion1Family (Fm : DFamP) : Prop := AllLarge Fm (1 / 52) Conclusion1

def Conclusion2Family (Fm : DFamP) : Prop :=
  SizesFe Fm (1 / 52) → ∀ C : ℝ, 0 < C → TOPF Fm (1 / 52) C →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Conclusion2 x ε (C + 3)

def SlopeLemmaFamily (Fm : DFamP) : Prop :=
  (∃ ε0 : ℝ, 0 < ε0 ∧ AdmFe Fm ε0 ∧ SizesFe Fm ε0) → RiemannHypothesis

def ConclusionOnFamily (Fm : DFamP) : Prop := Conclusion1Family Fm ∧ Conclusion2Family Fm ∧ PointsLemma ∧ SlopeLemmaFamily Fm

def KudlaFamilyStatement (Fm : DFamP) : Prop := AdmF Fm → ConclusionOnFamily Fm

end Formalism.MainNotions.ZetaZeroFreeRegion

end
