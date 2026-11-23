import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain MeasureTheory
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

def Zmu (K : Type) [Field K] (g : ℕ) : Subalgebra ℤ K := Algebra.adjoin ℤ {ζ : K | ζ ^ (g * (g - 1)) = 1}

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def FnModAt (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b))
    (Φ : HomE E a b → K) : Prop :=
  (∀ x, Φ x ≠ 0 → x ∈ homAt {P} N N') ∧
  (∀ x z, z ∈ homAt {P} N N' → Φ (x + (qOf P : E) • z) = Φ x) ∧
  ∀ x, Φ x ∈ Zmu K (qOf P)

abbrev FnMod (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (Φ : HomE E a b → K) : Prop :=
  FnModAt P (stdLat E a) (stdLat E b) Φ

def ColFn (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (f : Sp E n → K) : Prop :=
  (∀ y, f y ≠ 0 → (qOf P : E) • y ∈ stdAt E n P) ∧
  (∀ y z, z ∈ stdAt E n P → f (y + z) = f y) ∧
  ∀ y, f y ∈ Zmu K (qOf P)

def InDual (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (ξ : Sp E n →ₗ[E] E) : Prop := ∀ y ∈ stdAt E n P, IntAt P (ξ y)

def DualFn (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (F : (Sp E n →ₗ[E] E) → K) : Prop :=
  (∀ ξ, F ξ ≠ 0 → InDual P ξ) ∧
  (∀ ξ ξ', InDual P ξ' → F (ξ + (qOf P : E) • ξ') = F ξ) ∧
  ∀ ξ, F ξ ∈ Zmu K (qOf P)

omit [StarRing E] in
open Classical in

theorem colFn_indicator (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (y₀ : Sp E n) (h₀ : (qOf P : E) • y₀ ∈ stdAt E n P) :
    ColFn P (fun y => if y - y₀ ∈ stdAt E n P then (1 : K) else 0) := by
  refine ⟨fun y hy => ?_, fun y z hz => ?_, fun y => ?_⟩
  · have h : y - y₀ ∈ stdAt E n P := by
      by_contra h
      exact hy (if_neg h)
    have h1 : (qOf P : E) • (y - y₀) ∈ stdAt E n P := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem h _
    have h2 := add_mem h1 h₀
    rwa [← smul_add, sub_add_cancel] at h2
  · have h1 : y + z - y₀ = (y - y₀) + z := by abel
    simp only [h1, Submodule.add_mem_iff_left _ hz]
  · dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end Notions

section Padic

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

def stdP (g : ℕ) [Fact g.Prime] (n : ℕ) : Set (Fin n → ℚ_[g]) := {y | ∀ i, ‖y i‖ ≤ 1}

def InDualP (ξ : (Fin n → ℚ_[g]) →ₗ[ℚ_[g]] ℚ_[g]) : Prop := ∀ y ∈ stdP g n, ‖ξ y‖ ≤ 1

def repP (t : Fin n → Fin g) : Fin n → ℚ_[g] := fun i => ((t i : ℕ) : ℚ_[g]) / (g : ℚ_[g])

def fourierP [MeasurableSpace (Fin n → ℚ_[g])] (μ : Measure (Fin n → ℚ_[g])) (ψ : AddChar ℚ_[g] ℂ)
    (f : (Fin n → ℚ_[g]) → ℂ) (ξ : (Fin n → ℚ_[g]) →ₗ[ℚ_[g]] ℚ_[g]) : ℂ :=
  ∫ y, f y * (starRingEnd ℂ) (ψ (ξ y)) ∂μ

end Padic

def FourierLattice : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) [MeasurableSpace (Fin n → ℚ_[g])] [BorelSpace (Fin n → ℚ_[g])]
    (μ : Measure (Fin n → ℚ_[g])) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[g] ℂ),
    (∀ a : ℚ_[g], ‖a‖ ≤ 1 → ψ a = 1) → (∃ a : ℚ_[g], ‖(g : ℚ_[g]) * a‖ ≤ 1 ∧ ψ a ≠ 1) →
    ∀ f : (Fin n → ℚ_[g]) → ℂ,
      (∀ y, f y ≠ 0 → (g : ℚ_[g]) • y ∈ stdP g n) → (∀ y z, z ∈ stdP g n → f (y + z) = f y) →
      (∀ ξ : (Fin n → ℚ_[g]) →ₗ[ℚ_[g]] ℚ_[g], Integrable (fun y => f y * (starRingEnd ℂ) (ψ (ξ y))) μ) ∧
      (∀ ξ, fourierP μ ψ f ξ ≠ 0 → InDualP ξ) ∧
      (∀ ξ ξ', InDualP ξ' → fourierP μ ψ f (ξ + (g : ℚ_[g]) • ξ') = fourierP μ ψ f ξ) ∧
      (∀ ξ, InDualP ξ → fourierP μ ψ f ξ =
        (μ.real (stdP g n) : ℂ) * ∑ t : Fin n → Fin g, f (repP t) * (starRingEnd ℂ) (ψ (ξ (repP t)))) ∧
      ((∀ y, f y ∈ Zmu ℂ g) → ∀ ξ, ∃ z ∈ Zmu ℂ g, fourierP μ ψ f ξ = (μ.real (stdP g n) : ℂ) * z)

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def restrX {E : Type} [Field E] {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) : HomE E n' n :=
  LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ x ∘ₗ Loc.inX E n' c'

def colX {E : Type} [Field E] {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) : Sp E n :=
  LinearMap.funLeft E E (Fin.castAdd c) (x (Loc.eN E (n' + c') n'))

def fhat {n : ℕ} (P : rowSG Pr sel mu) (f : Sp X.E n → X.K) (η : Sp X.E n →ₗ[X.E] X.E) : X.K :=
  ∑ y ∈ Fintype.piFinset fun _ : Fin n => LocE.valsQ X.E (qOf P.1) 1 0, f y * ftY sel mu cst P η y

def topDatum (m2 : ℕ) (P : rowSG Pr sel mu) (f : Sp X.E (R.N (m2 + 1)) → X.K) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 (prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    fhat sel mu cst P f (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ x)

def facPen {u : Pr.Word} (m2 : ℕ) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (P : rowSG Pr sel mu) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) : X.K :=
  PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) ((frsF sel mu p P).symm (repY Y))

def facTop {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (P : rowSG Pr sel mu) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((frsF sel mu p P).symm (repY Y))

def SplitAt (m2 : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R m2) : Prop :=
  (∀ x, omPhi Ch sel mu cst m2 P hal 1 x = PsiAt Ch sel mu cst m2 P hal (restrX x) (colX x)) ∧
  ∃ (ι : Type) (_ : Fintype ι) (Ψ : ι → HomE X.E (R.N m2) (R.N (m2 + 1)) → X.K) (f : ι → Sp X.E (R.N (m2 + 1)) → X.K),
    (∀ a, FnMod P.1 (Ψ a)) ∧ (∀ a, ColFn P.1 (f a)) ∧
    ∀ x₀ y, PsiAt Ch sel mu cst m2 P hal x₀ y = ∑ a, Ψ a x₀ * f a y

end Chain

def ChainData : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ), Pr.Ok → cst.Ok → R.m = m2 + 2 →
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
      (∀ hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1), SplitAt Ch sel mu cst m2 P hal) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → DualFn P.1 (fhat sel mu cst P f)) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → FnMod P.1 (topDatum Ch sel mu cst m2 P f)) ∧
      (∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2),
        L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1) →
        ∀ (u : Pr.Word) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P)) ∧
      (∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P))

def LastTwoSteps : Prop := FourierLattice ∧ ChainData

end GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator
