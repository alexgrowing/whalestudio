import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

namespace Formalism.MainNotions.StandardLatticesGL3

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric
open scoped Pointwise

def cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (liftM M x)

def FixK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Prop :=
  ∀ a : D.host.K, D.host.φ₀ ((a : D.host.E)) ∈ M ∧
    cj M ρ (D.host.φ₀ ((a : D.host.E))) = D.host.φ₀ ((a : D.host.E))

def rhoBar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : M →ₐ[ℚ] ℂ :=
  ((Complex.conjAe.toAlgHom).restrictScalars ℚ).comp ρ

def ee (t : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

def Mod1All (x : ℂ) : Prop := ∃ h : x ∈ Qbar, ∀ σ : Qbar →+* ℂ, ‖σ ⟨x, h⟩‖ = 1

def Crv (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ

def wpF (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ :=
  1 / z ^ 2 + ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, (1 / (z - (w : ℂ)) ^ 2 - 1 / (w : ℂ) ^ 2)

def wpD (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := -2 * ∑' w : Λ, 1 / (z - (w : ℂ)) ^ 3

def StarPt (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (t t' : ℂ) : Prop :=
  (t ∈ Λ ∧ t' ∈ lamConj M ρ Λ) ∨
  (t ∉ Λ ∧ t' ∉ lamConj M ρ Λ ∧ wpF Λ t ∈ M ∧ wpD Λ t ∈ M ∧
    wpF (lamConj M ρ Λ) t' = cj M ρ (wpF Λ t) ∧ wpD (lamConj M ρ Λ) t' = cj M ρ (wpD Λ t))

def Adp1 (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (n : ℕ) (x x' : ℂ) : Prop :=
  StarPt M ρ Λ (x / (n : ℂ)) (x' / (n : ℂ))

def InRationalLattice (Λ : AddSubgroup ℂ) (x : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ (m : ℂ) * x ∈ Λ

def coef1 (g : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n g 0 / (n.factorial : ℂ)

def gl3FieldFirst (Λ : AddSubgroup ℂ) (z w : ℂ) : ℝ := (z * (starRingEnd ℂ) w).im / area Λ

def q1 (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : ℝ := Real.sqrt D.host.d / 2 * (‖x‖ ^ 2 / area Λ)

def w0 (D : D7) : ℂ := (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2

def nrm1Sq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)

def galCurve (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → ∀ n : ℕ, 0 < n →
      ∃ (cc' : Ideal (𝓞 D.host.K)) (δ' : ℂ), Crv D cc' δ' ∧ Nat.Coprime (Ideal.absNorm cc') n ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D cc' δ'

def galStar (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      (∀ t, InRationalLattice (lamOf D cc δ) t → (t ∈ lamOf D cc δ ∨ (wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M)) →
        ∃ t', StarPt M ρ (lamOf D cc δ) t t') ∧
      (∀ t t₁ t₂, StarPt M ρ (lamOf D cc δ) t t₁ →
        (StarPt M ρ (lamOf D cc δ) t t₂ ↔ t₁ - t₂ ∈ lamConj M ρ (lamOf D cc δ))) ∧
      (∀ t t' ω, StarPt M ρ (lamOf D cc δ) t t' → ω ∈ lamOf D cc δ → StarPt M ρ (lamOf D cc δ) (t + ω) t') ∧
      (∀ t t' u u', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) u u' →
        StarPt M ρ (lamOf D cc δ) (t + u) (t' + u')) ∧
      (∀ (a : 𝓞 D.host.K) t t', StarPt M ρ (lamOf D cc δ) t t' →
        StarPt M ρ (lamOf D cc δ) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t)
          (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) ∧
      (∀ (n : ℕ) t t', StarPt M ρ (lamOf D cc δ) t t' →
        ((n : ℂ) * t ∈ lamOf D cc δ ↔ (n : ℂ) * t' ∈ lamConj M ρ (lamOf D cc δ))) ∧
      (∀ n : ℕ, 0 < n →
        (∀ t, (n : ℂ) * t ∈ lamOf D cc δ → t ∉ lamOf D cc δ →
          wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) →
        ∀ t', (n : ℂ) * t' ∈ lamConj M ρ (lamOf D cc δ) →
          ∃ t, (n : ℂ) * t ∈ lamOf D cc δ ∧ StarPt M ρ (lamOf D cc δ) t t')

def galSg (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → (∀ n, coef1 (sgStar (lamOf D cc δ)) n ∈ M) →
      ∀ n, cj M ρ (coef1 (sgStar (lamOf D cc δ)) n) = coef1 (sgStar (lamConj M ρ (lamOf D cc δ))) n

def gal1 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      ∀ (x x' : ℂ) (m : ℕ), 0 < m → (m : ℂ) * (x / 2) ∈ lamOf D cc δ →
        Adp1 M ρ (lamOf D cc δ) (2 * m) x x' →
        (∀ n, coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n ∈ M) →
        ∀ n, cj M ρ (coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n) =
          coef1 (U1 (lamConj M ρ (lamOf D cc δ)) x' (sgStar (lamConj M ρ (lamOf D cc δ)))) n

def transInv (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (x ω : ℂ) (m : ℕ), 0 < m → (m : ℂ) * (x / 2) ∈ lamOf D cc δ → ω ∈ lamOf D cc δ →
      U1 (lamOf D cc δ) (x + 2 * (m : ℂ) * ω) (sgStar (lamOf D cc δ)) =
        U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))

def WeilPairingGaloisAlt (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      ∀ (a b a' b' : ℂ) (m : ℕ), 0 < m → (m : ℂ) * a ∈ lamOf D cc δ → (m : ℂ) * b ∈ lamOf D cc δ →
        Adp1 M ρ (lamOf D cc δ) m a a' → Adp1 M ρ (lamOf D cc δ) m b b' →
        ee (gl3FieldFirst (lamOf D cc δ) a b) ∈ M →
        cj M ρ (ee (gl3FieldFirst (lamOf D cc δ) a b)) = ee (gl3FieldFirst (lamConj M ρ (lamOf D cc δ)) a' b')

def galPh1 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    (∀ x : ℂ, q1 D (lamOf D cc δ) x = gl3FieldFirst (lamOf D cc δ) (w0 D * x) x) ∧
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      ∀ (x x' : ℂ) (m₀ : ℕ), 0 < m₀ → (m₀ : ℂ) * x ∈ lamOf D cc δ →
        Adp1 M ρ (lamOf D cc δ) (2 * m₀) x x' → ee (q1 D (lamOf D cc δ) x / 2) ∈ M →
        cj M ρ (ee (q1 D (lamOf D cc δ) x / 2)) = ee (q1 D (lamConj M ρ (lamOf D cc δ)) x' / 2)

def SD (D : D7) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSDLat D.host.E N L

def LaQ (D : D7) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : VC D N N') : Prop :=
  ∃ m : ℕ, 0 < m ∧ m • x ∈ La D T L L'

def AdpV (D : D7) (T : Tor D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (n : ℕ) (x x' : VC D N N') : Prop :=
  ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c c' : Fin r → ℂ),
    (∀ j, b j ∈ YYl D L L') ∧ (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
    x = ∑ j, c j • embV D T (b j) ∧ x' = ∑ j, c' j • embV D (torConj D T M ρ) (b j) ∧
    ∀ j, Adp1 M ρ T.abelian₂ n (c j) (c' j)

def wdPh (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ℂ := ee (qH D T x / 2)

def Wd (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => wdPh D T x * U D T x G z

def comb (D : D7) (T : Tor D) {N N' k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N')
    (e₀ : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ∑ i, c i * U D T (t i) e₀ z

def gal (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ) (x x' : VC D N N') (m₀ : ℕ),
      e₀ ∈ Th D (tor0 D cc δ) L L' → 0 < m₀ → m₀ • x ∈ La D (tor0 D cc δ) L L' →
      (∀ i, m₀ • t i ∈ La D (tor0 D cc δ) L L') →
      AdpV D (tor0 D cc δ) M ρ L L' (2 * m₀) x x' →
      CoefIn D (comb D (tor0 D cc δ) c t e₀) M →
      CoefIn D (U D (tor0 D cc δ) x (comb D (tor0 D cc δ) c t e₀)) M →
      fnConj D M ρ (U D (tor0 D cc δ) x (comb D (tor0 D cc δ) c t e₀)) =
        U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ (comb D (tor0 D cc δ) c t e₀)) ∧
      (wdPh D (tor0 D cc δ) x ∈ M →
        cj M ρ (wdPh D (tor0 D cc δ) x) = wdPh D (torConj D (tor0 D cc δ) M ρ) x' ∧
        fnConj D M ρ (Wd D (tor0 D cc δ) x (comb D (tor0 D cc δ) c t e₀)) =
          Wd D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ (comb D (tor0 D cc δ) c t e₀))) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (∃ j : ℕ, p ^ j • x ∈ La D (tor0 D cc δ) L L') →
        fnConj D M ρ (Wop D (tor0 D cc δ) p x (comb D (tor0 D cc δ) c t e₀)) =
          Wop D (torConj D (tor0 D cc δ) M ρ) p x' (fnConj D M ρ (comb D (tor0 D cc δ) c t e₀)))

def galEx (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M →
    (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ lamOf D cc δ → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ (x : VC D N N') (n : ℕ), LaQ D (tor0 D cc δ) L L' x → 0 < n →
      ∃ x', AdpV D (tor0 D cc δ) M ρ L L' n x x' ∧ LaQ D (torConj D (tor0 D cc δ) M ρ) L L' x'

def coordB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (j : Fin r)
    (z : VC D N N') : ℂ :=
  ∑ τ, ∑ a, ∑ c, z τ a c * (starRingEnd ℂ) (T.emb τ (b j a c))

def pullB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ) :
    VC D N N' → ℂ :=
  fun z => ∏ j, g (coordB D T b j z)

def LaB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {z | ∃ w ∈ T.abelian₂, ∃ j, z = w • embV D T (b j)}

def OnB (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  Orthonormal D b ∧ Submodule.span D.host.K (Set.range b) = ⊤

def ThetaVectorUpToUnits (D : D7) (T : Tor D) (t0 : ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (G : VC D N N' → ℂ) : Prop :=
  ∃ (b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E) (κ : ℂ), OnB D b ∧ Mod1All κ ∧
    G = fun z => κ * Iop D T (LaB D T b) (La D T L L') (pullB D T b (GL3Theta.th0 T.abelian₂ t0)) z

def subLa {V : Type*} [AddCommGroup V] (m : ℕ) (A : AddSubgroup V) : AddSubgroup V :=
  A.map (nsmulAddMonoidHom m)

def AdpB (D : D7) (T : Tor D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (x x' : VC D N N') : Prop :=
  ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
    x = ∑ j, c j • embV D T (b j) ∧ x' = ∑ j, c' j • embV D (torConj D T M ρ) (b j) ∧
    ∀ j, Adp1 M ρ T.abelian₂ n (c j) (c' j)

def galB (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M →
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b →
    ∀ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (x x' : VC D N N') (m₀ : ℕ),
      0 < m₀ → m₀ • x ∈ LaB D (tor0 D cc δ) b → (∀ i, m₀ • t i ∈ LaB D (tor0 D cc δ) b) →
      AdpB D (tor0 D cc δ) M ρ b (2 * m₀) x x' →
      CoefIn D (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) M →
      CoefIn D (U D (tor0 D cc δ) x
        (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))))) M →
      fnConj D M ρ (U D (tor0 D cc δ) x
          (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))))) =
        U D (torConj D (tor0 D cc δ) M ρ) x'
          (fnConj D M ρ (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))))) ∧
      (wdPh D (tor0 D cc δ) x ∈ M →
        cj M ρ (wdPh D (tor0 D cc δ) x) = wdPh D (torConj D (tor0 D cc δ) M ρ) x' ∧
        fnConj D M ρ (Wd D (tor0 D cc δ) x
            (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))))) =
          Wd D (torConj D (tor0 D cc δ) M ρ) x'
            (fnConj D M ρ (comb D (tor0 D cc δ) c t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))))))

def t0Ex (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    (∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) ∧
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      ∃ t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0'

def use1 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    (∀ x, InRationalLattice (lamOf D cc δ) x → ∀ n, coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n ∈ Qbar) ∧
    (∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ n, coef1 (GL3Theta.th0 (lamOf D cc δ) t0) n ∈ Qbar) ∧
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      ∀ t0 t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0' →
        (∀ n, coef1 (GL3Theta.th0 (lamOf D cc δ) t0) n ∈ M) →
        ∀ n, cj M ρ (coef1 (GL3Theta.th0 (lamOf D cc δ) t0) n) = coef1 (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') n

def useAlg (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → Even (N * N') →
    ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      CoefIn D G Qbar ∧
      (∀ x, LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x G) Qbar) ∧
      (∀ (k : ℕ) (a : Fin k → ℂ) (t : Fin k → VC D N N'), (∀ j, a j ∈ Qbar) →
        (∀ j, LaQ D (tor0 D cc δ) L L' (t j)) → CoefIn D (comb D (tor0 D cc δ) a t G) Qbar) ∧
      (∀ L₁ L₁', SD D L₁ → SD D L₁' →
        CoefIn D (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') G) Qbar) ∧
      ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
        Nat.Coprime (Ideal.absNorm cc) p →
        ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (ε : 𝓞 D.host.K)
          (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ), NNBasis D (tor0 D cc δ) δ p L L' b →
          IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ → (∀ a, Φ a ∈ Qbar) →
          CoefIn D (XiF D (tor0 D cc δ) δ p n ε b Φ G) Qbar

def useConj (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → Even (N * N') →
    ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), DataIn D (tor0 D cc δ) M → CoefIn D G M →
      fnConj D M ρ G ∈ Th D (torConj D (tor0 D cc δ) M ρ) L L' ∧
      (∀ t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0' →
        ThetaVectorUpToUnits D (torConj D (tor0 D cc δ) M ρ) t0' L L' (fnConj D M ρ G)) ∧
      ∀ L₁ L₁', SD D L₁ → SD D L₁' →
        CoefIn D (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') G) M →
        ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧
          fnConj D M ρ (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') G) =
            fun z => sg * Iop D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
              (La D (torConj D (tor0 D cc δ) M ρ) L₁ L₁') (fnConj D M ρ G) z

def useNorm (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → Even (N * N') →
    ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), DataIn D (tor0 D cc δ) M → CoefIn D G M →
    ∀ t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0' →
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ G) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') ∧
      ∀ x, LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x G) M →
        normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
            (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
          nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N')

def phiNormSq {p r : ℕ} [Fact p.Prime] (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (n : ℕ)
    (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ) : ℝ :=
  ((p : ℝ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), ‖cj M ρ (Φ (fun i => (((a i : ℕ) : ℤ_[p]))))‖ ^ 2

def useXi (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → Even (N * N') →
    ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
      Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (ε : 𝓞 D.host.K)
      (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ), NNBasis D (tor0 D cc δ) δ p L L' b →
      IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), DataIn D (tor0 D cc δ) M → CoefIn D G M →
      (∀ a, Φ a ∈ M) → CoefIn D (XiF D (tor0 D cc δ) δ p n ε b Φ G) M →
      normSq D (torConj D (tor0 D cc δ) M ρ) (subLa (p ^ n) (La D (torConj D (tor0 D cc δ) M ρ) L L'))
          (fnConj D M ρ (XiF D (tor0 D cc δ) δ p n ε b Φ G)) =
        phiNormSq M ρ n Φ *
          normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ G) ∧
      ((∀ a, Φ a = 0 ∨ ∃ (ζ s : ℂ) (m : ℕ) (k : ℤ), 0 < m ∧ ζ ^ m = 1 ∧ s ^ 2 = (p : ℂ) ∧ Φ a = ζ * s ^ k) →
        phiNormSq M ρ n Φ =
          ((p : ℝ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), ‖Φ (fun i => (((a i : ℕ) : ℤ_[p])))‖ ^ 2)

def usePsi : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (m : ℕ), 0 < m → (∀ ζ : ℂ, ζ ^ m = 1 → ζ ∈ M) →
    ∃ c : ℕ, Nat.Coprime c m ∧ ∀ ψ : AddChar (ZMod m) ℂ, ∀ a, cj M ρ (ψ a) = ψ a ^ c

def useLine (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∃ G ∈ Th D (tor0 D cc δ) L L', G ≠ 0 ∧ CoefIn D G Qbar ∧
      ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' →
        fnConj D Qbar ρ G ∈ Th D (torConj D (tor0 D cc δ) Qbar ρ) L L' ∧
        normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
            (fnConj D Qbar ρ G) =
          nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * N * N')

def torBar (D : D7) (T : Tor D) : Tor D :=
  ⟨fun τ x => (starRingEnd ℂ) (T.emb τ x), T.abelian₂.map (starRingEnd ℂ).toAddMonoidHom⟩

def vBar (D : D7) {N N' : ℕ} (z : VC D N N') : VC D N N' := fun τ i j => (starRingEnd ℂ) (z τ i j)

def cBar (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => (starRingEnd ℂ) (G (vBar D z))

def useBar (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), DataIn D (tor0 D cc δ) M →
      (FixK D M ρ ∨ FixK D M (rhoBar M ρ)) ∧
      torConj D (tor0 D cc δ) M (rhoBar M ρ) = torBar D (torConj D (tor0 D cc δ) M ρ) ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (G : VC D N N' → ℂ),
        fnConj D M (rhoBar M ρ) G = cBar D (fnConj D M ρ G) ∧
        (∀ x, cBar D (U D (torConj D (tor0 D cc δ) M ρ) x G) =
          U D (torBar D (torConj D (tor0 D cc δ) M ρ)) (vBar D x) (cBar D G)) ∧
        (G ∈ Th D (torConj D (tor0 D cc δ) M ρ) L L' →
          cBar D G ∈ Th D (torBar D (torConj D (tor0 D cc δ) M ρ)) L L' ∧
          (SD D L → SD D L' → ∀ x,
            normSq D (torBar D (torConj D (tor0 D cc δ) M ρ))
                (La D (torBar D (torConj D (tor0 D cc δ) M ρ)) L L')
                (cBar D (U D (torConj D (tor0 D cc δ) M ρ) x G)) =
              normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
                (U D (torConj D (tor0 D cc δ) M ρ) x G)))

open TensorProduct in

abbrev AE (D : D7) : Type := D.host.E ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

def sgA (D : D7) : AE D →+* AE D :=
  Formalism.UG.sigR (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)

def inc (D : D7) : D.host.E →+* AE D :=
  Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)

def OhE (D : D7) : Subring (AE D) :=
  Formalism.UG.tensInt (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (Formalism.UG.intOE D.host.E) (Formalism.UG.intAd ℚ)

def GA (D : D7) (N : ℕ) : Subgroup (GL (Fin N) (AE D)) :=
  Formalism.UG.UPts (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (1 : Matrix (Fin N) (Fin N) D.host.E)
    (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)

def ZeroAt (D : D7) (q : ℕ) (x : AE D) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m q ∧ ∃ s ∈ OhE D, (m : AE D) * x = (q : AE D) ^ k * s

def TrivAt (D : D7) {N : ℕ} (q : ℕ) (g : GL (Fin N) (AE D)) : Prop :=
  ∀ i j, ZeroAt D q ((g : Matrix (Fin N) (Fin N) (AE D)) i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j)

def InertQ (D : D7) (q : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P ≠ ⊥ → (q : 𝓞 D.host.E) ∈ P → (D.host.conj : _) • P = P

def SuppSplit (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) : Prop := ∀ q : ℕ, q.Prime → InertQ D q → TrivAt D q g

def SuppInert (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) : Prop := ∀ q : ℕ, q.Prime → ¬ InertQ D q → TrivAt D q g

def IntG (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) : Prop :=
  ∀ i j, (g : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D ∧
    ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D

def stdL (D : D7) (N : ℕ) : Submodule (𝓞 D.host.E) (Fin N → D.host.E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

def Moves (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∀ x : Fin N → D.host.E, x ∈ L₁ ↔
    ∀ i, (((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec (fun j => inc D (x j))) i ∈ OhE D

def IsRat (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (g : Matrix (Fin N) (Fin N) (AE D)) = γ.map (inc D)

def sgU (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (sgA D).toMonoidHom

def IntU (D : D7) (u : (AE D)ˣ) : Prop := (u : AE D) ∈ OhE D ∧ ((u⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D

structure HeckeU (D : D7) (N : ℕ) where
  f : (AE D)ˣ →* ℂˣ
  n : D.what₂.Tau → ℤ
  unitary : ∀ x, ‖((f x : ℂˣ) : ℂ)‖ = 1
  cont : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → f u = 1
  aut : ∀ a : D.host.Eˣ, ((f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
    ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (n τ) = 1
  norm : ∀ x, f (x * sgU D x) = 1
  par : ∀ τ, Even (n τ - (N : ℤ))
  unr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → f u = 1

theorem HeckeU.sq_AF {D : D7} {N : ℕ} (χ : HeckeU D N) (t : (AE D)ˣ) (ht : sgU D t = t) : χ.f t ^ 2 = 1 := by
  have h := χ.norm t
  rw [ht, ← sq, map_pow] at h
  exact h

def pt (D : D7) (T : Tor D) (δ : ℂ) {N N' : ℕ} (z : Matrix (Fin N') (Fin N) D.host.E) : VC D N N' :=
  δ • embV D T z

def IhE (D : D7) (cc : Ideal (𝓞 D.host.K)) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ c ∈ cc, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s ∈ OhE D,
    y = inc D ((((c : D.host.K) : D.host.E)) * a) * s}

def CloseTo (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (m : ℕ) (g : GL (Fin N) (AE D))
    (g' : GL (Fin N') (AE D)) (z z' : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∀ i j, ∃ y ∈ IhE D cc,
    (z'.map (inc D) - (g' : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j = (m : AE D) * y

def La0 (D : D7) (T : Tor D) (N N' : ℕ) : AddSubgroup (VC D N N') := La D T (stdL D N) (stdL D N')

def TT (D : D7) (T : Tor D) (N N' : ℕ) : Set (VC D N N' → ℂ) :=
  {F | Differentiable ℂ F ∧ ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D T N N', Wd D T (m • x) F = F}

structure WeilO (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) where
  nz : e0 ≠ 0
  chV : HeckeU D N
  chV' : HeckeU D N'
  ep : ℤ
  ep' : ℤ
  ep_pm : (ep = 1 ∨ ep = -1) ∧ (ep' = 1 ∨ ep' = -1)
  Om : GA D N → GA D N' → (VC D N N' → ℂ) → (VC D N N' → ℂ)
  maps : ∀ g g', ∀ F ∈ TT D (tor0 D cc δ) N N', Om g g' F ∈ TT D (tor0 D cc δ) N N'
  add : ∀ g g', ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ F' ∈ TT D (tor0 D cc δ) N N',
    Om g g' (F + F') = Om g g' F + Om g g' F'
  smul : ∀ g g' (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', Om g g' (a • F) = a • Om g g' F
  one : ∀ F ∈ TT D (tor0 D cc δ) N N', Om 1 1 F = F
  mul : ∀ g₁ g₂ g₁' g₂', ∀ F ∈ TT D (tor0 D cc δ) N N', Om (g₁ * g₂) (g₁' * g₂') F = Om g₁ g₁' (Om g₂ g₂' F)
  lift : ∀ (g : GA D N) (g' : GA D N') (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N',
    ∃ m : ℕ, 0 < m ∧ ∀ z', CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z z' →
      Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) =
        Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (Om g g' F)
  inert : ∀ (k : GA D N) (k' : GA D N'), IntG D (k : GL (Fin N) (AE D)) → IntG D (k' : GL (Fin N') (AE D)) →
    SuppInert D (k : GL (Fin N) (AE D)) → SuppInert D (k' : GL (Fin N') (AE D)) → Om k k' e0 = e0
  split : ∀ (g : GA D N) (g' : GA D N') (x x' : (AE D)ˣ) L₁ L₁',
    SuppSplit D (g : GL (Fin N) (AE D)) → SuppSplit D (g' : GL (Fin N') (AE D)) →
    (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1) ∧ ZeroAt D q ((x' : AE D) - 1)) →
    x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x →
    x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D)) * sgU D x' →
    Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' →
    Om g g' e0 = fun z => ((chV.f x' ^ ep * chV'.f x ^ ep' : ℂˣ) : ℂ) *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z

def DatS (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (e0 : VC D N N' → ℂ) (S : Finset ℕ) {p : ℕ}
    [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (F : VC D N N' → ℂ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E),
    (∀ i, r i ∈ Qbar ∧ ‖lamC lam (r i)‖ ≤ 1) ∧
    (∀ i, ∃ m : ℕ, 0 < m ∧ (∀ q : ℕ, q.Prime → q ∣ m → q ∈ S) ∧
      m • pt D (tor0 D cc δ) δ (z i) ∈ La0 D (tor0 D cc δ) N N') ∧
    F = fun y => ∑ i, r i * Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 y

def lenQ (D : D7) {N : ℕ} (L₀ L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : ℕ :=
  (Module.length (𝓞 D.host.E) (L₀ ⧸ Submodule.comap L₀.subtype L₁)).toNat

def odd1 (D : D7) : Prop :=
  ∀ N N' : ℕ, Even (N * N') → ∀ p : ℕ, p.Prime →
    ∃ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E,
      OnB D b ∧ LocBasis D p (YYl D (stdL D N) (stdL D N')) b

def LocForm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), Nat.Coprime (Ideal.absNorm cc) p →
    ∃ (b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E) (ε : ℂ),
      OnB D b ∧ LocBasis D p (YYl D (stdL D N) (stdL D N')) b ∧ ε ∈ Qbar ∧ ‖lamC lam ε‖ = 1 ∧
      Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La0 D (tor0 D cc δ) N N')).index) p ∧
      e0 = fun z => ε * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (La0 D (tor0 D cc δ) N N')
        (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z

def oddE0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N') ∧ CoefIn D e0 Qbar ∧
  normSq D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') e0 =
    nrm1Sq (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t0) ^ (fF D * N * N') ∧
  ThetaVectorUpToUnits D (tor0 D cc δ) t0 (stdL D N) (stdL D N') e0 ∧ LocForm D cc δ t0 N N' e0

def oddKer (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : WeilO D cc δ N N' e0) (S : Finset ℕ), (∀ q ∈ S, q.Prime ∧ AllSplit D q) →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → Nat.Coprime (Ideal.absNorm cc) p →
    ∀ F, DatS D cc δ e0 S lam F → ∀ (g : GA D N) (g' : GA D N'),
      TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p (g' : GL (Fin N') (AE D)) →
      ∃ (u : ℂ) (b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E) (k : ℕ) (r : Fin k → ℂ)
        (s : Fin k → VC D N N'),
        u ∈ Qbar ∧ ‖lamC lam u‖ = 1 ∧ OnB D b ∧ LocBasis D p (YYl D (stdL D N) (stdL D N')) b ∧
        (∀ i, r i ∈ Qbar ∧ ‖lamC lam (r i)‖ ≤ 1) ∧
        (∀ i, TorsPrime D p (La0 D (tor0 D cc δ) N N') (s i)) ∧
        W.Om g g' F = fun z => u * ∑ i, r i *
          U D (tor0 D cc δ) (s i) (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z

def odd3 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even (N * N') →
    ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0)
      (g : GA D N) (g' : GA D N') L₁ L₁',
      SuppInert D (g : GL (Fin N) (AE D)) → SuppInert D (g' : GL (Fin N') (AE D)) →
      Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' →
      W.Om g g' e0 = fun z => (-1 : ℂ) ^ (N * lenQ D (stdL D N') L₁' + N' * lenQ D (stdL D N) L₁) *
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z

def SplitComp (D : D7) (u z : (AE D)ˣ) : Prop :=
  ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q ((z : AE D) - 1)) ∧ (¬ InertQ D q → ZeroAt D q ((z : AE D) - (u : AE D)))

def odd4 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even (N * N') →
    ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ (W : WeilO D cc δ N N' e0)
      (g : GA D N) (g' : GA D N') L₁ L₁' (c : ℂ),
      Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' →
      (W.Om g g' e0 = fun z => c *
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) →
      (∀ z z' x x' : (AE D)ˣ,
        SplitComp D (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) z →
        SplitComp D (Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D))) z' →
        x = z * sgU D x → x' = z' * sgU D x' →
        ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧
          c ^ 2 = sg * (((W.chV.f x' ^ 2) ^ W.ep * (W.chV'.f x ^ 2) ^ W.ep' : ℂˣ) : ℂ)) ∧
      ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
        TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p (g' : GL (Fin N') (AE D)) →
        c ∈ Qbar ∧ ‖lamC lam c‖ = 1

def IntAt (D : D7) (T : Tor D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Cmb : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] → Prop) : Prop :=
    (p ≠ D.host.d → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], Cmb F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        Orthonormal D b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)) ∧
      JetsInt D lam (YYl D L L') F ∧
      ((p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
        ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F))) ∧
    (p = D.host.d →
      ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧
        ∃ u : D.what₂.Tau → ℂ_[p], (∀ τ, ‖u τ‖ = 1) ∧ (∀ τ, u (tauSg D τ) = u τ) ∧
          ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
            (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
          (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, LocBasisW D (tauEmb D lam τ) L' (P' τ)) →
          DualB D P → DualB D P' →
          ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], Cmb F →
          ∃ F₀, F = expMv (-(algebraMap ℂ_[p] _ S) * QdB D lam u P P') * F₀ ∧
            JetsInt D lam (YYl D L L') F₀)

def IsCombO (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} {e0 : VC D N N' → ℂ}
    (W : WeilO D cc δ N N' e0) (S : Finset ℕ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (t : Fin m → VC D N N') (g : Fin m → GA D N) (g' : Fin m → GA D N')
    (Φ : Fin m → VC D N N' → ℂ),
    (∀ k, IsIntP (r k)) ∧ (∀ k, TorsPrime D p (La0 D (tor0 D cc δ) N N') (t k)) ∧
    (∀ k, TrivAt D p (g k : GL (Fin N) (AE D)) ∧ TrivAt D p (g' k : GL (Fin N') (AE D))) ∧
    (∀ k, DatS D cc δ e0 S lam (Φ k)) ∧
    F = ∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) *
      pSer D lam (U D (tor0 D cc δ) (t k) (W.Om (g k) (g' k) (Φ k)))

def oddInt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : WeilO D cc δ N N' e0) (S : Finset ℕ), (∀ q ∈ S, q.Prime ∧ AllSplit D q) →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → Nat.Coprime (Ideal.absNorm cc) p →
      IntAt D (tor0 D cc δ) lam (stdL D N) (stdL D N') (IsCombO D cc δ W S lam)

def MomAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p])
    {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) : Prop :=
  ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
    (∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
      (∀ a, g a = ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam G) = μ g) ∧
    ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
      IsIdem D lam (2 * n + 2) ε → (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
      ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
        (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
        jet D lam y (pSer D lam (XiF D (tor0 D cc δ) δ p n ε b Φ G)) = μ g

def oddMom (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : WeilO D cc δ N N' e0) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧
      ∀ (g : GA D N) (g' : GA D N') L₁ L₁' (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p (g' : GL (Fin N') (AE D)) →
        Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' →
        NNBasis D (tor0 D cc δ) δ p L₁ L₁' b → MomAt D cc δ lam Ω b (W.Om g g' e0)

def oddRep (D : D7) : Prop :=
  ∀ (N p : ℕ), p.Prime → ∀ g : GA D N, ∃ (γA k : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E),
    IsRat D (γA : GL (Fin N) (AE D)) γ ∧ IntG D (k : GL (Fin N) (AE D)) ∧
      TrivAt D p ((γA * g * k : GA D N) : GL (Fin N) (AE D))

def oddEq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : WeilO D cc δ N N' e0) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (a a' : D.what₂.Tau → ℤ),
    IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' →
    (∀ τ, 2 * a' τ = W.ep * W.chV.n τ + (N : ℤ)) → (∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) →
    ∀ F ∈ TT D (tor0 D cc δ) N N',
      W.Om γA γA' F = fun z => (∏ τ, embT D τ γ.det ^ (-(a τ)) * embT D τ γ'.det ^ (-(a' τ))) *
        pull D (tor0 D cc δ) γ γ' F z

def odd (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ N N' : ℕ, Even (N * N') → ∃ e0 : VC D N N' → ℂ,
      oddE0 D cc δ t0 N N' e0 ∧ oddKer D cc δ t0 N N' e0 ∧ oddInt D cc δ N N' e0 ∧ oddMom D cc δ N N' e0 ∧
        oddEq D cc δ N N' e0

def KLat (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) : Prop :=
  (∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b ∧ A = LaB D T b) ∨
  (∃ L L', SD D L ∧ SD D L' ∧ A = La D T L L')

def IntertwinerUnitary (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N')),
    KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ th ∈ ThSp D (tor0 D cc δ) A₁,
      (∀ x, normSq D (tor0 D cc δ) A₁ (U D (tor0 D cc δ) x th) = normSq D (tor0 D cc δ) A₁ th) ∧
      Iop D (tor0 D cc δ) A₁ A₂ th ∈ ThSp D (tor0 D cc δ) A₂ ∧
      normSq D (tor0 D cc δ) A₂ (Iop D (tor0 D cc δ) A₁ A₂ th) = normSq D (tor0 D cc δ) A₁ th ∧
      Iop D (tor0 D cc δ) A₂ A₁ (Iop D (tor0 D cc δ) A₁ A₂ th) = th

def GaussSumTripleConstant (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')),
    KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ →
    ∀ th ∈ ThSp D (tor0 D cc δ) A₁, ∃ μ : ℂ, μ ^ 8 = 1 ∧
      Iop D (tor0 D cc δ) A₂ A₃ (Iop D (tor0 D cc δ) A₁ A₂ th) =
        fun z => μ * Iop D (tor0 D cc δ) A₁ A₃ th z

def LemmaCGaussConstant (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ (N N' r : ℕ) (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D b' →
    ∃ (c ζ : ℂ) (m : ℕ), 0 < m ∧ ζ ^ m = 1 ∧
      c ^ 2 = ζ * D.host.φ₀ (((Matrix.of fun i j => hYY D (b' j) (b i)).det : D.host.K) : D.host.E) ∧
      pullB D (tor0 D cc δ) b' (GL3Theta.th0 (lamOf D cc δ) t0) = fun z => c *
        Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (LaB D (tor0 D cc δ) b')
          (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z

def TraceMapNormalisation (D : D7) : Prop :=
  ∀ y : D.host.E, ∑ τ, embT D τ y = D.host.φ₀ ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E)

def admG1 (D : D7) : Prop := GL3Theta.InducedCMType D ∧ TraceMapNormalisation D

def admissible_poisson (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even (N * N') →
    ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ W : WeilO D cc δ N N' e0,
    ∃ a a' : D.what₂.Tau → ℤ, ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E),
      IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' →
      ∀ F ∈ TT D (tor0 D cc δ) N N',
        W.Om γA γA' F = fun z => (∏ τ, embT D τ γ.det ^ (-(a τ)) * embT D τ γ'.det ^ (-(a' τ))) *
          pull D (tor0 D cc δ) γ γ' F z

def EmbeddingPermutesTypes (D : D7) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → (∀ τ x, embT D τ x ∈ M) →
    ∃ π : Equiv.Perm D.what₂.Tau, ∀ τ x, cj M ρ (embT D τ x) = embT D (π τ) x

def StatementGaloisCurve (D : D7) : Prop := galCurve D
def StatementGaloisStar (D : D7) : Prop := galStar D
def StatementGaloisSubgroup (D : D7) : Prop := galStar D → galSg D
def StatementTranslationInvariant (D : D7) : Prop := transInv D
def StatementGaloisFirst (D : D7) : Prop := galStar D → galSg D → transInv D → gal1 D
def StatementGaloisPhase (D : D7) : Prop := galStar D → WeilPairingGaloisAlt D → galPh1 D

def StatementGaloisBase (D : D7) : Prop := WeilPairingGaloisAlt D → admG1 D → galStar D → gal1 D → galPh1 D → galB D

def StatementGaloisTheta (D : D7) : Prop := WeilPairingGaloisAlt D → admG1 D → galStar D → galB D → gal D
def StatementGaloisExtension (D : D7) : Prop := galStar D → galEx D
def StatementBasePointExists (D : D7) : Prop := galCurve D → useBar D → t0Ex D
def StatementFirstUse (D : D7) : Prop := galStar D → gal1 D → use1 D
def StatementAlgebraicUse (D : D7) : Prop := admG1 D → gal D → galB D → galEx D → use1 D → useAlg D
def StatementConjugateUse (D : D7) : Prop := admG1 D → gal D → galB D → galEx D → use1 D → useAlg D → useBar D → useConj D
def StatementNormUse (D : D7) : Prop :=
  admG1 D → galCurve D → EmbeddingPermutesTypes D → useConj D → gal D → galEx D → useBar D → IntertwinerUnitary D → useNorm D
def StatementXiUse (D : D7) : Prop :=
  admG1 D → galCurve D → EmbeddingPermutesTypes D → useConj D → gal D → galEx D → WeilPairingGaloisAlt D → useBar D → IntertwinerUnitary D → useXi D
def StatementInducedType : Prop := usePsi
def StatementLineUse (D : D7) : Prop :=
  admG1 D → galCurve D → EmbeddingPermutesTypes D → gal D → galB D → galEx D → use1 D → useBar D → IntertwinerUnitary D → useLine D
def StatementBarUse (D : D7) : Prop := GL3Theta.InducedCMType D → useBar D
def StatementOddFirst (D : D7) : Prop := odd1 D

def StatementOddVectorExists (D : D7) : Prop :=
  admG1 D → odd1 D → IntertwinerUnitary D → GaussSumTripleConstant D → LemmaCGaussConstant D → useAlg D →
    ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
      ∀ N N' : ℕ, Even (N * N') → ∃ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0
def StatementOddThird (D : D7) : Prop := admG1 D → IntertwinerUnitary D → GaussSumTripleConstant D → odd3 D
def StatementOddFourth (D : D7) : Prop := admG1 D → IntertwinerUnitary D → odd3 D → odd4 D
def StatementOddKernel (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (N * N') → oddE0 D cc δ t0 N N' e0 → admG1 D → IntertwinerUnitary D → GaussSumTripleConstant D →
    odd3 D → odd4 D → oddKer D cc δ t0 N N' e0

def StatementOddIntegrality (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (N * N') → oddKer D cc δ t0 N N' e0 →
    GL3Theta.transl D → GL3Theta.atTwo D → GL3Theta.jetsPh D → GL3Theta.PhUnitary D → oddInt D cc δ N N' e0
def StatementOddMoments (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (N * N') → oddE0 D cc δ t0 N N' e0 → oddKer D cc δ t0 N N' e0 →
    GL3Theta.transl D → GL3Theta.atTwo D → GL3Theta.splitZero D → oddMom D cc δ N N' e0
def StatementOddRepresentation (D : D7) : Prop := oddRep D

def StatementOddExactness (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (N * N') → oddE0 D cc δ t0 N N' e0 → admissible_poisson D → admG1 D → IntertwinerUnitary D → GaussSumTripleConstant D → LemmaCGaussConstant D → odd3 D →
    odd4 D → oddEq D cc δ N N' e0

def GaloisThetaProperties (D : D7) : Prop :=
  galCurve D ∧ galStar D ∧ galSg D ∧ transInv D ∧ gal1 D ∧ galPh1 D ∧ galB D ∧ gal D ∧ galEx D ∧ t0Ex D ∧ use1 D ∧ useAlg D ∧
    useConj D ∧ useNorm D ∧ useXi D ∧ usePsi ∧ useLine D ∧ useBar D

def OddThetaProperties (D : D7) : Prop := odd1 D ∧ odd3 D ∧ odd4 D ∧ oddRep D ∧ odd D

def aux₃ (D : D7) : Prop := GaloisThetaProperties D ∧ OddThetaProperties D

def AdmDext (D : D7) : Prop :=
  WeilPairingGaloisAlt D ∧ admG1 D ∧ EmbeddingPermutesTypes D ∧ IntertwinerUnitary D ∧ GaussSumTripleConstant D ∧ LemmaCGaussConstant D ∧ admissible_poisson D

def ThetaInputsCDE (D : D7) : Prop :=
  GL3Theta.transl D ∧ GL3Theta.atTwo D ∧ GL3Theta.jetsPh D ∧ GL3Theta.PhUnitary D ∧ GL3Theta.splitZero D

def AdmD (D : D7) : Prop := AdmDext D ∧ ThetaInputsCDE D

def Stmt (D : D7) : Prop := AdmD D → aux₃ D

def natTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ N N' L L', admitted D N N' L L' →
    ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' (e N N' L L')

theorem admissible_self_dual_even {D : D7} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h : admitted D N N' L L') :
    SD D L ∧ SD D L' ∧ Even (N * N') := by
  obtain ⟨hN, hN', hL, hL'⟩ := h
  exact ⟨hL, hL', hN.mul_right _⟩

theorem normConj_indep (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (hc : Crv D cc δ)
    (h0 : t0Ex D) (hn : useNorm D) (ht : natTie D cc δ e) :
    ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D (tor0 D cc δ) M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L₁ L₁')
            (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L₂ L₂')
            (fnConj D M ρ (e N N' L₂ L₂')) := by
  intro N N' L₁ L₁' L₂ L₂' h1 h2 M _ hM hc1 hc2 ρ
  obtain ⟨hL₁, hL₁', hE⟩ := admissible_self_dual_even h1
  obtain ⟨hL₂, hL₂', -⟩ := admissible_self_dual_even h2
  obtain ⟨⟨t0, ht0⟩, hconj⟩ := h0 cc δ hc
  obtain ⟨t0', ht0'⟩ := hconj M ρ hM.2.1 hM.2.2
  rw [(hn cc δ hc t0 ht0 N N' L₁ L₁' hL₁ hL₁' hE _ (ht t0 ht0 N N' L₁ L₁' h1) M ρ hM hc1 t0' ht0').1,
    (hn cc δ hc t0 ht0 N N' L₂ L₂' hL₂ hL₂' hE _ (ht t0 ht0 N N' L₂ L₂' h2) M ρ hM hc2 t0' ht0').1]

theorem nat_alg (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (hc : Crv D cc δ)
    (h0 : t0Ex D) (ha : useAlg D) (ht : natTie D cc δ e) :
    ∀ N N' L L', admitted D N N' L L' → CoefIn D (e N N' L L') Qbar := by
  intro N N' L L' hA
  obtain ⟨hL, hL', hE⟩ := admissible_self_dual_even hA
  obtain ⟨⟨t0, ht0⟩, -⟩ := h0 cc δ hc
  exact (ha cc δ hc t0 ht0 N N' L L' hL hL' hE _ (ht t0 ht0 N N' L L' hA)).1

def kRat (D : D7) : Prop := ∀ u, ∀ i < D.R.m, (D.fm u).KRat i

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam AdmD Fm
def AdmExtF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam AdmDext Fm
def GaloisThetaPropertiesOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam GaloisThetaProperties Fm
def OddThetaPropertiesOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam OddThetaProperties Fm
def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam aux₃ Fm
def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → ConclusionOnFamily Fm
def kRatF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam kRat Fm

end Formalism.MainNotions.StandardLatticesGL3
