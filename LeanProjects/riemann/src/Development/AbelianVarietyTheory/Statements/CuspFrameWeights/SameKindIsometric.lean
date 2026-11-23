import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def ResidueBound : Prop :=
  ∀ (k : Type) [Field k] [NumberField k], 2 ≤ Module.finrank ℚ k →
    dedekindZeta_residue k ≤ (Real.exp 1 * Real.log |(discr k : ℝ)| /
      (2 * ((Module.finrank ℚ k : ℝ) - 1))) ^ (Module.finrank ℚ k - 1)

def SameKindIsometric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), Jᴴ = J → J'ᴴ = J' → J.det ≠ 0 → J'.det ≠ 0 →
    (∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
    (∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
    (∀ φ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (J.map φ) p q ∧ Formalism.UG.HasSignature (J'.map φ) p q) →
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * (γ : Matrix (Fin n) (Fin n) E) = J'

def GenLinVolume : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j →
    glVol E j = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j ^ 2) *
      ∏ l ∈ Finset.Icc 2 j, zetaE E l)

def VolumeStep : Prop :=
  ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E),
      (∀ y, e (star y) = star (e y)) ∧ I'.n + 1 = I.n ∧
      star x ⬝ᵥ (I.J *ᵥ x) = (if s then 1 else -1) ∧ star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = I'.J.map e ∧
      HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) ∧
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I' c' →
        gaugeVol I c μf / ENNReal.ofReal (volU I.n ^ I.f) =
          gaugeVol I' c' μf' / ENNReal.ofReal (volU I'.n ^ I.f) *
            ENNReal.ofReal (Formalism.HermitianLatticesTheory.massRatioRightSide I.E I.n)

def VolumeInvariant : Prop :=
  ∀ (I I' : AutInst) (p q : ℕ), SameField I I' → HasSig I p q → HasSig I' p q →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
      IsGaugeAll I c → IsGaugeAll I' c' → gaugeVol I c μf = gaugeVol I' c' μf'

def VolumeRatio : Prop :=
  ∀ (I : AutInst) (p q p₀ q₀ : ℕ), HasSig I p q → p₀ ≤ p → q₀ ≤ q → 2 ≤ p₀ + q₀ →
    (∃ I₀ : AutInst, SameField I I₀ ∧ HasSig I₀ p₀ q₀) ∧
    ∀ I₀ : AutInst, SameField I I₀ → HasSig I₀ p₀ q₀ →
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c₀ : InfinitePlace I₀.F → ℝ) (μ₀ : Measure I₀.Gf) [SigmaFinite μ₀] [μ₀.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I₀ c₀ →
        gaugeVol I c μf = gaugeVol I₀ c₀ μ₀ * ENNReal.ofReal (∏ M ∈ Finset.Ioc (p₀ + q₀) (p + q), rankFac I.E M)

def IwasawaFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p →
    (univ.filter fun a => ε a = false).card = q →
    ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    ∀ (c : ℝ) (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGauge ε c → IsGaugeSub (flagN ε W) (dimN n j) μN →
      IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM →
      μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) →
      ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ →
        ENNReal.ofReal c * ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) =
          ENNReal.ofReal (cIw p q j) * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
            ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN

def RadicalCovolume : Prop :=
  ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) →
    ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S →
    ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (ν v)],
      (∀ v, IsGaugeSub (flagN (I.ε v) (flagAt I S v)) (dimN I.n j) (ν v)) →
      covol {g : I.Ginf | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset ∧
          ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)} (Measure.pi ν)
          {g : I.Ginf | ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)} ≤
        ENNReal.ofReal ((2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2) *
          layerProd I.n I.f j
            (fun i => Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc)) id)

def UnfoldBound : Prop :=
  ∀ (I I₀ : AutInst) (p q : ℕ) (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∑ i, j i ≤ p →
    SameField I I₀ → HasSig I p q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c₀ : InfinitePlace I₀.F → ℝ) (μ₀ : Measure I₀.Gf) [SigmaFinite μ₀] [μ₀.IsHaarMeasure],
      IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a →
      ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) (typeSet I j B) / μf I.Kset ≤
        ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) *
          (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * glVol I.E (j i)) * gaugeVol I₀ c₀ μ₀ *
          ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ)

def FlagMeasureBound : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → ∀ (p q : ℕ), HasSig I p q → 2 * q + 2 ≤ I.n →
    ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q →
    ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a →
      MeasurableSet (typeSet I j B) ∧ 0 < I.muA μf fund ∧ I.muA μf fund < ⊤ ∧
      I.muA μf (typeSet I j B ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (kapBd I.E p q j) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ)

def ConstantBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ (p q a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → 15 ≤ Real.log (p + q : ℕ) → q ^ 2 ≤ p + q →
      Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ Real.exp (p + q : ℕ) →
      Real.log (Formalism.HermitianLatticesTheory.fDeg E) ≤ Real.sqrt (p + q : ℕ) →
      kapBd E p q j ≤
        Real.exp (-(1 / 2 * (∑ i, j i : ℕ) * (p + q : ℕ) * Formalism.HermitianLatticesTheory.fDeg E * Real.log (p + q : ℕ)))

def NonzeroFlagBound : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → ∀ (p q : ℕ), HasSig I p q → 15 ≤ Real.log I.n → q ^ 2 ≤ I.n →
      Real.log I.rd ≤ Real.exp I.n → Real.log I.f ≤ Real.sqrt I.n →
      I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (Real.exp (-(1 / 3 * I.n * I.f * Real.log I.n)))

def RankTwoClasses : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ((defClassNum E 2 : ENat) : ENNReal) ≤ ENNReal.ofReal
      (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) *
        (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E))

def AbsoluteVolume : Prop :=
  ∀ (I : AutInst) (p q : ℕ), HasSig I p q → q ^ 2 ≤ I.n → 8 ≤ I.n →
    ∀ X : ℝ, 2 ≤ X → I.rd ≤ X → 2 * I.f * I.rd ≤ X ^ 2 →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure],
      IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (X ^ (I.n ^ 2 * I.f))

end GlobalTheory.FlagMeas
