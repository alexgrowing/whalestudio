import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def v₀ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) := ⟨some p.1, p.2⟩

def v₁ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) :=
  if h : p.1 = k₀ then ⟨none, cast (congrArg ι h) p.2⟩ else ⟨some p.1, p.2⟩

theorem v₁_ne {k₀ : K} {p : Σ k, ι k} (h : p.1 ≠ k₀) : v₁ k₀ p = ⟨some p.1, p.2⟩ := dif_neg h

theorem v₁_self (k₀ : K) (m : ι k₀) : v₁ k₀ ⟨k₀, m⟩ = ⟨none, m⟩ := dif_pos rfl

def fstPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₀ k₀

def sndPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₁ k₀

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def normRhs (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : ℝ :=
  Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
        else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁))

def IsNormFn (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (f : RW.X → ℝ) : Prop :=
  ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F →
    M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ (fstPt k₀ (RW.lift x x)) →
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 →
    (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) →
    f x = normRhs M τ a F z₀ z₁ h t

def IsWChart (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e)
    (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsCompatChart RW.A ψ ∧ M.IsFrame F ∧ (∀ i, σ i ≠ i₀) ∧
    (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) ∧
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) ψ.target) ∧
    ∀ x' ∈ ψ.source, (∀ τ', IsBlockDiag j (H τ' (ψ x')) ∧ (H τ' (ψ x')).det ≠ 0) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x' x')))) ∧
      ∃ z₀ z₁ : (Σ k, ι k) → ℂ, SameOrbit z₀ (fstPt k₀ (RW.lift x' x')) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift x' x')) ∧
        ∀ τ' i, M.ExactAt F (τ', i) z₀ (H τ' (ψ x')) ∧
          M.ExactAt F (τ', i) z₁ (if τ' = τ then H τ (ψ x') * (1 + Matrix.single cb ca (ψ x' i₀)) else H τ' (ψ x'))

def IsWAtlas (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) : Prop :=
  HoloMap RW.A Rb.A pr ∧
    (∀ x, SameOrbit (Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) ∧
    ∀ x, ∃ ψ kb σ i₀ F H, x ∈ ψ.source ∧ IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H

def IsFibreChart {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) : Prop :=
  ∃ (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X),
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, M.ExactAt (BM.F l) (τ', i) z₀
        (if τ' = τ then H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)) else H τ' (Fin.tail z))) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem pullback_pullback {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (P : LocPot X)
    (f : Y → X) (g : Z → Y) (r : Z → X) (hf : Continuous f) (hg : Continuous g) (hr : Continuous r) (h : f ∘ g = r) :
    (P.pullback f hf).pullback g hg = P.pullback r hr := by
  subst h
  rfl

theorem orbit_symm {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem orbit_trans {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' z'' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.WSq
