import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Summand
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Abstract

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def Act (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (s : ℂ → V →L[ℂ] V) : Prop :=
  ∃ (u : ℝ →₀ (V →L[ℂ] V)) (κ : ℝ → V →L[ℂ] V), Ker κ ∧
    (∀ x, Y (J x) = J ((u.sum fun t c => c.compLpL 2 volume (sh V t x)) + conv κ x)) ∧
    ∀ z, s z = (u.sum fun t c => Complex.exp (z * t) • c) + symb κ z

def eigP {d : ℕ} (a : Eu d →L[ℂ] Eu d) (x : ℝ) : Eu d →L[ℂ] Eu d :=
  (Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ)).starProjection

end Abstract

def Family2 {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)}
    [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')
    (P : L2 μ →L[ℂ] L2 μ) (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (C : ℝ) : Prop :=
  Family μ A A' 0 P N C ∧ ∀ (Y : L2 μ →L[ℂ] L2 μ) s s', Act A.J Y s → Act A'.J Y s' → ∀ w, N (s' 0 w) = s 0 (N w)

section Fam

variable {E : Type} [Field E] [NumberField E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ}

structure Fam (𝔢 : Side θ 2) where
  τ₁ : Submodule ℂ (L2 (BW.mu1 E 2))
  τ₂ : Submodule ℂ (L2 (BW.mu1 E 2))
  pair : Pair (BW.mu1 E 2) τ₁ τ₂
  m₁ : (E →+* ℂ) → Multiset ℂ
  m₂ : (E →+* ℂ) → Multiset ℂ
  B₁ : Pl E → Multiset ℂ
  B₂ : Pl E → Multiset ℂ
  at₁ : At (BW.mu1 E 2) 𝔢.S τ₁ m₁ B₁
  at₂ : At (BW.mu1 E 2) 𝔢.S τ₂ m₂ B₂
  smo₁ : ∀ V, IsSummand (BW.mu1 E 2) V → At (BW.mu1 E 2) 𝔢.S V m₁ B₁ → V = τ₁
  smo₂ : ∀ V, IsSummand (BW.mu1 E 2) V → At (BW.mu1 E 2) 𝔢.S V m₂ B₂ → V = τ₂
  rigid : ∀ b : Datum E (2 + 2), b.Pt 𝔢.S (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w) →
    b.r = 2 ∧ (∀ i, b.d i = 2) ∧ ∃ i j, i ≠ j ∧ At (b.μ i) 𝔢.S (b.V i) m₁ B₁ ∧ At (b.μ j) 𝔢.S (b.V j) m₂ B₂
  D : TypeDat E (2 + 2)
  level : D.Level 𝔢.U
  d : ℕ
  d' : ℕ
  A : Line μ τ₁ τ₂ D d
  A' : Line μ τ₂ τ₁ D d'
  P : L2 μ →L[ℂ] L2 μ
  isP : IsOrthogonalProjectionTwoLines A.J A'.J P
  σ : E ≃+* E
  θ₂ : Twist (BW.mu1 E 2)
  gal : UpperTheory.ConvolutionTheory.K.IsGal σ θ
  gal₂ : UpperTheory.ConvolutionTheory.K.IsGal σ θ₂
  stable : Stable D θ
  swap₁ : τ₁.map (θ₂.U : L2 (BW.mu1 E 2) →ₗ[ℂ] L2 (BW.mu1 E 2)) = τ₂
  swap₂ : τ₂.map (θ₂.U : L2 (BW.mu1 E 2) →ₗ[ℂ] L2 (BW.mu1 E 2)) = τ₁
  s : Eu d ≃ₗᵢ[ℂ] Eu d'
  s_sec : ∀ v x, A'.sec (s v) x = A.sec v (θ.e.symm x)
  s_op : ∀ (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, v x = s (u x)) → θ.U (A.J u) = A'.J v
  a_hecke : D.Hecke 𝔢.a
  g_hecke : D.Hecke 𝔢.g
  βa : ℝ → Eu d' →L[ℂ] Eu d'
  βg : ℝ → Eu d' →L[ℂ] Eu d'
  a_acts : ActsBy μ A' 𝔢.a βa
  g_acts : ActsBy μ A' 𝔢.g βg
  u : ZMod 2 → ℂ → Eu d' →L[ℂ] Eu d'
  v : ZMod 2 → ℂ → Eu d →L[ℂ] Eu d
  u_act : ∀ i, Act A'.J (𝔢.Uq i) (u i)
  v_act : ∀ i, Act A.J (𝔢.Uq i) (v i)
  u_comm : 𝔢.Uq 0 ∘L P = P ∘L 𝔢.Uq 0

variable {𝔢 : Side θ 2} (𝔣 : Fam 𝔢)

def Fam.Λ (τ : E →+* ℂ) : Multiset ℂ := 𝔣.m₁ τ + 𝔣.m₂ τ

def Fam.t (w : Pl E) : Multiset ℂ := 𝔣.B₁ w + 𝔣.B₂ w

def Fam.a₀ : Eu 𝔣.d' →L[ℂ] Eu 𝔣.d' := symb 𝔣.βa 0

def Fam.tr (N : Eu 𝔣.d' ≃ₗᵢ[ℂ] Eu 𝔣.d) (x : ℝ) (j : ℕ) : ℂ :=
  LinearMap.trace ℂ (Eu 𝔣.d) ((N.toLinearEquiv : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d) ∘ₗ
    ((eigP 𝔣.a₀ x ∘L (𝔣.u 0 0 ^ j) ∘L symb 𝔣.βg 0 : Eu 𝔣.d' →L[ℂ] Eu 𝔣.d') : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d') ∘ₗ
    (𝔣.s.toLinearEquiv : Eu 𝔣.d →ₗ[ℂ] Eu 𝔣.d'))

structure Fam.IsEvz (ev : PR E (2 + 2) →+* (LL μ →L[ℂ] LL μ)) (evz : ℂ → PR E (2 + 2) →+* (Eu 𝔣.d' →L[ℂ] Eu 𝔣.d')) : Prop where
  act : ∀ R : PR E (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔢.S) → Act 𝔣.A'.J (ev R) fun z => evz z R
  comm : ∀ R : PR E (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔢.S) → ev R ∘L 𝔣.P = 𝔣.P ∘L ev R
  const : ∀ z (c : ℂ), evz z (C (C c)) = c • 1
  amp : ∀ z, evz z (C (X none)) = symb 𝔣.βa z
  zero : ∀ R : PR E (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔢.S) → ∀ x : ℝ, 0 < x →
    ∀ v ∈ Module.End.eigenspace (𝔣.a₀ : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d') (x : ℂ), evz 0 R v = val x 𝔣.Λ 𝔣.t R • v

end Fam

def SB {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : ℂ → V →L[ℂ] V) (K : ℝ) : Prop := ∀ z : ℂ, |z.re| ≤ 1 → ‖s z‖ ≤ K

def CIx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (μE : Measure (normOneGL E (2 + 2))) [μE.IsHaarMeasure] (μF : Measure (normOneGL F (2 + 2))) [μF.IsHaarMeasure] (θ : Twist μE)
    (𝔢 : Side θ 2) (𝔣 : Side (Twist.id μF) 2) (c : ℂ), GeoPair 𝔢 𝔣 c → ∀ 𝔵 : Fam 𝔢,
    (∀ (b : Datum F (2 + 2)) Λ' t', b.Pt 𝔣.S Λ' t' → ¬ (𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, 𝔵.t w = bcSat t' w)) →
    ∃ N : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d,
      (∀ (Y : L2 μE →L[ℂ] L2 μE) s s', Act 𝔵.A.J Y s → Act 𝔵.A'.J Y s' → ∀ w, N (s' 0 w) = s 0 (N w)) ∧
      ∀ x : ℝ, 0 < x → ∀ᶠ j : ℕ in atTop,
        𝔢.tr (fun V => At μE 𝔢.S V 𝔵.Λ 𝔵.t) x j + (1 / 2 : ℂ) * 𝔵.tr N x j =
          c * 𝔣.tr (fun V => ∃ Λ' t', At μF 𝔣.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, 𝔵.t w = bcSat t' w) x j

def KillExempt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (μ : Measure (normOneGL E (2 + 2))) [μ.IsHaarMeasure] (θ : Twist μ)
    (𝔢 : Side θ 2) (𝔵 : Fam 𝔢) (η : ℝ), 0 < η →
    ∃ (B : Type) (_ : Fintype B) (b : B → Datum E (2 + 2)), (∀ i, ∃ Λ t, (b i).Pt 𝔢.S Λ t) ∧ (∀ i, ¬ (b i).Pt 𝔢.S 𝔵.Λ 𝔵.t) ∧
      ∀ ev, 𝔢.toAmp.IsEv ev → (∀ R : PR E (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔢.S) → ev R ∘L 𝔵.P = 𝔵.P ∘L ev R) →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x ≤ η / 2, χ x = 0) → (∀ x, |χ x| ≤ 1) →
      ∀ F G, admitted 𝔢.S F → (∀ i, Kills 𝔢.S F (b i)) → IsGen F G →
        ∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔢.toAmp.A ∘L (1 - Pc μ - 𝔵.P)‖ ≤ C ^ (d + 1) / d.factorial

def FamEx : Prop := ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → ∃ N C, Family2 μ A A' P N C

def KernX : Prop := ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' =>
  ∀ (θ : Twist μ) (a g : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → θ.U ∘L P = P ∘L θ.U →
    (∀ (T : ℝ) (Λ : L2 μ →L[ℂ] L2 μ), 0 ≤ T → IsTrunc A.J A'.J T Λ → θ.U ∘L Λ = Λ ∘L θ.U) →
    IsLeftSmooth a → D.Hecke a → IsLeftSmooth (CuspidalProjection.ccStar g) → D.Hecke g →
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ N' : ℕ, ∃ C T₁ : ℝ, ∀ (f : CC K (2 + 2)) (M Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), T₁ ≤ T → 0 ≤ T →
      M ∘L Pc μ = Pc μ ∘L M → M ∘L P = P ∘L M → Rop μ f = Rop μ a ∘L M ∘L Rop μ g → IsTrunc A.J A'.J T Λ →
      (∀ x : G1 K (2 + 2), Real.exp (c * T) < qht x → twK θ f x = 0) →
      IsTraceClass (Λ ∘L (Rop μ f ∘L θ.U) ∘L P ∘L Λ) ∧
      ‖twInt θ f - cuspTr μ θ f - trace (Λ ∘L (Rop μ f ∘L θ.U) ∘L P ∘L Λ)‖ ≤
        C * Real.exp (N * T) * ‖M ∘L (1 - Pc μ - P)‖ + C * Real.exp (-(N' * T)) * ‖M‖

def KillEx2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (n : ℕ) (SE : Set (Pl E)) (SF : Set (Pl F)), (∀ w : Pl E, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) →
    ∀ (B B' : Type) [Fintype B] [Fintype B'] (b : B → Datum E n) (b' : B' → Datum F n),
      (∀ i, ∃ Λ t, (b i).Pt SE Λ t) → (∀ i, ∃ Λ t, (b' i).Pt SF Λ t) →
    ∀ (L : Ix E n → ℂ) (t : Pl E → Multiset ℂ), (∀ w ∉ SE, (t w).card = n) → (∀ i, ¬ (b i).Pt SE (msOf L) t) →
    (∀ i Λ' t', (b' i).Pt SF Λ' t' → ¬ (msOf L = bcInf Λ' ∧ ∀ w ∉ SE, t w = bcSat t' w)) →
    ∃ Φ : KF (Ix E n) (Pl E × Fin n), admitted SE Φ ∧ evK L (hval t) Φ ≠ 0 ∧ (∀ i, Kills SE Φ (b i)) ∧
      ∀ i (L' : Ix F n → ℂ) t', (b' i).Pt SF (msOf L') t' →
        evK (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (hval (bcSat t')) Φ = 0

def OneSideX : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (normOneGL K (2 + 2))) [μ.IsHaarMeasure] (θ : Twist μ)
    (𝔰 : Side θ 2) (𝔵 : Fam 𝔰) (ev : PR K (2 + 2) →+* (LL μ →L[ℂ] LL μ)) (evz : ℂ → PR K (2 + 2) →+* (Eu 𝔵.d' →L[ℂ] Eu 𝔵.d'))
    (Nn : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d) (C₀ : ℝ), 𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → 𝔵.IsEvz ev evz →
    Family μ 𝔵.A 𝔵.A' 0 𝔵.P Nn C₀ → ∀ sp : Finset ℝ,
    (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥) →
    ∃ (c cU M₁ : ℝ) (N : ℕ), 0 < c ∧ 1 ≤ cU ∧ 4 ≤ M₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ p, p ∈ s ↔ η < p.1 ∧ IsSummand μ p.2 ∧ p.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = p.2 ∧ eigIn p.2 𝔰.toAmp.A p.1 ≠ ⊥) ∧
        (∀ p ∈ s, FiniteDimensional ℂ (eigIn p.2 𝔰.toAmp.A p.1)) ∧
        ∀ N' : ℕ, ∃ C₁ T₁ : ℝ, ∀ (Q : PR K (2 + 2)) (a : ℝ × Submodule ℂ (LL μ) → ℂ) (KQ : ℝ),
          (∀ y ∈ Q.vars, y.1 ∉ 𝔰.S) → SB (fun z => evz z Q) KQ →
          (∀ p ∈ s, ∀ v ∈ eigIn p.2 𝔰.toAmp.A p.1, ev Q v = a p • v) →
          ∀ (m j : ℕ) (T : ℝ) (f : TG K (2 + 2)), T₁ ≤ T → 𝔰.Rep (ev (chebP η m * Q)) j (Real.exp (c * T)) f →
            ‖twInt θ f - ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p *
                trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) -
              (1 / 2 : ℂ) * ∑ x ∈ sp, (cheb η m x : ℂ) * (x * val x 𝔵.Λ 𝔵.t Q * 𝔵.tr Nn x j)‖ ≤
              C₁ * cU ^ j * (Real.exp (N * T) * (‖ev Q‖ + (4 / η) ^ m * ‖ev Q ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ - 𝔵.P)‖) +
                (4 / η) ^ m * Real.exp (-(N' * T)) * ‖ev Q‖ + (M₁ / η) ^ m * KQ * Real.exp (-2 * T))

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
