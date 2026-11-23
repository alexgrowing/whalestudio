import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.MatrixExponentialEntries
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal

def ForDS (Q : ∀ (m : ℕ) (_ : Fin m → Bool) (_ : Fin m → ℝ) (_ : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    (Mat m → (H →L[ℂ] H)) → Prop) : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (B : ℝ), 3 ≤ m → IsHCParam lam → GapAtLeast ε lam (1000 * (m : ℝ) ^ 3) →
    (∀ a, |lam a| ≤ B) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Mat m → (H →L[ℂ] H)), IsDS ε lam π →
      Q m ε lam B H π

def EmbLaws : Prop := ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), Signs e ε ε' →
  (∀ h ∈ UJset ε', embH e h ∈ UJset ε) ∧ (∀ h h', embH e (h * h') = embH e h * embH e h') ∧ Continuous (embH e) ∧
  (∀ h ∈ UJset ε', (embH e h)⁻¹ = embH e h⁻¹) ∧ (∀ g h, colLen e (g * embH e h) = colLen e g) ∧
  (∀ g ∈ UJset ε, (∀ a, g a (e none) = if a = e none then 1 else 0) → ∃ h ∈ UJset ε', g = embH e h) ∧
  (∀ X ∈ lieOf (Jm ε'), embL e X ∈ lieOf (Jm ε)) ∧ (∀ (t : ℝ) X, NormedSpace.exp (t • embL e X) = embH e (NormedSpace.exp (t • X))) ∧
  (∀ h, hsn (embH e h) ^ 2 = hsn h ^ 2 + 1) ∧ (∀ X, hsn (embL e X) = hsn X) ∧ (∀ g, colLen e g ≤ hsn g) ∧
  (∀ g ∈ UJset ε, 1 ≤ colLen e g ∧ hsn g⁻¹ = hsn g) ∧ ∀ g g' : Mat (n + 1), hsn (g * g') ≤ hsn g * hsn g'

def Boost : Prop := ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), Signs e ε ε' →
  ∀ g ∈ UJset ε, ∃ h ∈ UJset ε', ∃ b ∈ UJset ε, g = embH e h * b ∧ hsn b ^ 2 ≤ (n : ℝ) + 1 + 2 * colLen e g⁻¹ ^ 2

def VolBall : Prop := ∀ (m : ℕ) (ε : Fin m → Bool) (δ R : ℝ), 0 < δ → 0 < R →
  0 < muG ε (nbh ε δ) ∧ muG ε (nbh ε δ) < ⊤ ∧
    muG ε {g | hsn (umat g) ≤ R} ≤ ENNReal.ofReal ((1 + 2 * R ^ 2 / δ) ^ (2 * m ^ 2)) * muG ε (nbh ε δ)

def PowInt : Prop := ∀ (m : ℕ) (ε : Fin m → Bool) (A : ℝ), 1 ≤ m → 4 * (m : ℝ) ^ 2 + 1 ≤ A →
  Integrable (fun g : UJ ε => hsn (umat g) ^ (-A)) (muG ε) ∧
    ∫ g, hsn (umat g) ^ (-A) ∂muG ε ≤ Real.exp (10 * (m : ℝ) ^ 2) * (muG ε (nbh ε (1 / 4))).toReal

def Fold : Prop := ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), Signs e ε ε' →
  ∀ (F : Mat (n + 1) → ℝ), ContinuousOn F (UJset ε) → ∀ (R : ℝ) (Ω : Set (UJ ε)), MeasurableSet Ω →
    (∀ g ∈ Ω, ∃ h ∈ UJset ε', ∃ b ∈ UJset ε, umat g = embH e h * b ∧ hsn b ≤ R) →
    muG ε' (nbh ε' (1 / 4)) * ∫⁻ g in Ω, ENNReal.ofReal (F (umat g)) ∂muG ε ≤
      ∫⁻ g in {g | hsn (umat g) ≤ 2 * R}, ∫⁻ h, ENNReal.ofReal (F (embH e (umat h) * umat g)) ∂muG ε' ∂muG ε

def LogNear : Prop := ∀ (m : ℕ) (ε : Fin m → Bool) (δ : ℝ), δ ≤ 1 / 4 → ∀ g ∈ UJset ε, hsn (g - 1) ≤ δ →
  ∃ X ∈ lieOf (Jm ε), hsn X ≤ 2 * δ ∧ NormedSpace.exp X = g

def DecPow : Prop := ForDS fun m ε lam _ _ _ _ π => ∀ v₀, IsLowUnit ε lam π v₀ → ∀ g ∈ UJset ε,
  ‖⟪v₀, π g v₀⟫_ℂ‖ ≤ Real.exp (100 * (m : ℝ) ^ 3) * hsn g ^ (-(40 * (m : ℝ) ^ 2))

def LieBound : Prop := ForDS fun m ε lam B _ _ _ π => ∀ v₀, IsLowUnit ε lam π v₀ → SmV (lieOf (Jm ε)) π v₀ ∧
  ∀ l : List (Mat m), (∀ X ∈ l, X ∈ lieOf (Jm ε)) → l.length ≤ m + 2 →
    ‖l.foldr (dR π) v₀‖ ≤ (l.map fun X => (8 * (m : ℝ) * B) ^ 2 * hsn X).prod

def DegUpper : Prop := ForDS fun m ε _ B _ _ _ π => ∀ d, IsFdeg (muG ε) π d →
  (muG ε (nbh ε (1 / (4 * (8 * (m : ℝ) * B) ^ 2)))).toReal ≤ 4 / d

def DegRatio : Prop := ForPair fun n _ ε lam ε' _ _ _ _ _ _ _ _ π σ => (∃ d', IsFdeg (muG ε') σ d') ∧ ∃ d, IsFdeg (muG ε) π d ∧
  ∀ (s : Fin (n + 1)) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : Mat (n + 1) → (K →L[ℂ] K)),
    IsDS ε (lam - Pi.single s 1) ρ → ∃ ds, IsFdeg (muG ε) ρ ds ∧ d ≤ 2 ^ n * ds

def CoefProj : Prop := ∀ (n : ℕ) (ε' : Fin n → Bool) (H' K : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (σ : Mat n → (H' →L[ℂ] H')) (ρ : Mat n → (K →L[ℂ] K)) (d : ℝ) (w : H'),
  IsURepOn (UJset ε') σ → IsIrredOn (UJset ε') σ → IsFdeg (muG ε') σ d → IsURepOn (UJset ε') ρ → ‖w‖ = 1 →
  Integrable (fun h => ⟪w, σ (umat h) w⟫_ℂ) (muG ε') →
  ∃ Q : K →L[ℂ] K, (∀ x y, ⟪y, Q x⟫_ℂ = (d : ℂ) * ∫ h, star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) x⟫_ℂ ∂muG ε') ∧
    (∀ j : H' →L[ℂ] K, (∀ h ∈ UJset ε', ∀ a, j (σ h a) = ρ h (j a)) → Q (j w) = j w) ∧
    ∀ x, ∃ j : H' →L[ℂ] K, (∀ h ∈ UJset ε', ∀ a, j (σ h a) = ρ h (j a)) ∧ j w = Q x

def RankOne : Prop := ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), Signs e ε ε' →
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H')) (d : ℝ) (w : H') (j : H' →L[ℂ] H) (P : H →L[ℂ] H'),
    IsURepOn (UJset ε) π → IsURepOn (UJset ε') σ → IsIrredOn (UJset ε') σ → IsFdeg (muG ε') σ d → ‖w‖ = 1 →
    Integrable (fun h => ⟪w, σ (umat h) w⟫_ℂ) (muG ε') → IsProj e ε' π σ j P →
    (∀ x y, (d : ℂ) * ∫ h, star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, π (embH e (umat h)) x⟫_ℂ ∂muG ε' = ⟪y, j w⟫_ℂ * ⟪j w, x⟫_ℂ) ∧
    ∀ v, Integrable (fun h => ⟪v, π (embH e (umat h)) v⟫_ℂ) (muG ε') → ∀ a b,
      ∫ h, star ⟪v, π (embH e (umat h)) v⟫_ℂ * ⟪b, σ (umat h) a⟫_ℂ ∂muG ε' = ⟪P v, a⟫_ℂ * ⟪b, P v⟫_ℂ / (d : ℂ)

def ProjSmooth : Prop := ForPair fun _ e ε _ ε' _ _ _ _ _ _ _ _ π σ => ∀ j P, IsProj e ε' π σ j P →
  (∀ h ∈ UJset ε', ∀ v, P (π (embH e h) v) = σ h (P v)) ∧ ∀ v, SmV (lieOf (Jm ε)) π v → SmV (lieOf (Jm ε')) σ (P v) ∧
    ∀ X ∈ lieOf (Jm ε'), P (dR π (embL e X) v) = dR σ X (P v)

structure TensDat (m : ℕ) (H : Type) where

  K : Fin m → Type
  [nK : ∀ s, NormedAddCommGroup (K s)]
  [iK : ∀ s, InnerProductSpace ℂ (K s)]

  ρ : ∀ s, Mat m → (K s →L[ℂ] K s)

  ep : Fin m → ℝ

  io : ∀ s, K s → Fin m → H

  pr : ∀ s, (Fin m → H) → K s

attribute [instance] TensDat.nK TensDat.iK

structure TensDat.Is {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : TensDat m H) (ε : Fin m → Bool)
    (lam : Fin m → ℝ) (π : Mat m → (H →L[ℂ] H)) : Prop where

  ds : ∀ s, IsDS ε (lam - Pi.single s 1) (T.ρ s)

  ep : ∀ s, T.ep s = 1 ∨ T.ep s = -1

  io_sm : ∀ s y, SmV (lieOf (Jm ε)) (T.ρ s) y → ∀ c, SmV (lieOf (Jm ε)) π (T.io s y c)

  pr_sm : ∀ s x, (∀ c, SmV (lieOf (Jm ε)) π (x c)) → SmV (lieOf (Jm ε)) (T.ρ s) (T.pr s x)

  io_lin : ∀ s (a : ℂ) y y', SmV (lieOf (Jm ε)) (T.ρ s) y → SmV (lieOf (Jm ε)) (T.ρ s) y' → T.io s (a • y + y') = a • T.io s y + T.io s y'

  pr_lin : ∀ s (a : ℂ) x x', (∀ c, SmV (lieOf (Jm ε)) π (x c)) → (∀ c, SmV (lieOf (Jm ε)) π (x' c)) →
    T.pr s (a • x + x') = a • T.pr s x + T.pr s x'

  io_eq : ∀ s, ∀ g ∈ UJset ε, ∀ y, SmV (lieOf (Jm ε)) (T.ρ s) y → ∀ c, T.io s (T.ρ s g y) c = ∑ d, g⁻¹ d c • π g (T.io s y d)

  pr_eq : ∀ s, ∀ g ∈ UJset ε, ∀ x, (∀ c, SmV (lieOf (Jm ε)) π (x c)) → T.pr s (fun c => ∑ d, g⁻¹ d c • π g (x d)) = T.ρ s g (T.pr s x)

  io_der : ∀ s, ∀ X ∈ lieOf (Jm ε), ∀ y, SmV (lieOf (Jm ε)) (T.ρ s) y → ∀ c,
    T.io s (dR (T.ρ s) X y) c = dR π X (T.io s y c) - ∑ d, X d c • T.io s y d

  sum : ∀ x, (∀ c, SmV (lieOf (Jm ε)) π (x c)) → ∑ s, T.io s (T.pr s x) = x

  adj : ∀ s y x, SmV (lieOf (Jm ε)) (T.ρ s) y → (∀ c, SmV (lieOf (Jm ε)) π (x c)) →
    ∑ c, (if ε c then 1 else -1) * ⟪x c, T.io s y c⟫_ℂ = (T.ep s : ℂ) * ⟪T.pr s x, y⟫_ℂ

def TensEx : Prop := ForPair fun n _ ε lam _ _ _ H _ _ _ _ _ π _ => ∃ T : TensDat (n + 1) H, T.Is ε lam π

def TensId : Prop := ForPair fun n e ε lam ε' _ _ H _ _ _ _ _ π _ => ∀ T : TensDat (n + 1) H, T.Is ε lam π →
  (∀ v v', SmV (lieOf (Jm ε)) π v → SmV (lieOf (Jm ε)) π v' → ∀ c, ∀ g ∈ UJset ε, g⁻¹ c (e none) * ⟪v, π g v'⟫_ℂ =
    ∑ s, (T.ep s : ℂ) * ⟪T.pr s (Pi.single (e none) v), T.ρ s g (T.pr s (Pi.single c v'))⟫_ℂ) ∧
  ∀ s v v', SmV (lieOf (Jm ε)) π v → SmV (lieOf (Jm ε)) π v' → ∀ h ∈ UJset ε',
    (T.ep s : ℂ) * ⟪T.pr s (Pi.single (e none) v'), T.ρ s (embH e h) (T.pr s (Pi.single (e none) v))⟫_ℂ =
      ⟪v', π (embH e h) (T.io s (T.pr s (Pi.single (e none) v)) (e none))⟫_ℂ

def TensNorm : Prop := ForPair fun n _ ε lam _ _ B H _ _ _ _ _ π _ => ∀ T : TensDat (n + 1) H, T.Is ε lam π →
  ∀ v₀, IsLowUnit ε lam π v₀ → ∀ s c, ‖T.pr s (Pi.single c v₀)‖ ^ 2 ≤ (8 * ((n : ℝ) + 1) * B) ^ (4 * (n + 1))

def TensCap : Prop := ForPair fun n e ε lam ε' _ B H _ _ _ _ _ π σ => ∀ T : TensDat (n + 1) H, T.Is ε lam π →
  ∀ j P, IsProj e ε' π σ j P → ∀ s, ∃ γ : ℂ, ‖γ‖ ≤ (2 * B + 1) ^ n ∧ ∀ v, SmV (lieOf (Jm ε)) π v →
    P (T.io s (T.pr s (Pi.single (e none) v)) (e none)) = γ • P v

def Expand : Prop := ForPair fun n e ε lam ε' mu B H H' _ _ _ _ π σ => ∀ T : TensDat (n + 1) H, T.Is ε lam π →
  ∀ j P, IsProj e ε' π σ j P → ∀ w₀, IsLowUnit ε' mu σ w₀ → ∃ (a : Fin (n + 1) → ℂ) (u : ∀ s, T.K s),
    (∀ s, ‖a s‖ ^ 2 ≤ (2 * B + 1) ^ n ∧ ‖u s‖ = 1) ∧ ∀ v', SmV (lieOf (Jm ε)) π v' → ∀ c, ∀ g ∈ UJset ε,
      g⁻¹ c (e none) * ⟪j w₀, π g v'⟫_ℂ = ∑ s, a s * ⟪u s, T.ρ s g (T.pr s (Pi.single c v'))⟫_ℂ

def IntBounds : Prop := ∀ C₀ : ℝ, 0 < C₀ → ∃ C : ℝ, 0 < C ∧ ForPair fun n e ε lam ε' _ B _ _ _ _ _ _ π _ => ∀ v₀, IsLowUnit ε lam π v₀ →
  ∀ g₀ ∈ UJset ε, hsn g₀ ≤ (8 * ((n : ℝ) + 1) * B) ^ (C₀ * ((n : ℝ) + 1)) →
    (∀ g ∈ UJset ε, Integrable (fun h => ⟪π g₀ v₀, π (g * embH e (umat h)) (π g₀ v₀)⟫_ℂ) (muG ε') ∧
      ∫ h, ‖⟪π g₀ v₀, π (g * embH e (umat h)) (π g₀ v₀)⟫_ℂ‖ ∂muG ε' ≤
        (muG ε' (nbh ε' (1 / 4))).toReal * big C n B * colLen e g ^ (-(2 * (n : ℝ) + 7))) ∧
    ∃ A : ℝ, ∀ g ∈ UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A * hsn g ^ (-(20 * ((n : ℝ) + 1) ^ 2))

def DerBounds : Prop := ∀ C₀ : ℝ, 0 < C₀ → ∃ C : ℝ, 0 < C ∧ ForPair fun n e ε lam ε' _ B _ _ _ _ _ _ π _ => ∀ v₀, IsLowUnit ε lam π v₀ →
  ∀ g₀ ∈ UJset ε, hsn g₀ ≤ (8 * ((n : ℝ) + 1) * B) ^ (C₀ * ((n : ℝ) + 1)) → ∀ X ∈ lieOf (Jm ε'), hsn X ≤ 1 →
    Integrable (fun h => ⟪dR π (embL e X) (π g₀ v₀), π (embH e (umat h)) (π g₀ v₀)⟫_ℂ) (muG ε') ∧
      ∫ h, ‖⟪dR π (embL e X) (π g₀ v₀), π (embH e (umat h)) (π g₀ v₀)⟫_ℂ‖ ∂muG ε' ≤ (muG ε' (nbh ε' (1 / 4))).toReal * big C n B

theorem one_mem_nbh {m : ℕ} (ε : Fin m → Bool) {δ : ℝ} (h : 0 ≤ δ) : (1 : UJ ε) ∈ nbh ε δ := by
  simpa [nbh, hsn, umat] using h

section RankOne

open scoped ContDiff
open GlobalTheory.Survey.MatrixExponentialEntries (chi)

theorem exp_entry (X : Mat 1) : (NormedSpace.exp X) 0 0 = Complex.exp (X 0 0) := by
  have : X = Matrix.diagonal (fun _ => X 0 0) := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [this, Matrix.exp_diagonal]
  simp [Pi.exp_def, Complex.exp_eq_exp_ℂ]

theorem prod_entry (l : List (Mat 1)) : l.prod 0 0 = (l.map fun X => X 0 0).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Matrix.mul_apply, ih]

theorem smV_chi (L : Set (Mat 1)) (m : ℤ) (w : ℂ) : SmV L (chi m) w := by
  intro k Xs _
  have : (fun t : Fin k → ℝ => chi m ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w) =
      fun t => Complex.exp (m * ∑ i, (t i : ℂ) * Xs i 0 0) * w := by
    funext t
    simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, prod_entry, List.map_ofFn,
      List.prod_ofFn, Function.comp, exp_entry, Complex.exp_int_mul, Complex.exp_sum]
    simp
  rw [this]
  refine ContDiff.mul (ContDiff.cexp (ContDiff.mul contDiff_const (ContDiff.sum fun i _ => ContDiff.mul ?_ contDiff_const))) contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)

theorem dR_chi (m : ℤ) (X : Mat 1) (w : ℂ) : dR (chi m) X w = m * X 0 0 * w := by
  have : (fun t : ℝ => chi m (NormedSpace.exp (t • X)) w) = fun t : ℝ => Complex.exp ((t : ℂ) * (m * X 0 0)) * w := by
    funext t
    simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, exp_entry, ← Complex.exp_int_mul]
    congr 2
    simp; ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (m * X 0 0)) * w)
      ((Complex.exp (((0 : ℝ) : ℂ) * (m * X 0 0)) * (1 * (m * X 0 0))) * w) 0 :=
    ((((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const _).cexp).comp_ofReal).mul_const _
  unfold dR
  rw [this, hd.deriv]; simp

def tensOne (ε : Fin 1 → Bool) (m : ℤ) : TensDat 1 ℂ where
  K := fun _ => ℂ
  ρ := fun _ => chi (m - 1)
  ep := fun _ => if ε 0 then 1 else -1
  io := fun _ y _ => y
  pr := fun _ x => x 0

theorem tensOne_is (ε : Fin 1 → Bool) (m : ℤ) : (tensOne ε m).Is ε (fun _ => (m : ℝ)) (chi m) := by
  have hne : ∀ g ∈ UJset ε, g 0 0 ≠ 0 := fun g hg h0 => by
    have := GlobalTheory.Survey.MatrixExponentialEntries.norm_entry (ε := ε) hg
    simp [h0] at this
  have hinv : ∀ g : Mat 1, g⁻¹ 0 0 = (g 0 0)⁻¹ := fun g => by
    simp [Matrix.inv_def, Matrix.det_unique, Matrix.adjugate_fin_one]
  refine ⟨fun s => ?_, fun s => ?_, fun _ _ _ _ => smV_chi _ _ _, fun _ _ _ => smV_chi _ _ _, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, fun s g hg y _ c => ?_, fun s g hg x _ => ?_, fun s X _ y _ c => ?_, fun x _ => ?_, fun s y x _ _ => ?_⟩
  · have : ((fun _ => (m : ℝ)) - Pi.single s 1 : Fin 1 → ℝ) = fun _ => (((m - 1 : ℤ)) : ℝ) := by
      funext a; obtain rfl : a = s := Subsingleton.elim _ _; simp
    rw [this]
    exact GlobalTheory.Survey.MatrixExponentialEntries.isDS_chi ε (m - 1)
  · simp only [tensOne]; split_ifs <;> simp
  · obtain rfl : c = 0 := Subsingleton.elim _ _
    show (g 0 0) ^ (m - 1) * (show ℂ from y) = ∑ d, g⁻¹ d 0 • chi m g (show ℂ from y)
    generalize (show ℂ from y) = z
    simp [tensOne, chi, hinv, zpow_sub₀ (hne g hg)]
    ring
  · show _ = (g 0 0) ^ (m - 1) * x 0
    simp [tensOne, chi, hinv, zpow_sub₀ (hne g hg)]
    ring
  · obtain rfl : c = 0 := Subsingleton.elim _ _
    show dR (chi (m - 1)) X (show ℂ from y) = dR (chi m) X (show ℂ from y) - ∑ d, X d 0 • (show ℂ from y)
    generalize (show ℂ from y) = z
    simp [dR_chi]; ring
  · funext a; obtain rfl : a = 0 := Subsingleton.elim _ _; simp [tensOne]
  · show ∑ c : Fin 1, (if ε c then 1 else -1 : ℂ) * ⟪x c, (y : ℂ)⟫_ℂ = (((if ε 0 then 1 else -1 : ℝ)) : ℂ) * ⟪x 0, (y : ℂ)⟫_ℂ
    by_cases h : ε 0 <;> simp [h]

end RankOne

end GlobalTheory.SepReal

end
