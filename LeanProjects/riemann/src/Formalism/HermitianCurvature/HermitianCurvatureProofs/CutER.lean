import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

def capLw (k r : ℕ) (Y : ℂ) : List (ℂ × List (B.Mat k r)) :=
  Classical.choose (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)

def capTh (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s Y : ℂ) : B.DiffOp k r Wp Wq :=
  TLB.capOp k r Wp Wq s (capLw k r Y)

def CapAdj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F →
    ∀ g ∈ B.GV k r, B.opAdj (capTh k r Wp Wq s Y) F g = conj s • Q.CV k r (conj Y) F g

def CapThFacts : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s Y : ℂ)
    (ε : ℝ) (m : ℕ),
    B.opOrder (capTh k r Wp Wq s Y) = 2 * r + k + 1 ∧ B.SmoothCoef (B.GPos D) (capTh k r Wp Wq s Y) ∧
      B.Commutes D (B.GPos D) (capTh k r Wp Wq s Y) ∧ B.PolyCoef D ε 0 m (capTh k r Wp Wq s Y) ∧
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F →
        ∀ g ∈ B.GV k r, B.opApply (capTh k r Wp Wq s Y) F g = s • Q.CV k r Y F g

def CVSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) (s • Q.CV k r Y F)

def CVCC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ) (A : ℝ) (m : ℕ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F → B.InCC A (m + (2 * r + k + 1)) F →
    B.InCC A m (s • Q.CV k r Y F)

def CVSupp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ)
    (c : ℝ) (s Y : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F →
    (∀ g ∈ B.GV k r, F g ≠ 0 → c ≤ Gf k r z z' g) →
    ∀ g ∈ B.GV k r, (s • Q.CV k r Y F) g ≠ 0 → c ≤ Gf k r z z' g

def CVCongr : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ)
    (F F₁ : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F₁ →
    (∀ g ∈ B.GV k r, F g = F₁ g) → ∀ g ∈ B.GV k r, (s • Q.CV k r Y F) g = (s • Q.CV k r Y F₁) g

def CVComm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y Y' : ℂ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F →
    ∀ g ∈ B.GV k r, (s • Q.CV k r Y (s • Q.CV k r Y' F)) g = (s • Q.CV k r Y' (s • Q.CV k r Y F)) g

def BetaCongr : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F F₁ F' F₁' : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ g ∈ B.GV k r, F g = F₁ g) → (∀ g ∈ B.GV k r, F' g = F₁' g) →
    B.beta D F F' = B.beta D F₁ F₁'

section general

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem beta_conj (D : B.RealPlaceData k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.beta D F F' = conj (B.beta D F' F) := by
  unfold B.beta Formalism.QuantumDeterminants.betaBig
  rw [← integral_conj]
  congr 1
  funext p
  rw [map_mul, Complex.conj_ofReal, inner_conj_symm]

end general

section assembly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def opL (k r : ℕ) (s : ℂ) (x : Bool × ℝ) (H : B.Mat k r → (Wq →L[ℂ] Wp)) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  s • Q.CV k r (x.2 : ℂ) H

def Good (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (c : ℝ) (H : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  B.CkOn ⊤ (B.GV k r) H ∧ B.InCC A m H ∧ ∀ g ∈ B.GV k r, H g ≠ 0 → c ≤ Gf k r D.z D.z' g

def EqG (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop := ∀ g ∈ B.GV k r, H₁ g = H₂ g

theorem inCC_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m m' : ℕ} (hm : m' ≤ m)
    {F : B.Mat k r → E} (h : B.InCC A m F) : B.InCC A m' F := by
  obtain ⟨C, h1, h2⟩ := h
  exact ⟨C, Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast hm) h1,
    fun u v hu hv huv g hg => h2 u v hu hv (huv.trans hm) g hg⟩

theorem good_mono {D : B.RealPlaceData k r Wp Wq} {A : ℝ} {m m' : ℕ} {c : ℝ} (hm : m' ≤ m)
    {H : B.Mat k r → (Wq →L[ℂ] Wp)} (h : Good D A m c H) : Good D A m' c H :=
  ⟨h.1, inCC_mono hm h.2.1, h.2.2⟩

theorem op_good (hSm : CVSmooth) (hCC : CVCC) (hSu : CVSupp) {D : B.RealPlaceData k r Wp Wq} {A : ℝ} {m : ℕ}
    {c : ℝ} (s : ℂ) (x : Bool × ℝ) {H : B.Mat k r → (Wq →L[ℂ] Wp)} (h : Good D A (m + (2 * r + k + 1)) c H) :
    Good D A m c (opL k r s x H) :=
  ⟨hSm k r Wp Wq s _ H h.1, hCC k r Wp Wq s _ A m H h.1 h.2.1, hSu k r Wp Wq D.z D.z' c s _ H h.1 h.2.2⟩

theorem fold_good (hSm : CVSmooth) (hCC : CVCC) (hSu : CVSupp) {D : B.RealPlaceData k r Wp Wq} {A : ℝ} {c : ℝ}
    (s : ℂ) : ∀ (a : List (Bool × ℝ)) (m : ℕ) (H : B.Mat k r → (Wq →L[ℂ] Wp)),
      Good D A (m + a.length * (2 * r + k + 1)) c H → Good D A m c (a.foldr (opL k r s) H)
  | [], m, H, h => by simpa using h
  | x :: a, m, H, h => by
    rw [List.foldr_cons]
    refine op_good hSm hCC hSu s x (fold_good hSm hCC hSu s a (m + (2 * r + k + 1)) H ?_)
    have e : m + (2 * r + k + 1) + a.length * (2 * r + k + 1) = m + (x :: a).length * (2 * r + k + 1) := by
      rw [List.length_cons]; ring
    rw [e]; exact h

theorem fold_smooth (hSm : CVSmooth) (s : ℂ) : ∀ (a : List (Bool × ℝ)) (H : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.CkOn ⊤ (B.GV k r) H → B.CkOn ⊤ (B.GV k r) (a.foldr (opL k r s) H)
  | [], _, h => h
  | x :: a, H, h => hSm k r Wp Wq s _ _ (fold_smooth hSm s a H h)

theorem adj_step (hA : CapAdj) (hF : CapThFacts) (hB : BetaCongr) (D : B.RealPlaceData k r Wp Wq) {A : ℝ}
    (hAB : B.AB k r ≤ A) {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : conj s = s) (x : Bool × ℝ)
    {H H' : B.Mat k r → (Wq →L[ℂ] Wp)} (hH : Good D A (2 * r + k + 1 + 5) c H)
    (hH' : Good D A (2 * r + k + 1 + 5) c H') :
    B.beta D (opL k r s x H) H' = B.beta D H (opL k r s x H') := by
  set Θ := capTh k r Wp Wq s (x.2 : ℂ) with hΘ
  obtain ⟨hord, hSC, hCo, hPC, hApp⟩ := hF k r Wp Wq D s (x.2 : ℂ) c (B.opOrder Θ + 5)
  obtain ⟨_, _, _, _, _, _, hP⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D A hAB
  have hHc : B.InCC (A + 0) (B.opOrder Θ + 5) H := by rw [add_zero, hord]; exact hH.2.1
  have hH'c : B.InCC (A + 0) (B.opOrder Θ + 5) H' := by rw [add_zero, hord]; exact hH'.2.1
  have h1 := hP Θ c 0 hc le_rfl hSC hCo hPC H H' hHc hH'c hH.2.2 hH'.2.2
  have h0 : B.beta D (opL k r s x H) H' = B.beta D (B.opApply Θ H) H' :=
    hB k r Wp Wq D _ _ _ _ (fun g hg => (hApp H (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hH.1) g hg).symm)
      (fun _ _ => rfl)
  have h2 : B.beta D H (B.opAdj Θ H') = B.beta D H (opL k r s x H') :=
    hB k r Wp Wq D _ _ _ _ (fun _ _ => rfl) (fun g hg => by
      rw [hΘ, hA k r Wp Wq s (x.2 : ℂ) H' hH'.1 g hg, hs, Complex.conj_ofReal]; rfl)
  rw [h0, h1, h2]

theorem fold_adj (hA : CapAdj) (hF : CapThFacts) (hB : BetaCongr) (hSm : CVSmooth) (hCC : CVCC) (hSu : CVSupp)
    (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hAB : B.AB k r ≤ A) {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : conj s = s) :
    ∀ (a : List (Bool × ℝ)) (H H' : B.Mat k r → (Wq →L[ℂ] Wp)),
      Good D A (a.length * (2 * r + k + 1) + (2 * r + k + 1 + 5)) c H →
      Good D A (a.length * (2 * r + k + 1) + (2 * r + k + 1 + 5)) c H' →
      B.beta D (a.foldr (opL k r s) H) H' = B.beta D H (a.reverse.foldr (opL k r s) H')
  | [], _, _, _, _ => by simp
  | x :: a, H, H', hH, hH' => by
    have hZ : Good D A (2 * r + k + 1 + 5) c (a.foldr (opL k r s) H) := by
      refine fold_good hSm hCC hSu s a _ H (good_mono ?_ hH)
      rw [List.length_cons]; nlinarith
    have hx : Good D A (a.length * (2 * r + k + 1) + (2 * r + k + 1 + 5)) c (opL k r s x H') := by
      refine op_good hSm hCC hSu s x ?_
      have e : a.length * (2 * r + k + 1) + (2 * r + k + 1 + 5) + (2 * r + k + 1) =
          (x :: a).length * (2 * r + k + 1) + (2 * r + k + 1 + 5) := by rw [List.length_cons]; ring
      rw [e]; exact hH'
    have h1 := adj_step hA hF hB D hAB hc hs x hZ (good_mono (by omega) hH')
    have h2 := fold_adj hA hF hB hSm hCC hSu D hAB hc hs a H (opL k r s x H')
      (good_mono (by rw [List.length_cons]; nlinarith) hH) hx
    rw [List.foldr_cons, h1, h2, List.reverse_cons, List.foldr_append]
    rfl

theorem fold_push (hSm : CVSmooth) (hCg : CVCongr) (hCm : CVComm) (s : ℂ) (x : Bool × ℝ) :
    ∀ (a : List (Bool × ℝ)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) H →
      EqG (a.foldr (opL k r s) (opL k r s x H)) (opL k r s x (a.foldr (opL k r s) H))
  | [], _, _ => fun _ _ => rfl
  | y :: a, H, h => by
    intro g hg
    have ih := fold_push hSm hCg hCm s x a H h
    have h1 : EqG (opL k r s y (a.foldr (opL k r s) (opL k r s x H)))
        (opL k r s y (opL k r s x (a.foldr (opL k r s) H))) :=
      hCg k r Wp Wq s _ _ _ (fold_smooth hSm s a _ (hSm k r Wp Wq s _ H h))
        (hSm k r Wp Wq s _ _ (fold_smooth hSm s a H h)) ih
    rw [List.foldr_cons, List.foldr_cons, h1 g hg]
    exact hCm k r Wp Wq s _ _ (a.foldr (opL k r s) H) (fold_smooth hSm s a H h) g hg

theorem fold_rev (hSm : CVSmooth) (hCg : CVCongr) (hCm : CVComm) (s : ℂ) :
    ∀ (a : List (Bool × ℝ)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) H →
      EqG (a.reverse.foldr (opL k r s) H) (a.foldr (opL k r s) H)
  | [], _, _ => fun _ _ => rfl
  | x :: a, H, h => by
    intro g hg
    rw [List.reverse_cons, List.foldr_append]
    show (a.reverse.foldr (opL k r s) (opL k r s x H)) g = (opL k r s x (a.foldr (opL k r s) H)) g
    rw [fold_rev hSm hCg hCm s a (opL k r s x H) (hSm k r Wp Wq s _ H h) g hg]
    exact fold_push hSm hCg hCm s x a H h g hg

end assembly

theorem bound_aux (r k N Ntop : ℕ) (A₀ : ℝ) (hN : N ≤ Ntop)
    (hA0 : 100 * ((r : ℝ) + 1) ^ 4 * ((Ntop : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    B.AB k r + 2 * ((r : ℝ) + 1) * ((N * (2 * r + k + 1) + (2 * r + k + 1 + 5) : ℕ) : ℝ) ≤ A₀ := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hNN : (N : ℝ) ≤ Ntop := by exact_mod_cast hN
  have hT0 : (0 : ℝ) ≤ Ntop := Nat.cast_nonneg Ntop
  have hcast : ((N * (2 * r + k + 1) + (2 * r + k + 1 + 5) : ℕ) : ℝ) =
      (N : ℝ) * (2 * (r : ℝ) + k + 1) + (2 * (r : ℝ) + k + 1) + 5 := by push_cast; ring
  rw [hcast]
  unfold B.AB
  generalize hRd : (r : ℝ) + 1 = R at hA0 ⊢
  generalize hnd : 2 * (r : ℝ) + k + 1 = n at hA0 ⊢
  have hR : 1 ≤ R := by rw [← hRd]; linarith
  have hn : 1 ≤ n := by rw [← hnd]; linarith
  have hkr : (k : ℝ) + r ≤ n := by rw [← hnd]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hn3' : 1 ≤ n ^ 3 := one_le_pow₀ hn
  have hR4 : R ≤ R ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hR3 hR0
    have e : R ^ 4 = R * R ^ 3 := by ring
    rw [e]; linarith
  have hn3 : n ≤ n ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hn2 hn0
    have e : n ^ 3 = n * n ^ 2 := by ring
    rw [e]; linarith
  have hnn2 : n ≤ n ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hn hn0
    have e : n ^ 2 = n * n := by ring
    rw [e]; linarith
  have hX0 : 0 ≤ (Ntop : ℝ) * n ^ 2 + n ^ 3 := by positivity
  have fa : R * ((k : ℝ) + r) ≤ R * n := mul_le_mul_of_nonneg_left hkr hR0
  have fN : (N : ℝ) * n ≤ (Ntop : ℝ) * n ^ 2 :=
    (mul_le_mul_of_nonneg_right hNN hn0).trans (mul_le_mul_of_nonneg_left hnn2 hT0)
  have fb : R * ((N : ℝ) * n) ≤ R * ((Ntop : ℝ) * n ^ 2) := mul_le_mul_of_nonneg_left fN hR0
  have fc : R * n ≤ R * n ^ 3 := mul_le_mul_of_nonneg_left hn3 hR0
  have fd : R * 1 ≤ R * n ^ 3 := mul_le_mul_of_nonneg_left hn3' hR0
  have g1 : 0 ≤ R * ((Ntop : ℝ) * n ^ 2) := mul_nonneg hR0 (mul_nonneg hT0 (by positivity))
  have g2 : 0 ≤ R * n ^ 3 := mul_nonneg hR0 (by positivity)
  have hRX : R * ((Ntop : ℝ) * n ^ 2 + n ^ 3) ≤ R ^ 4 * ((Ntop : ℝ) * n ^ 2 + n ^ 3) :=
    mul_le_mul_of_nonneg_right hR4 hX0
  have e1 : 2 * ((k : ℝ) + r) * R + 1 + 2 * R * ((N : ℝ) * n + n + 5) =
      2 * (R * ((k : ℝ) + r)) + 1 + 2 * (R * ((N : ℝ) * n)) + 2 * (R * n) + 10 * (R * 1) := by ring
  have e2 : 100 * R ^ 4 * ((Ntop : ℝ) * n ^ 2 + n ^ 3) = 100 * (R ^ 4 * ((Ntop : ℝ) * n ^ 2 + n ^ 3)) := by ring
  have e3 : R * ((Ntop : ℝ) * n ^ 2 + n ^ 3) = R * ((Ntop : ℝ) * n ^ 2) + R * n ^ 3 := by ring
  rw [e1]
  rw [e2] at hA0
  rw [e3] at hRX
  linarith

theorem energyReal_of_leaves (hA : CapAdj) (hF : CapThFacts) (hSm : CVSmooth) (hCC : CVCC) (hSu : CVSupp)
    (hCg : CVCongr) (hCm : CVComm) (hB : BetaCongr) : EnergyReal := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hBu v ε hε a ha
  obtain ⟨hIB, -, -, -⟩ := hBu
  obtain ⟨-, -, -, hBuilt, -, -, -, -, -, hfs, -, hA0, -⟩ := hIB
  obtain ⟨hχ, hv⟩ := hBuilt
  obtain ⟨-, -, -, -, hfc, -⟩ := hv v
  obtain ⟨hχ1, ⟨δ, hδ, hδ0⟩, hχ3⟩ := hχ
  obtain ⟨w, rfl⟩ := ha
  set Bs := (T v).base with hBs
  set s : ℂ := M.sgn (FourierDecayAlt.D.parOf S v) (S.l + 1) with hsdef
  set F := FourierDecayAlt.D.cutF Bs χ (f v) ε with hFdef
  have hs : conj s = s := by rw [hsdef]; unfold M.sgn; simp
  have hc : 0 < δ * ε := mul_pos hδ hε
  have hN : (w.1 v).length ≤ S.Ntop :=
    (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)).trans w.2.2
  have hFs : B.CkOn ⊤ (B.GV S.G.k S.G.r) F :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs ⟨hχ1, ⟨δ, hδ, hδ0⟩, hχ3⟩ (hfs v) ε
  have hFsupp : ∀ g ∈ B.GV S.G.k S.G.r, F g ≠ 0 → δ * ε ≤ Gf S.G.k S.G.r Bs.z Bs.z' g := by
    intro g _ hg
    by_contra hlt
    push_neg at hlt
    apply hg
    have h0 : χ (Gf S.G.k S.G.r Bs.z Bs.z' g / ε) = 0 := hδ0 _ (by rw [div_lt_iff₀ hε]; exact hlt)
    simp only [hFdef, FourierDecayAlt.D.cutF, h0, Complex.ofReal_zero, zero_smul]
  have hbound := bound_aux S.G.r S.G.k (w.1 v).length S.Ntop A₀ hN hA0
  have hFcc : B.InCC (B.AB S.G.k S.G.r)
      ((w.1 v).length * (2 * S.G.r + S.G.k + 1) + (2 * S.G.r + S.G.k + 1 + 5)) F :=
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs ⟨hχ1, ⟨δ, hδ, hδ0⟩, hχ3⟩ hfc hε _ _ hbound
  have hG : Good Bs (B.AB S.G.k S.G.r)
      ((w.1 v).length * (2 * S.G.r + S.G.k + 1) + (2 * S.G.r + S.G.k + 1 + 5)) (δ * ε) F := ⟨hFs, hFcc, hFsupp⟩
  have e0 : C7.principalHermitianLattice Bs s (w.1 v) F = B.beta Bs ((w.1 v).foldr (opL S.G.k S.G.r s) F) F := rfl
  have h1 := fold_adj hA hF hB hSm hCC hSu Bs (le_refl _) hc hs (w.1 v) F F hG hG
  have h2 : B.beta Bs F ((w.1 v).reverse.foldr (opL S.G.k S.G.r s) F) =
      B.beta Bs F ((w.1 v).foldr (opL S.G.k S.G.r s) F) :=
    hB S.G.k S.G.r _ _ Bs _ _ _ _ (fun _ _ => rfl) (fold_rev hSm hCg hCm s (w.1 v) F hFs)
  have h3 := beta_conj Bs F ((w.1 v).foldr (opL S.G.k S.G.r s) F)
  rw [e0, ← Complex.conj_eq_iff_im, ← h3, ← h2, ← h1]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
