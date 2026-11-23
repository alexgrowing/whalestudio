import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacqExists

noncomputable section

open GlobalTheory.WeilM GlobalTheory.KSTransfer MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

section Defs

variable {k E : Type} [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E)

theorem map_mul_c {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    (A * B).map c = A.map c * B.map c := Matrix.map_mul (f := c.toRingHom)

def stabX {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (J : Matrix ι ι E) (X : Matrix ι (Fin r) E) :
    Subgroup (UG c J) where
  carrier := {q | ∃ a : GL (Fin r) E, ((q : GL ι E) : Matrix ι ι E) * X = X * (a : Matrix (Fin r) (Fin r) E)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by
      rw [Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro q ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    calc _ = (((q : GL ι E)⁻¹ : GL ι E) : Matrix ι ι E) * (X * (a : Matrix (Fin r) (Fin r) E)) *
          ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]; rfl
      _ = _ := by rw [← ha, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

def skew (r : ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {s | sᵀ + s.map c = 0}
  zero_mem' := by ext i j; simp
  add_mem' := by
    intro s t hs ht
    ext i j
    have h1 := congrFun (congrFun hs i) j
    have h2 := congrFun (congrFun ht i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, map_add, Matrix.zero_apply] at *
    linear_combination h1 + h2
  neg_mem' := by
    intro s hs
    ext i j
    have h1 := congrFun (congrFun hs i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, map_neg, Matrix.neg_apply,
      Matrix.zero_apply] at *
    linear_combination -h1

def stdJ {m' : ℕ} (J' : Matrix (Fin m') (Fin m') E) (r : ℕ) :
    Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E :=
  Matrix.fromBlocks J' 0 0 (Matrix.fromBlocks 0 1 1 0)

def stdX (E : Type) [Field E] (m' r : ℕ) : Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin r) E :=
  Matrix.fromRows 0 (Matrix.fromRows 1 0)

def dualGL {r : ℕ} (a : GL (Fin r) E) : GL (Fin r) E where
  val := (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map c)ᵀ
  inv := ((a : Matrix (Fin r) (Fin r) E).map c)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← map_mul_c, Units.mul_inv, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← map_mul_c, Units.inv_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]

def parMat {m' r : ℕ} (J' : Matrix (Fin m') (Fin m') E) (a : GL (Fin r) E) (g : GL (Fin m') E)
    (w : Matrix (Fin m') (Fin r) E) (s : Matrix (Fin r) (Fin r) E) :
    Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E :=
  Matrix.fromBlocks (g : Matrix (Fin m') (Fin m') E) (Matrix.fromCols 0 ((g : Matrix (Fin m') (Fin m') E) * w))
    (Matrix.fromRows (-((a : Matrix (Fin r) (Fin r) E) * ((w.map c)ᵀ * J'ᵀ))) 0)
    (Matrix.fromBlocks (a : Matrix (Fin r) (Fin r) E)
      ((a : Matrix (Fin r) (Fin r) E) * (s - (2 : E)⁻¹ • ((w.map c)ᵀ * J'ᵀ * w))) 0
      ((dualGL c a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))

def omega {m' r : ℕ} (J' : Matrix (Fin m') (Fin m') E) (w w' : Matrix (Fin m') (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  (2 : E)⁻¹ • ((w'.map c)ᵀ * J'ᵀ * w - (w.map c)ᵀ * J'ᵀ * w')

end Defs

section Top

variable {k E : Type} [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end Top

section Mod

variable {k E : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Field E] [Algebra k E]
  {c : E →ₐ[k] E} {r : ℕ}

end Mod

section Steps

def IsWeight {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (Q : Subgroup G) (ν : Measure Q)
    (φ : G → ℝ) : Prop :=
  Measurable φ ∧ (∀ g, 0 ≤ φ g) ∧ (∃ (K : Set G) (B : ℝ), IsCompact K ∧ ∀ g, φ g ≤ B ∧ (φ g ≠ 0 → g ∈ K)) ∧
    ∀ g, ∫⁻ q : Q, ENNReal.ofReal (φ ((q : G)⁻¹ * g)) ∂ν = 1

def WeightExists : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (Q : Subgroup G), IsClosed (Q : Set G) →
    (∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ Q, ∃ x ∈ C, g = q * x) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure Q) [ν.IsHaarMeasure],
      ∃ φ : G → ℝ, IsWeight Q ν φ ∧ ∀ U ∈ nhds (1 : G), 0 < ∫ g in U, φ g ∂μ

def WeightIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (Q : Subgroup G) [LocallyCompactSpace Q]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure Q) [ν.IsHaarMeasure] (φ φ' : G → ℝ), IsWeight Q ν φ → IsWeight Q ν φ' →
    ∀ F : G → ℂ, Continuous F → (∀ (q : Q) (g : G), F (q * g) = ((modularCharacterFun q : ℝ) : ℂ) * F g) →
      ∫ g, (φ g : ℂ) * F g ∂μ = ∫ g, (φ' g : ℂ) * F g ∂μ

def AvgAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] (Q : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → (∀ g : G, modularCharacterFun g = 1) →
    (∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ Q, ∃ x ∈ C, g = q * x) →
    ∃ Av : (G → ℂ) →ₗ[ℂ] ℂ,
      (∀ U : Subgroup G, IsOpen (U : Set G) → ∃ (s : Finset G) (w : G → ℂ),
        ∀ F : G → ℂ, (∀ g, ∀ u ∈ U, F (g * u) = F g) → Av F = ∑ g ∈ s, w g * F g) ∧
      (∀ F : G → ℂ, (∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, F (g * u) = F g) →
        (∀ (q : Q) (g : G), F (q * g) = ((modularCharacterFun q : ℝ) : ℂ) * F g) →
        ∀ g₀, Av (fun g => F (g * g₀)) = Av F) ∧
      (∀ F : G → ℂ, (∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, F (g * u) = F g) →
        (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → F 1 ≠ 0 → Av F ≠ 0)

def ChartMod : Prop :=
  ∀ (Q M A B : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q]
    [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [T2Space B] [MeasurableSpace B] [BorelSpace B]
    (Φ : M × A × B ≃ₜ Q) (L₁ : M → A ≃ₜ+ A) (L₂ : M → B ≃ₜ+ B) (ω : A → A → B), (∀ x : M, modularCharacterFun x = 1) →
    (∀ x a b x' a' b', Φ (x, a, b) * Φ (x', a', b') = Φ (x * x', L₁ x' a + a', L₂ x' b + b' + ω (L₁ x' a) a')) →
    ∀ x a b, modularCharacterFun (Φ (x, a, b)) * (addEquivAddHaarChar (L₁ x) * addEquivAddHaarChar (L₂ x)) = 1

def UnimodU : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm c J → ∀ [LocallyCompactSpace (UG c J)] (g : UG c J),
    modularCharacterFun g = 1

def UnimodM : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (r n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm c J →
    ∀ [LocallyCompactSpace (GL (Fin r) E × UG c J)] (x : GL (Fin r) E × UG c J), modularCharacterFun x = 1

def AbsExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
    ∃ v : E →*₀ ℝ≥0, IsCompact {y : E | v y ≤ 1}

def FrameCpt : Prop :=
  ∀ (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E] (v : E →*₀ ℝ≥0),
    IsCompact {y : E | v y ≤ 1} → ∀ m r : ℕ, ∃ S : Set (Matrix (Fin m) (Fin r) E), IsCompact S ∧
      (∀ Y ∈ S, ∀ u, Y *ᵥ u = 0 → u = 0) ∧ ∀ Y : Matrix (Fin m) (Fin r) E, (∀ u, Y *ᵥ u = 0 → u = 0) →
        ∃ Y₀ ∈ S, ∃ a : GL (Fin r) E, Y = Y₀ * (a : Matrix (Fin r) (Fin r) E)

def Cocpt : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ (m r : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm c J → ∀ X : Matrix (Fin m) (Fin r) E, Xᵀ * J * X.map c = 0 →
    (∀ u, X *ᵥ u = 0 → u = 0) → ∃ C : Set (UG c J), IsCompact C ∧ ∀ g, ∃ q ∈ stabX c J X, ∃ x ∈ C, g = q * x

def JacMat : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (p q : ℕ) [LocallyCompactSpace (Matrix (Fin p) (Fin q) E)]
    [MeasurableSpace (Matrix (Fin p) (Fin q) E)] [BorelSpace (Matrix (Fin p) (Fin q) E)]
    (g : GL (Fin p) E) (a : GL (Fin q) E) (L : Matrix (Fin p) (Fin q) E ≃ₜ+ Matrix (Fin p) (Fin q) E),
    (∀ u, L u = (g : Matrix (Fin p) (Fin p) E) * u * (a : Matrix (Fin q) (Fin q) E)) →
      (addEquivAddHaarChar L : ℝ) = detMod k g ^ q * detMod k a ^ p

def JacSkew : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ [IsTopologicalRing E] (r : ℕ) [LocallyCompactSpace (skew c r)] [MeasurableSpace (skew c r)] [BorelSpace (skew c r)]
    (a : GL (Fin r) E) (L : skew c r ≃ₜ+ skew c r),
    (∀ s, (L s : Matrix (Fin r) (Fin r) E) = ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (s : Matrix (Fin r) (Fin r) E) *
      ((dualGL c a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) → (addEquivAddHaarChar L : ℝ) * detMod k a ^ r = 1

def ParUnit : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E), (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' → ∀ (a : GL (Fin r) E) (g : UG c J')
    (w : Matrix (Fin m') (Fin r) E) (s : Matrix (Fin r) (Fin r) E), s ∈ skew c r →
      (parMat c J' a g w s)ᵀ * stdJ J' r * (parMat c J' a g w s).map c = stdJ J' r

def ParLaw : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E), (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E) (a a' : GL (Fin r) E) (g g' : UG c J')
    (w w' w₁ : Matrix (Fin m') (Fin r) E) (s s' s₁ : Matrix (Fin r) (Fin r) E),
    w₁ = (((g' : GL (Fin m') E)⁻¹ : GL (Fin m') E) : Matrix (Fin m') (Fin m') E) * w *
      ((dualGL c a' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) →
    s₁ = ((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * s * ((dualGL c a' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) →
      parMat c J' a g w s * parMat c J' a' g' w' s' =
        parMat c J' (a * a') ((g * g' : UG c J') : GL (Fin m') E) (w₁ + w') (s₁ + s' + omega c J' w₁ w')

def ParDec : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E), (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' → ∀ (q : UG c (stdJ J' r)) (a : GL (Fin r) E),
    ((q : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) : Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) * stdX E m' r =
      stdX E m' r * (a : Matrix (Fin r) (Fin r) E) →
    ∃ (g : UG c J') (w : Matrix (Fin m') (Fin r) E), ∃ s ∈ skew c r,
      ((q : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) : Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) =
        parMat c J' a g w s

def ParChart : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] (c : E →ₐ[k] E),
    Continuous c → (∀ z, c (c z) = z) → (2 : E) ≠ 0 →
  ∀ (m' r : ℕ) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' →
    ∃ (Φ : (GL (Fin r) E × UG c J') × Matrix (Fin m') (Fin r) E × skew c r ≃ₜ stabX c (stdJ J' r) (stdX E m' r))
      (L₁ : GL (Fin r) E × UG c J' → Matrix (Fin m') (Fin r) E ≃ₜ+ Matrix (Fin m') (Fin r) E)
      (L₂ : GL (Fin r) E × UG c J' → skew c r ≃ₜ+ skew c r)
      (ω : Matrix (Fin m') (Fin r) E → Matrix (Fin m') (Fin r) E → skew c r),
      (∀ x w, L₁ x w = (((x.2 : GL (Fin m') E)⁻¹ : GL (Fin m') E) : Matrix (Fin m') (Fin m') E) * w *
        ((dualGL c x.1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) ∧
      (∀ x s, (L₂ x s : Matrix (Fin r) (Fin r) E) = ((x.1⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
        (s : Matrix (Fin r) (Fin r) E) * ((dualGL c x.1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) ∧
      (∀ x w s x' w' s', Φ (x, w, s) * Φ (x', w', s') = Φ (x * x', L₁ x' w + w', L₂ x' s + s' + ω (L₁ x' w) w')) ∧
      ∀ x w s, (((Φ (x, w, s) : UG c (stdJ J' r)) : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) :
        Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) * stdX E m' r =
          stdX E m' r * (x.1 : Matrix (Fin r) (Fin r) E)

def StabTransport : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] (c : E →ₐ[k] E)
    (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (J' : Matrix (Fin m') (Fin m') E), IsHerm c J' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → Pᵀ * JA * P.map c = stdJ J' r →
    (∃ p : Matrix (Fin r) (Fin m) E, p * colX P = 1) ∧ (colX P)ᵀ * JA * (colX P).map c = 0 ∧
    ∃ e : stabX c (stdJ J' r) (stdX E m' r) ≃ₜ* stabX c JA (colX P), ∀ (q : stabX c (stdJ J' r) (stdX E m' r))
      (a : GL (Fin r) E), (((q : UG c (stdJ J' r)) : GL (Fin m' ⊕ (Fin r ⊕ Fin r)) E) :
        Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) * stdX E m' r =
          stdX E m' r * (a : Matrix (Fin r) (Fin r) E) →
      (((e q : UG c JA) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * colX P = colX P * (a : Matrix (Fin r) (Fin r) E)

end Steps

section Law

end Law

end GlobalTheory.ParAvg

end
