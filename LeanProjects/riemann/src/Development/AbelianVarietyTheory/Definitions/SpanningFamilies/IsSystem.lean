import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible

open Matrix Complex NumberField MeasureTheory
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 : ℕ} (X : Data E r)
  (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

def IsUn (γ : GL (Fin r) E) : Prop :=
  ∀ x y, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
    herm X.Gm x y

abbrev TF (n g : ℕ) : Type := Matrix (Fin n) (Fin g) ℚ → ℂ

def thA (φ : TF n g) (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) : ℂ :=
  (hMat X bas idx x).det ^ (n / 2) *
    cexp (Real.pi / 2 * ∑ k, (hMat X bas idx x *ᵥ z k) ⬝ᵥ imInv X bas idx x *ᵥ
      (hMat X bas idx x *ᵥ z k)) * thS φ (tauMat X bas idx x) fun k => hMat X bas idx x *ᵥ z k

def thP (φ : TF n g) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) : ℂ :=
  polyDeriv P (letterDir X hr idx) (thA X bas idx φ x) 0

open Classical in

def wG (γ : GL (Fin r) E) (φ : TF n g) : TF n g :=
  if h : ∃ ψ : TF n g, IsSB ψ ∧ ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x
  then h.choose else 0

def vecQ (m : Fin g ⊕ Fin g → ℚ) : Fin r → E :=
  ∑ j, m j • ((bas (Pi.single j 1) : X.Λ) : Fin r → E)

def crd (v : Fin r → E) : Fin g ⊕ Fin g → ℚ := Function.invFun (vecQ X bas) v

def heisG (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) : TF n g :=
  heisS (Matrix.of fun k i => crd X bas (y k) (Sum.inl i))
    (Matrix.of fun k i => crd X bas (y k) (Sum.inr i)) φ

def aLin (x₁ x₂ : Frame X.Ψ r) : CM X.Ψ r r := fun τ => Matrix.of fun a c =>
  if (a : ℕ) < X.p0 then ∑ b, τ.1 (X.Gm c b) * conj (x₂ τ b a) else (mat x₁ τ)⁻¹ a c

def aAnti (x₁ x₂ : Frame X.Ψ r) : CM X.Ψ r r := fun τ => Matrix.of fun a c =>
  if (a : ℕ) < X.p0 then ∑ b, x₁ τ b a * τ.1 (X.Gm b c) else conj ((mat x₂ τ)⁻¹ a c)

def dblZ (x₁ x₂ : Frame X.Ψ r) : CM X.Ψ r r := fun τ => (τ.1 X.κ0 / 4) •
  (((aLin X x₁ x₂ τ)⁻¹ * Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) *
    aLin X x₁ x₂ τ)ᵀ * X.Gm.map τ.1)

def dblz (x₁ x₂ : Frame X.Ψ r) (z₁ w : Fin n → Fin g → ℂ) : CM X.Ψ n r := fun τ =>
  Matrix.of fun k => (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ (aAnti X x₁ x₂ τ)⁻¹ *ᵥ fun a =>
    if (a : ℕ) < X.p0 then z₁ k (idx.symm (τ, a)) else w k (idx.symm (τ, a)))

def dblz' (x₁ x₂ : Frame X.Ψ r) (z₁ w : Fin n → Fin g → ℂ) : CM X.Ψ n r := fun τ =>
  Matrix.of fun k => (τ.1 X.κ0 / 2) • (((aLin X x₁ x₂ τ)⁻¹ *ᵥ fun a =>
    if (a : ℕ) < X.p0 then w k (idx.symm (τ, a)) else z₁ k (idx.symm (τ, a))) ᵥ* X.Gm.map τ.1)

def kZero (x₁ x₂ : Frame X.Ψ r) (z₁ w : Fin n → Fin g → ℂ) : ℂ :=
  ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ *
    cexp (Real.pi * ∑ k, dblz' X idx x₁ x₂ z₁ w τ k ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ
      dblz X idx x₁ x₂ z₁ w τ k)

def IsDbl (φ₁ φ₂ : TF n g) (ψ : Matrix (Fin n) (Fin r) E → ℂ) : Prop :=
  ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ,
    thA X bas idx φ₁ x₁ z₁ * conj (thA X bas idx φ₂ x₂ fun k i => conj (w k i)) =
      kZero X idx x₁ x₂ z₁ w *
        thH X.Ψ ψ (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)

open Classical in

def dbl (φ₁ φ₂ : TF n g) : Matrix (Fin n) (Fin r) E → ℂ :=
  if h : ∃ ψ, IsSB ψ ∧ IsDbl X bas idx φ₁ φ₂ ψ then h.choose else 0

def dblT : M2 E r :=
  Matrix.fromBlocks 1 ((X.κ0 / 4) • X.Gm) (-1) ((X.κ0 / 4) • X.Gm)

def iota (γ₁ γ₂ : GL (Fin r) E) : M2 E r :=
  (dblT X)⁻¹ * Matrix.fromBlocks ((γ₁⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ 0 0
    ((γ₂⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ * dblT X

def barP {σ : Type} (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ := MvPolynomial.map (starRingEnd ℂ) P

def biDeriv {J : Type} [Fintype J] (P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (F : (Fin n → Fin g → ℂ) → (Fin n → Fin g → ℂ) → ℂ) : ℂ :=
  ∑ j, polyDeriv (P j) (letterDir X hr idx)
    (fun z₁ => polyDeriv (barP (P j)) (letterDir X hr idx) (F z₁) 0) 0

def kern {J : Type} [Fintype J] (P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (x₁ x₂ : Frame X.Ψ r) : ℂ := biDeriv X hr idx P (kZero X idx x₁ x₂)

def InvFam {T J : Type} [Fintype J] {p q : ℕ} (P : J → Harm.Poly ℂ T p q (Fin n)) : Prop :=
  ∀ u : T → GL (Fin n) ℂ, (∀ t, (u t : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) →
    ∀ z w : Harm.Var T p q (Fin n) → ℂ,
      ∑ j, MvPolynomial.eval z (Harm.colActHom u (P j)) *
        conj (MvPolynomial.eval w (Harm.colActHom u (P j))) =
      ∑ j, MvPolynomial.eval z (P j) * conj (MvPolynomial.eval w (P j))

def sgnM : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def slab (δ : ℝ) : Set (Frame X.Ψ r) :=
  {x | ∀ τ : X.Ψ, ∀ a b, ‖gram τ.1 X.Gm (mat x τ) a b - sgnM X a b‖ < δ}

def mapL (γ : GL (Fin r) E) (L : Lt E r) : Lt E r :=
  L.map ((Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E))

structure IsSystem (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r))
    (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ) : Prop where
  un : ∀ γ ∈ Δ, IsUn X γ
  lat : ∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤
  stab : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛
  sb : ∀ L ∈ 𝓛, ∀ Λ ∈ Vset E n M, IsSB (Φ L Λ)
  norm : ∃ a : ℝ, 0 < a ∧ (∀ L ∈ 𝓛, ∀ Λ ∈ Vset E n M, ip (Φ L Λ) (Φ L Λ) = a) ∧
    ∃ (b : Lt E r → Lt E r → ℝ) (θ : ℝ), θ < 1 ∧
      (∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, ∀ Λ ∈ Vset E n M, ‖ip (Φ L Λ) (Φ L' Λ)‖ ≤ a * b L L') ∧
      ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => b L L'.1) ∧
        ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, b L L'.1 ≤ θ
  mu : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ‖μ γ L‖ = 1 ∧
    ∀ Λ ∈ Vset E n M, wG X bas idx γ (Φ L Λ) = μ γ L • Φ (mapL γ L) Λ
  supp : ∀ γ, IsUn X γ → γ ∉ Δ → ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, ∀ Λ ∈ Vset E n M,
    ip (Φ L Λ) (wG X bas idx γ (Φ L' Λ)) = 0
  cusp : ∀ ξ : Fin r → E, ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∀ L ∈ 𝓛, ∀ Λ ∈ Vset E n M,
    ∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧
      ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) (Φ L Λ) = 0
  adm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, ∃ R, admitted M R fun Λ => dbl X bas idx (Φ L Λ) (Φ L' Λ)

structure IsForm (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (μ : GL (Fin r) E → Lt E r → ℂ)
    (la : Wt X.Ψ r) (F : Lt E r → Frame X.Ψ r → ℂ) : Prop where
  hol : ∀ L ∈ 𝓛, DifferentiableOn ℂ (F L) X.dom
  bor : ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F L (rmul x b) = bchar la b * F L x
  aut : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ x ∈ X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x
  bdd : ∃ C : ℝ, ∀ L ∈ 𝓛, ∀ x ∈ X.dom, X.pnorm la (F L) x ≤ C

def InSpan (M : ℕ) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g)
    (𝓗 : Set (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) (F : Lt E r → Frame X.Ψ r → ℂ) : Prop :=
  ∃ (m : ℕ) (Λ : Fin m → Lt E n) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (a : Fin m → ℂ),
    (∀ i, Λ i ∈ Vset E n M ∧ P i ∈ 𝓗) ∧
    ∀ L ∈ 𝓛, ∀ x ∈ X.dom, F L x = ∑ i, a i * thP X hr bas idx (Φ L (Λ i)) (P i) x

def SelfD (L : Lt E r) : Prop := L.FG ∧ ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, EF X x y = k

def epsW (w : E) (y : Matrix (Fin n) (Fin r) E) : ℂ :=
  cexp (Real.pi * I * ((∑ k, EF X (y k) (w • y k) : ℚ) : ℂ))

def tens (Λ : Lt E n) (L : Lt E r) : AddSubgroup (Matrix (Fin n) (Fin r) E) :=
  AddSubgroup.closure {y | ∃ v ∈ Λ, ∃ u ∈ L, y = vecMulVec v u}

def IsVac (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) (φ : TF n g) : Prop :=
  IsSB φ ∧ ip φ φ = 1 ∧ ∀ y ∈ A, epsW X w y • heisG X bas y φ = φ

def projA (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) (φ : TF n g) : TF n g :=
  ((((fun y => epsW X w y • heisG X bas y φ) '' A).ncard : ℕ) : ℂ)⁻¹ •
    ∑ᶠ ψ ∈ (fun y => epsW X w y • heisG X bas y φ) '' A, ψ

def unitv (φ : TF n g) : TF n g := ((Real.sqrt (ip φ φ).re : ℝ) : ℂ)⁻¹ • φ

def idq (𝔞 𝔟 : Ideal (𝓞 E)) (L : Lt E r) : Lt E r where
  carrier := {v | ∀ b ∈ 𝔟, b • v ∈ 𝔞 • L}
  add_mem' := fun hu hv b hb => by rw [smul_add]; exact add_mem (hu b hb) (hv b hb)
  zero_mem' := fun b _ => by rw [smul_zero]; exact zero_mem _
  smul_mem' := fun c _ hv b hb => by rw [smul_comm]; exact Submodule.smul_mem _ c (hv b hb)

def Cong (𝔪 : Ideal (𝓞 E)) (u v : Fin r → E) : Prop :=
  ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ s • (u - v) ∈ 𝔪 • X.Λ

structure Level where

  𝔪 : Ideal (𝓞 E)
  proper : 𝔪 ≠ ⊤
  ne_bot : 𝔪 ≠ ⊥
  cop : IsCoprime 𝔪 (conjI 𝔪)
  odd : IsCoprime 𝔪 (Ideal.span {2})

  β : Fin r → Fin r → E
  β_mem : ∀ i, β i ∈ X.Λ
  β_span : X.Λ ≤ Submodule.span (𝓞 E) (Set.range β) ⊔ 𝔪 • X.Λ

  J : Subgroup (GL (Fin r) (𝓞 E ⧸ 𝔪))

  lam : J →* ℂˣ

  w : E
  w_int : IsIntegral ℤ w
  w_tr : w + cc w = 1

variable {X}

def Level.Red (D : Level X) (u : Fin r → Fin r → E) (k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Prop :=
  ∃ k' : Matrix (Fin r) (Fin r) (𝓞 E), k'.map (Ideal.Quotient.mk D.𝔪) = k ∧
    ∀ i, Cong X D.𝔪 (u i) (∑ j, k' j i • D.β j)

def Level.grp (D : Level X) : Subgroup (GL (Fin r) E) := Subgroup.closure
  {γ | IsUn X γ ∧ ∃ k ∈ D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k}

def Level.lats (D : Level X) : Set (Lt E r) :=
  {L | SelfD X L ∧ ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) (D.𝔪 * conjI D.𝔪) ∧
    (∀ v ∈ L, s • v ∈ X.Λ) ∧ ∀ v ∈ X.Λ, s • v ∈ L}

open Classical in

def Level.dat (D : Level X) (hn : r ≤ n) (y : Matrix (Fin n) (Fin r) E) : ℂ :=
  if h : (∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y k) 0 then (D.lam h.1.choose : ℂˣ) else 0

def Level.sh (D : Level X) (L : Lt E r) : Lt E r := idq D.𝔪 (conjI D.𝔪) L

def Level.phi (D : Level X) (hn : r ≤ n) (v₀ : Lt E r → TF n g) (L : Lt E r) (Λ : Lt E n) :
    TF n g :=
  ∑ᶠ c : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _,
    D.dat hn (c.out : Matrix (Fin n) (Fin r) E) • heisG X bas (c.out : Matrix (Fin n) (Fin r) E)
      (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)))

end

end GlobalTheory.SW
