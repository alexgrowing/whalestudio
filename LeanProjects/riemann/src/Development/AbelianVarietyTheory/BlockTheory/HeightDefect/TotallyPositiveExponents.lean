import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaWeightHeightConstants

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField Matrix
open scoped ComplexOrder

variable {R : Ranks}

abbrev Pl (R : Ranks) : Type := ↥(R.Psi)

instance instFintypePl : Fintype (Pl R) := Fintype.ofFinite _

def tau (H : Host R) (τ : Pl R) : H.E →+* ℂ := H.emb τ.1

theorem tau_conj (H : Host R) (τ : Pl R) (x : H.E) :
    tau H τ (H.conj x) = starRingEnd ℂ (tau H τ x) := H.conjE_apply _ x

theorem conj_conj (H : Host R) (x : H.E) : H.conj (H.conj x) = x :=
  H.φ₀.injective (by
    rw [show H.φ₀ (H.conj (H.conj x)) = _ from H.conjE_apply _ _,
      show H.φ₀ (H.conj x) = _ from H.conjE_apply _ _]
    simp)

abbrev V (H : Host R) (n : ℕ) : Type := Fin n → H.E

variable {H : Host R} {n : ℕ}

def IsLattice (X : Submodule (𝓞 H.E) (V H n)) : Prop :=
  X.FG ∧ Submodule.span H.E (X : Set (V H n)) = ⊤

def idealMul (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) (N : Submodule (𝓞 H.E) (V H n)) :
    Submodule (𝓞 H.E) (V H n) :=
  Submodule.span (𝓞 H.E) {w | ∃ a ∈ 𝔞, ∃ v ∈ N, w = a • v}

theorem smul_dot (a : 𝓞 H.E) (y x : V H n) : (a • y) ⬝ᵥ x = y ⬝ᵥ (a • x) := by
  rw [smul_dotProduct, dotProduct_smul]

def dualO (X : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) where
  carrier := {y | ∀ x ∈ X, IsIntegral ℤ (y ⬝ᵥ x)}
  add_mem' := fun {y y'} hy hy' x hx => by rw [add_dotProduct]; exact (hy x hx).add (hy' x hx)
  zero_mem' := fun x _ => by rw [zero_dotProduct]; exact isIntegral_zero
  smul_mem' := fun a y hy x hx => by rw [smul_dot]; exact hy _ (X.smul_mem a hx)

def dualZ (X : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) where
  carrier := {y | ∀ x ∈ X, ∃ z : ℤ, Algebra.trace ℚ H.E (y ⬝ᵥ x) = z}
  add_mem' := fun {y y'} hy hy' x hx => by
    obtain ⟨z, h⟩ := hy x hx
    obtain ⟨z', h'⟩ := hy' x hx
    exact ⟨z + z', by rw [add_dotProduct, map_add, h, h']; push_cast; rfl⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := fun a y hy x hx => by rw [smul_dot]; exact hy _ (X.smul_mem a hx)

def cochar (N : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) := idealMul H.AA N

def charLattice (N : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) := dualZ (cochar N)

def DualsClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (X : Submodule (𝓞 H.E) (V H n)), IsLattice X →
  IsLattice (dualO X) ∧ IsLattice (dualZ X) ∧
  (∀ φ : X →ₗ[𝓞 H.E] 𝓞 H.E, ∃! y : dualO X, ∀ x : X, (y : V H n) ⬝ᵥ (x : V H n) = (φ x : H.E)) ∧
  (∀ φ : X →+ ℤ, ∃! y : dualZ X, ∀ x : X,
    Algebra.trace ℚ H.E ((y : V H n) ⬝ᵥ (x : V H n)) = (φ x : ℚ)) ∧
  dualZ X = idealMul ((H.ddE : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E))⁻¹ (dualO X) ∧
  dualZ (dualZ X) = X ∧
  Module.finrank ℤ X = 2 * R.f * n

def CuspLatticeClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (N : Submodule (𝓞 H.E) (V H n)),
  IsLattice N → IsLattice (charLattice N) ∧ dualZ (charLattice N) = cochar N

def Herm (H : Host R) (n : ℕ) : Submodule ℚ (Matrix (Fin n) (Fin n) H.E) where
  carrier := {χ | ∀ i k, χ k i = H.conj (χ i k)}
  add_mem' := fun {a b} ha hb i k => by simp [ha i k, hb i k]
  zero_mem' := fun i k => by simp
  smul_mem' := fun q a ha i k => by
    simp only [Matrix.smul_apply, ha i k, Rat.smul_def, map_mul, map_ratCast]

def val (χ : Herm H n) (y y' : V H n) : H.E :=
  ∑ i, ∑ k, y i * (χ : Matrix (Fin n) (Fin n) H.E) i k * H.conj (y' k)

theorem conj_val (χ : Herm H n) (y y' : V H n) : H.conj (val χ y y') = val χ y' y := by
  simp only [val, map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← χ.2 k i]; ring

def HermMatrixClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (h : V H n → V H n → H.E),
  (∀ y', IsLinearMap H.E fun y => h y y') → (∀ y y', h y' y = H.conj (h y y')) →
  ∃! χ : Herm H n, ∀ y y', val χ y y' = h y y'

def sqForm (x : V H n) : Herm H n :=
  ⟨Matrix.of fun i k => x i * H.conj (x k), fun i k => by simp [conj_conj, mul_comm]⟩

def symForm (x x' : V H n) : Herm H n :=
  ⟨Matrix.of fun i k => x i * H.conj (x' k) + x' i * H.conj (x k), fun i k => by
    simp only [Matrix.of_apply, map_add, map_mul, conj_conj]; ring⟩

def atPl (χ : Herm H n) (τ : Pl R) : Matrix (Fin n) (Fin n) ℂ :=
  (χ : Matrix (Fin n) (Fin n) H.E).map (tau H τ)

def TotPos (χ : Herm H n) : Prop := ∀ τ, (atPl χ τ).PosDef

def TotNonneg (χ : Herm H n) : Prop := ∀ τ, (atPl χ τ).PosSemidef

def IntegralOn (X : Submodule (𝓞 H.E) (V H n)) (χ : Herm H n) : Prop :=
  ∀ y ∈ dualO X, ∀ y' ∈ dualO X, IsIntegral ℤ (val χ y y')

def diagVal (χ : Herm H n) (ξ : V H n) : H.F :=
  ⟨val χ ξ ξ, (H.conjE_mem_hostF_iff _).2 (conj_val χ ξ ξ)⟩

def trVal (χ : Herm H n) (ξ : V H n) : ℚ := Algebra.trace ℚ H.F (diagVal χ ξ)

def TraceClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (χ : Herm H n) (ξ : V H n),
  ((trVal χ ξ : ℚ) : ℂ) = ∑ τ : Pl R, tau H τ (val χ ξ ξ) ∧
  2 * trVal χ ξ = Algebra.trace ℚ H.E (val χ ξ ξ)

def levelOne (X : Submodule (𝓞 H.E) (V H n)) : AddSubgroup (Herm H n) :=
  AddSubgroup.closure {χ | ∃ x ∈ X, ∃ x' ∈ X, χ = symForm x x'}

def level (H : Host R) : ℕ := H.g 0 * H.g 1

theorem level_pos (H : Host R) : 0 < level H := Nat.mul_pos (H.g_prime 0).pos (H.g_prime 1).pos

def expGroup (X : Submodule (𝓞 H.E) (V H n)) : AddSubgroup (Herm H n) :=
  (levelOne X).comap (nsmulAddMonoidHom (level H))

def expNonneg (X : Submodule (𝓞 H.E) (V H n)) : Set (Herm H n) := {χ | χ ∈ expGroup X ∧ TotNonneg χ}

def cuspExponents (X : Submodule (𝓞 H.E) (V H n)) : Set (Herm H n) := {χ | χ ∈ expGroup X ∧ TotPos χ}

def modesOver (X : Submodule (𝓞 H.E) (V H n)) (ξ : V H n) (ν : H.F) : Set (Herm H n) :=
  {χ | χ ∈ cuspExponents X ∧ diagVal χ ξ = ν}

def IsShallow (X : Submodule (𝓞 H.E) (V H n)) (c : ℝ) (χ : Herm H n) : Prop :=
  ∃ ξ ∈ dualZ X, ξ ≠ 0 ∧ ((trVal χ ξ : ℚ) : ℝ) ≤ c

abbrev XR (R : Ranks) (n : ℕ) : Type := Pl R → Fin n → ℂ

def toR (H : Host R) (n : ℕ) : V H n →+ XR R n where
  toFun x τ i := tau H τ (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def act (a : H.E) (u : XR R n) : XR R n := fun τ i => tau H τ a * u τ i

theorem toR_smul (a : 𝓞 H.E) (x : V H n) : toR H n (a • x) = act (a : H.E) (toR H n x) := by
  ext τ i
  simp [toR, act, Algebra.smul_def]

def RealPointsClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (X : Submodule (𝓞 H.E) (V H n)),
  IsLattice X → ∀ (ι : Type) (b : Module.Basis ι ℤ X),
    LinearIndependent ℝ (fun i => toR H n (b i)) ∧
    Submodule.span ℝ (Set.range fun i => toR H n (b i)) = ⊤

def Bal (H : Host R) (n : ℕ) : Submodule ℝ (XR R n →ₗ[ℝ] XR R n →ₗ[ℝ] ℝ) where
  carrier := {B | (∀ u v, B u v = B v u) ∧
    ∀ (a : 𝓞 H.E) u v, B (act (a : H.E) u) v = B u (act (H.conj (a : H.E)) v)}
  add_mem' := by
    rintro B C ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun u v => by simp [h1 u v, h3 u v], fun a u v => by simp [h2 a u v, h4 a u v]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro t B ⟨h1, h2⟩
    exact ⟨fun u v => by simp [h1 u v], fun a u v => by simp [h2 a u v]⟩

def bil (B : Bal H n) (u v : XR R n) : ℝ := (B : XR R n →ₗ[ℝ] XR R n →ₗ[ℝ] ℝ) u v

def Q (B : Bal H n) (u : XR R n) : ℝ := bil B u u / 2

open Classical in

def vec (τ : Pl R) (i : Fin n) (z : ℂ) : XR R n := Pi.single τ (Pi.single i z)

def hermPart (B : Bal H n) (τ : Pl R) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => ((bil B (vec τ i 1) (vec τ k 1) : ℂ) -
    Complex.I * (bil B (vec τ i 1) (vec τ k Complex.I) : ℂ)) / 2

def trBil (b : Pl R → Matrix (Fin n) (Fin n) ℂ) : XR R n →ₗ[ℝ] XR R n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ τ, ∑ i, ∑ k, 2 * (starRingEnd ℂ (u τ i) * b τ i k * v τ k).re)
    (fun u u' v => by
      simp only [Pi.add_apply, map_add, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib])
    (fun t u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun k _ => ?_
      simp; ring)
    (fun u v v' => by
      simp only [Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib])
    (fun t u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun k _ => ?_
      simp; ring)

def ofHerm (H : Host R) (b : Pl R → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ τ, (b τ).IsHermitian) : Bal H n :=
  ⟨trBil b, fun u v => by
    simp only [trBil, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← (hb τ).apply k i]
    simp; ring,
   fun a u v => by
    simp only [trBil, LinearMap.mk₂_apply, act, tau_conj, map_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => ?_
    congr 2; ring⟩

def TrClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ),
  (∀ B : Bal H n, ∃ hb : ∀ τ, (hermPart B τ).IsHermitian, ofHerm H (hermPart B) hb = B) ∧
  (∀ (b : Pl R → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ τ, (b τ).IsHermitian), hermPart (ofHerm H b hb) = b) ∧
  ∀ (B : Bal H n) (u : XR R n), (Q B u : ℂ) = ∑ τ, star (u τ) ⬝ᵥ (hermPart B τ *ᵥ u τ)

def IsPSD (B : Bal H n) : Prop := ∀ u, 0 ≤ bil B u u

def IsPD (B : Bal H n) : Prop := ∀ u, u ≠ 0 → 0 < bil B u u

def kerR (B : Bal H n) : Submodule ℝ (XR R n) := LinearMap.ker (B : XR R n →ₗ[ℝ] XR R n →ₗ[ℝ] ℝ)

def RationalKernel (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) : Prop :=
  Submodule.span ℝ {u | u ∈ kerR B ∧ ∃ x ∈ X, u = toR H n x} = kerR B

def IsPSDRat (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) : Prop := IsPSD B ∧ RationalKernel X B

def IntValued (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, ∃ z : ℤ, bil B (toR H n x) (toR H n x') = z

def pairing (χ : Herm H n) (B : Bal H n) : ℝ := ∑ τ, (Matrix.trace (atPl χ τ * hermPart B τ)).re

def PairingClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (B : Bal H n),
  (∀ (χ : Herm H n) τ, (Matrix.trace (atPl χ τ * hermPart B τ)).im = 0) ∧
  (∀ x : V H n, pairing (sqForm x) B = Q B (toR H n x)) ∧
  ∀ x x' : V H n, pairing (symForm x x') B = bil B (toR H n x) (toR H n x')

def ExponentClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (X : Submodule (𝓞 H.E) (V H n)),
  IsLattice X → ∀ χ : Herm H n,
    (χ ∈ levelOne X ↔ ∀ B : Bal H n, IntValued X B → ∃ z : ℤ, pairing χ B = z) ∧
    (χ ∈ levelOne X ↔ IntegralOn X χ) ∧
    (χ ∈ expGroup X → ∀ y ∈ dualO X, ∀ y' ∈ dualO X, IsIntegral ℤ ((level H : H.E) * val χ y y')) ∧
    (χ ∈ expGroup X → ∀ ξ ∈ dualZ X, ∀ ξ' ∈ dualZ X, (level H : H.E) * val χ ξ ξ' ∈
      ((H.ddE : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E))⁻¹ ^ 2)

def PositivityClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (X : Submodule (𝓞 H.E) (V H n)),
  IsLattice X → ∀ χ : Herm H n,
    TotPos χ ↔ ∀ B : Bal H n, IsPSDRat X B → B ≠ 0 → 0 < pairing χ B

def restrict (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) :
    Formalism.MainNotions.ModuliIntegralCharts.SymB (fun x : H.E => H.conj x) X :=
  ⟨LinearMap.mk₂ ℤ (fun a b : X => bil B (toR H n a) (toR H n b))
      (fun a a' b => by simp [bil]) (fun z a b => by
        simp only [bil, Submodule.coe_smul_of_tower, map_zsmul, LinearMap.smul_apply])
      (fun a b b' => by simp [bil]) (fun z a b => by
        simp only [bil, Submodule.coe_smul_of_tower, map_zsmul, LinearMap.smul_apply]),
    fun a b => B.2.1 _ _,
    fun c c' h a b => by
      change bil B (toR H n (c • (a : V H n))) (toR H n b) = bil B (toR H n a) (toR H n (c' • (b : V H n)))
      rw [toR_smul, toR_smul, h]
      exact B.2.2 c _ _⟩

def phiC (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) : ℝ :=
  Formalism.MainNotions.ModuliIntegralCharts.phiC (fun x : H.E => H.conj x) (restrict X B)

def phiValues (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) : Set ℝ :=
  {t | ∃ l : Herm H n, IntegralOn X l ∧ TotPos l ∧ t = pairing l B}

def PhiClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (X : Submodule (𝓞 H.E) (V H n)),
  IsLattice X → Function.Bijective (restrict X) ∧
    ∀ B : Bal H n, IsPSDRat X B → IsLeast (phiValues X B) (phiC X B)

def realPair (ξ : V H n) (u : XR R n) : ℝ := ∑ τ, 2 * (toR H n ξ τ ⬝ᵥ u τ).re

def dualQuot (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) : Set (V H n) :=
  {ξ | ξ ∈ dualZ X ∧ ∀ u ∈ kerR B, realPair ξ u = 0}

def IsDualNormSq (B : Bal H n) (ξ : V H n) (s : ℝ) : Prop :=
  IsLeast {t : ℝ | 0 ≤ t ∧ ∀ u, realPair ξ u ^ 2 ≤ t * Q B u} s

def IsLaMax (X : Submodule (𝓞 H.E) (V H n)) (B : Bal H n) (l : ℝ) : Prop :=
  IsLeast {r : ℝ | 0 ≤ r ∧
    Submodule.span ℝ {u | (∃ x ∈ X, u = toR H n x) ∧ Q B u ≤ r ^ 2} ⊔ kerR B = ⊤} l

def MinimaClaim : Prop := ∀ (R : Ranks) (H : Host R) (n : ℕ) (X : Submodule (𝓞 H.E) (V H n)),
  IsLattice X → ∀ B : Bal H n, IsPSDRat X B → B ≠ 0 →
    (∃ l, IsLaMax X B l) ∧ (∀ ξ ∈ dualQuot X B, ∃ s, IsDualNormSq B ξ s) ∧
    (∀ l, IsLaMax X B l → ∃ ξ ∈ dualQuot X B, ξ ≠ 0 ∧
      ∀ s, IsDualNormSq B ξ s → s * l ^ 2 ≤ ((2 * R.f * n : ℕ) : ℝ) ^ 2) ∧
    (∀ χ : Herm H n, TotNonneg χ → ∀ ξ ∈ dualQuot X B, ∀ s, IsDualNormSq B ξ s →
      4 * ((trVal χ ξ : ℚ) : ℝ) ≤ pairing χ B * s) ∧
    ∀ l, IsLaMax X B l → phiC X B ≤ n * l ^ 2

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

def cOne (D : D7) (j : Lift D.R) (T : ℕ) (c : ℝ) : ℝ :=
  RR D * T * c * (dPrime j : ℝ) ^ 2 * (rho j : ℝ) / 2

def qMin (D : D7) : ℕ := min (D.host.g 0) (D.host.g 1)

def cOf (D : D7) {j : Lift D.R} (P : ℝ) (wL : ThetaWeight D j) : ℝ :=
  RR D * P * (wL.DF : ℝ) ^ 2 / (qMin D : ℝ)

def cRecord {D : D7} (L : SizeData₂ D) (CP : ℝ) {j : Lift D.R} (wL : ThetaWeight D j) : ℝ :=
  cOf D (PP L CP 12) wL

def pThirteen (D : D7) (nW : ℕ) : ℝ :=
  max (16200 * Real.pi * nW * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * D.R.m) ^ 4)
    (max ((2 * (D.R.f : ℝ) * D.R.m) ^ 4 * nW + 2 * (2 * (D.R.f : ℝ) * D.R.m) ^ 3)
      ((D.R.r : ℝ) * (2 * (D.R.f : ℝ) * D.R.m) ^ 3))

def AdmissibleC (D : D7) {j : Lift D.R} (wL : ThetaWeight D j) (T : ℕ) (c : ℝ) : Prop :=
  cOf D (pThirteen D wL.n) wL ≤ c ∧ T * c * (2 * 5 ^ 4 * (D.R.r : ℝ)) ≤ 1 ∧
    (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * RR D ^ 2 * c ≤ 1 / 2

def COneBoundClaim : Prop := ∀ (D : D7) (L : SizeData₂ D) (j : Lift D.R) (T : ℕ) (c : ℝ), 0 ≤ c →
  (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * RR D ^ 2 * c ≤ 1 / 2 →
    cOne D j T c ≤ D.R.f * T / RR D ∧
    ((T : ℝ) ≤ L.sc.b → (D.R.f : ℝ) * T / RR D ≤ D.R.f * L.sc.b ∧
      (Real.log (D.R.f : ℝ) ≤ L.sc.L → 0 < cOne D j T c → Real.log (cOne D j T c) ≤ 2 * L.sc.L))

def shallowExponents (D : D7) (j : Lift D.R) (T : ℕ) (c : ℝ)
    (X : Submodule (𝓞 D.host.E) (V D.host (rho j))) : Set (Herm D.host (rho j)) :=
  {χ | χ ∈ cuspExponents X ∧ IsShallow X (cOne D j T c) χ}

def DeepPairingClaim : Prop := ∀ (D : D7) (j : Lift D.R) (T : ℕ) (c : ℝ), 0 ≤ c →
  ∀ X : Submodule (𝓞 D.host.E) (V D.host (rho j)), IsLattice X →
  ∀ χ ∈ expNonneg X, ¬ IsShallow X (cOne D j T c) χ →
  ∀ B : Bal D.host (rho j), IsPSDRat X B → B ≠ 0 → T * c * phiC X B < pairing χ B

example (H : Host R) :
    IsPD (ofHerm H (n := n) (fun _ => 1) fun _ => Matrix.isHermitian_one) := by
  classical
  intro u hu
  have h : bil (ofHerm H (n := n) (fun _ => 1) fun _ => Matrix.isHermitian_one) u u =
      ∑ τ, ∑ i, 2 * Complex.normSq (u τ i) := by
    simp only [bil, ofHerm, trBil, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Matrix.one_apply_ne hk.symm]) (by simp)]
    simp [Complex.normSq_apply]
  rw [h]
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hτ
  refine Finset.sum_pos' (fun τ _ => Finset.sum_nonneg fun i _ => by
    have := Complex.normSq_nonneg (u τ i); positivity) ⟨τ, Finset.mem_univ _, ?_⟩
  refine Finset.sum_pos' (fun i _ => by have := Complex.normSq_nonneg (u τ i); positivity)
    ⟨i, Finset.mem_univ _, ?_⟩
  have := Complex.normSq_pos.2 hi
  positivity

example (x : V H n) : symForm x x = 2 • sqForm x := by
  apply Subtype.ext; ext i k; simp [symForm, sqForm, two_mul]

end GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

end
