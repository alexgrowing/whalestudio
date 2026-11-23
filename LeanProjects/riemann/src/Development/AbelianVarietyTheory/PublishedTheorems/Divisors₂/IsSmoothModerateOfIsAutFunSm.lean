import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal ENNReal ContDiff

namespace GlobalTheory.SiegelSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure IsWittFrame (X Y : Matrix (Fin n) (Fin r) E) : Prop where
  xx : cT (σ : E →+* E) X * J * X = 0
  yy : cT (σ : E →+* E) Y * J * Y = 0
  xy : cT (σ : E →+* E) X * J * Y = 1
  aniso : ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    hE σ J z z = 0 → z = 0

variable (F) in

abbrev adMat {m m' : Type} (X : Matrix m m' E) : Matrix m m' (AF F ⊗[F] E) := X.map (inclR (F := F) (AF F))

def minParOne (X : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {p | ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular id ∧
    (matHom _ σ J p).1 * adMat F X = adMat F X * B ∧ ∀ i, ∃ u : (AF F ⊗[F] E)ˣ, B i i = u ∧ absE F E u = 1}

def IsTorusElt (X Y : Matrix (Fin n) (Fin r) E) (t : Fin r → ℝ) (a : GAd σ J) : Prop :=
  a ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w),
    archMat σ J τ (projArch σ J w a) * X.map τ.1 = X.map τ.1 * diagonal (fun i => (t i : ℂ)) ∧
    archMat σ J τ (projArch σ J w a) * Y.map τ.1 = Y.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) ∧
    ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      archMat σ J τ (projArch σ J w a) *ᵥ (fun i => τ.1 (z i)) = fun i => τ.1 (z i)

variable (r) in

def cone (c : ℝ) : Set (Fin r → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ (∀ i j : Fin r, j.val = i.val + 1 → c * t j ≤ t i) ∧ ∀ i : Fin r, i.val + 1 = r → c ≤ t i}

def siegelSet (X Y : Matrix (Fin n) (Fin r) E) (Ω : Set (GAd σ J)) (c : ℝ) (K : Subgroup (GAd σ J)) : Set (GAd σ J) :=
  {g | ∃ p ∈ Ω, ∃ t ∈ cone r c, ∃ a, IsTorusElt σ J X Y t a ∧ ∃ k ∈ K, g = p * a * k}

variable (F n) in

def modulus (t : Fin r → ℝ) : ℝ := ∏ i : Fin r, t i ^ (2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1))

def IsRealLine (γ : ℝ → GAd σ J) : Prop :=
  ∃ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ), Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 ∧
    ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ archMat σ J τ y = NormedSpace.exp (t • Z)

variable {σ J} in

def lineDer (γ : ℝ → GAd σ J) (φ : GAd σ J → ℂ) : GAd σ J → ℂ := fun g => deriv (fun t => φ (g * γ t)) 0

def unipRad (C : Matrix (Fin n) (Fin r) E) : Subgroup (GAd σ J) :=
  Subgroup.closure {g | let m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 - 1
    m * adMat F C = 0 ∧ adMat F (cT (σ : E →+* E) C * J) * m = 0 ∧
    ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 →
      ∃ a : Fin r → AF F ⊗[F] E, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F C *ᵥ a}

def IsCuspidal (φ : GAd σ J → ℂ) : Prop :=
  ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E),
    (0 < r ∧ LinearIndependent E C.transpose ∧ cT (σ : E →+* E) C * J * C = 0) →
    ∀ (μ : Measure (unipRad σ J C)) (𝓕 : Set (unipRad σ J C)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J C)) 𝓕 μ →
      ∀ g, ∫ u in 𝓕, φ ((u : GAd σ J) * g) ∂μ = 0

structure IsSmoothModerate (φ : GAd σ J → ℂ) : Prop where
  left : ∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod)
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ N

end GlobalTheory.SiegelSet

namespace GlobalTheory.Published

open GlobalTheory.SiegelSet in

def SiegelSetUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∃ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ),
          IsCompact (K : Set (GAd σ J)) ∧ IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧
          (∀ g, ∃ p ∈ minParOne σ J X, ∃ t a, (∀ i, 0 < t i) ∧ IsTorusElt σ J X Y t a ∧ ∃ k ∈ K, g = p * a * k) ∧
          IsClosed (siegelSet σ J X Y Ω c K) ∧
          (∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s) ∧
          (∃ C : Set (GAd σ J), IsCompact C ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → a⁻¹ * p * a ∈ C) ∧
          (∀ μ : Measure (GAd σ J), μ.IsHaarMeasure → μ (siegelSet σ J X Y Ω c K) < ⊤ ∧
            ∃ C : ℝ≥0, ∀ (f : GAd σ J → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
              (∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, f (p * a * k) ≤ h t) →
              ∫⁻ g in siegelSet σ J X Y Ω c K, f g ∂μ ≤
                C * ∫⁻ t in cone r c, h t * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹)) ∧
          (∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J,
            height σ J g ≤ C * height σ J (γ * g) ^ A) ∧
          ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ →
            ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C

end GlobalTheory.Published

namespace GlobalTheory.SiegelSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField F] [NumberField E] in
theorem gram_apply {s : ℕ} (X : Matrix (Fin n) (Fin r) E) (Y : Matrix (Fin n) (Fin s) E) (i : Fin r) (j : Fin s) :
    (cT (σ : E →+* E) X * J * Y) i j = toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J (Xᵀ i) (Yᵀ j) := by
  simp only [toLinearMapₛₗ₂'_apply, Matrix.mul_apply, cT, Finset.sum_mul, transpose_apply, map_apply, smul_eq_mul,
    RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem gram_mulVec (X : Matrix (Fin n) (Fin r) E) (z : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) X * J) *ᵥ z) i = toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J (Xᵀ i) z :=
  gram_apply (s := 1) X (of fun a _ => z a) i 0

theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_cons {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V] {s : E →+* E}
    (B : V →ₛₗ[s] V →ₗ[E] E) (hs : ∀ u v, B u v = s (B v u)) {x y : Fin r → V} (hx : ∀ i j, B (x i) (x j) = 0)
    (hy : ∀ i j, B (y i) (y j) = 0) (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0) {z w₀ : V}
    (hxz : ∀ i, B (x i) z = 0) (hyz : ∀ i, B (y i) z = 0) (hzz : B z z = 0) (hw₀ : B z w₀ = 1) :
    ∃ x y : Fin (r + 1) → V, (∀ i j, B (x i) (x j) = 0) ∧ (∀ i j, B (y i) (y j) = 0) ∧
      ∀ i j, B (x i) (y j) = if i = j then 1 else 0 := by
  have hzx : ∀ i, B z (x i) = 0 := fun i => by rw [hs, hxz, map_zero]
  have hzy : ∀ i, B z (y i) = 0 := fun i => by rw [hs, hyz, map_zero]
  have hyx : ∀ i j, B (y i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [hs, hxy]; simp [apply_ite s, eq_comm]
  obtain ⟨w₁, a1, a2, a3⟩ : ∃ w, (∀ i, B (x i) w = 0) ∧ (∀ i, B (y i) w = 0) ∧ B z w = 1 :=
    ⟨w₀ - ∑ j, B (y j) w₀ • x j - ∑ j, B (x j) w₀ • y j, fun i => by simp [hx, hxy], fun i => by simp [hy, hyx],
      by simp [hzx, hzy, hw₀]⟩
  obtain ⟨w, b1, b2, b3, b4⟩ : ∃ w, (∀ i, B (x i) w = 0) ∧ (∀ i, B (y i) w = 0) ∧ B z w = 1 ∧ B w w = 0 := by
    refine ⟨w₁ - (B w₁ w₁ / 2) • z, fun i => by simp [a1, hxz], fun i => by simp [a2, hyz], by simp [a3, hzz], ?_⟩
    have c1 : B w₁ z = 1 := by rw [hs, a3, map_one]
    have c2 : s (B w₁ w₁) = B w₁ w₁ := (hs _ _).symm
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, c1, a3,
      hzz, map_div₀, c2, map_ofNat]
    ring
  have hwy : ∀ i, B w (y i) = 0 := fun i => by rw [hs, b2, map_zero]
  refine ⟨Fin.cons z x, Fin.cons w y, ?_, ?_, ?_⟩ <;> intro i j <;> refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [hzz, hzx, hxz, hx, b4, hwy, b2, hy, b3, hzy, b1, hxy, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem exists_isWittFrame (h : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y := by
  classical
  let B := toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J
  have hB : ∀ u v, B u v = ∑ i, ∑ j, σ (u i) * J i j * v j := fun u v => by
    simp only [B, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hs : ∀ u v, B u v = (σ : E →+* E) (B v u) := fun u v => by
    simp only [hB, map_sum, map_mul, RingHom.coe_coe, sigma_sigma h, hJ.1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  let P : ℕ → Prop := fun r => ∃ x y : Fin r → Fin n → E, (∀ i j, B (x i) (x j) = 0) ∧ (∀ i j, B (y i) (y j) = 0) ∧
    ∀ i j, B (x i) (y j) = if i = j then 1 else 0
  have hle : ∀ r, P r → r ≤ n := by
    rintro r ⟨x, y, -, -, e⟩
    have e1 : cT (σ : E →+* E) (of x)ᵀ * J * (of y)ᵀ = 1 := Matrix.ext fun i j => (gram_apply _ _ i j).trans (e i j)
    have e2 := congrArg Matrix.rank e1
    rw [Matrix.rank_one, Fintype.card_fin] at e2
    exact e2.symm.le.trans ((Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height _))
  obtain ⟨r, ⟨x, y, hx, hy, hxy⟩, hr⟩ : ∃ r, P r ∧ ¬ P (r + 1) := ⟨Nat.findGreatest P n,
    Nat.findGreatest_spec (Nat.zero_le n) ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
    fun hP => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hle _ hP) hP⟩
  refine ⟨r, (of x)ᵀ, (of y)ᵀ, Matrix.ext fun i j => (gram_apply _ _ i j).trans (hx i j),
    Matrix.ext fun i j => (gram_apply _ _ i j).trans (hy i j),
    Matrix.ext fun i j => (gram_apply _ _ i j).trans (hxy i j), fun z h1 h2 h3 => ?_⟩
  by_contra hz
  obtain ⟨w₀, hw₀⟩ : ∃ w, B z w = 1 := by
    have h4 : (fun i => σ (z i)) ᵥ* J ≠ 0 := fun e => hz (funext fun i => (σ : E →+* E).injective
      ((congrFun (Matrix.eq_zero_of_vecMul_eq_zero hJ.2 e) i).trans (map_zero σ).symm))
    obtain ⟨b, hb⟩ := Function.ne_iff.1 h4
    have h5 : B z (Pi.single b 1) = ((fun i => σ (z i)) ᵥ* J) b := by
      simp [hB, Pi.single_apply, vecMul, dotProduct]
    exact ⟨(((fun i => σ (z i)) ᵥ* J) b)⁻¹ • Pi.single b 1, by rw [map_smul, h5, smul_eq_mul, inv_mul_cancel₀ hb]⟩
  exact hr (exists_cons B hs hx hy hxy (fun i => (gram_mulVec (of x)ᵀ z i).symm.trans (congrFun h1 i))
    (fun i => (gram_mulVec (of y)ᵀ z i).symm.trans (congrFun h2 i)) ((hB z z).trans h3) hw₀)

omit [NumberField F] [NumberField E] in

theorem isWittFrame_plane : IsWittFrame σ !![0, 1; 1, 0] (!![1; 0] : Matrix (Fin 2) (Fin 1) E) !![0; 1] := by
  refine ⟨?_, ?_, ?_, fun z h1 h2 _ => ?_⟩
  · ext i j; simp [cT, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; simp [cT, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; simp [cT, Matrix.mul_apply, Fin.sum_univ_two, Subsingleton.elim i j, Matrix.one_apply]
  · have e1 := congrFun h1 0
    have e2 := congrFun h2 0
    simp [cT, Matrix.mul_apply, Fin.sum_univ_two, mulVec, dotProduct] at e1 e2
    funext i; fin_cases i <;> simp [e1, e2]

theorem exists_unit_torus {A : Type} [CommRing A] {s : A →+* A} (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hJ : cT s J = J) {X Y : Matrix (Fin n) (Fin r) A} (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0)
    (xy : cT s X * J * Y = 1) (d : Fin r → Aˣ) (hd : ∀ i, s (d i) = d i) :
    ∃ m ∈ Formalism.UG.UJ s J, m.1 * X = X * diagonal (fun i => (d i).1) ∧ m.1 * Y = Y * diagonal (fun i => (d i)⁻¹.1) ∧
      m.1 = 1 + X * diagonal (fun i => (d i).1 - 1) * (cT s Y * J) + Y * diagonal (fun i => (d i)⁻¹.1 - 1) * (cT s X * J) := by
  have cc : ∀ Z : Matrix (Fin n) (Fin r) A, cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have yx : cT s Y * J * X = 1 := by
    have := congrArg (cT s) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  let M : (Fin r → Aˣ) → Matrix (Fin n) (Fin n) A := fun d =>
    1 + X * diagonal (fun i => (d i).1 - 1) * (cT s Y * J) + Y * diagonal (fun i => (d i)⁻¹.1 - 1) * (cT s X * J)
  have e : ∀ a : Fin r → A, diagonal (fun i => a i - 1) = diagonal a - 1 := fun a => by
    rw [← diagonal_one, diagonal_sub]
  have hX : ∀ d, M d * X = X * diagonal fun i => (d i).1 := fun d => by
    simp only [M, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), xx, yx, e,
      Matrix.mul_sub]
    simp
  have hY : ∀ d, M d * Y = Y * diagonal fun i => (d i)⁻¹.1 := fun d => by
    simp only [M, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), yy, xy, e,
      Matrix.mul_sub]
    simp
  have hM : ∀ d, M d * M d⁻¹ = 1 := fun d => by
    conv_lhs => rw [show M d⁻¹ = 1 + _ + _ from rfl, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
    simp only [← Matrix.mul_assoc (M d), hX, hY, Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal]
    simp only [M, Pi.inv_apply, inv_inv, mul_sub, Units.mul_inv, Units.inv_mul, mul_one, ← diagonal_sub, diagonal_one,
      Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hd' : ∀ i, s (d i)⁻¹.1 = (d i)⁻¹.1 := fun i =>
    (Units.inv_eq_of_mul_eq_one_right (by rw [← hd i, ← map_mul, Units.mul_inv, map_one])).symm
  have cd : ∀ a : Fin r → A, (∀ i, s (a i) = a i) → cT s (diagonal fun i => a i - 1) = diagonal fun i => a i - 1 :=
    fun a ha => by ext i j; by_cases h : i = j <;> simp [cT, diagonal, h, ha, eq_comm]
  have ca : ∀ P Q : Matrix (Fin n) (Fin n) A, cT s (P + Q) = cT s P + cT s Q := fun P Q =>
    Matrix.ext fun i j => map_add s _ _
  have hU : cT s (M d) * J = J * M d⁻¹ := by
    simp only [M, ca, Formalism.UG.cT_mul, Formalism.UG.cT_one, cc, hJ, cd _ hd, cd _ hd', Pi.inv_apply, inv_inv, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    abel
  have hM' : M d⁻¹ * M d = 1 := by simpa only [inv_inv] using hM d⁻¹
  exact ⟨⟨M d, M d⁻¹, hM d, hM'⟩, show cT s (M d) * J * M d = J by rw [hU, Matrix.mul_assoc, hM', Matrix.mul_one],
    hX d, hY d, rfl⟩

theorem exists_isTorusElt (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ} (ht : ∀ i, t i ≠ 0) : ∃ a, IsTorusElt σ J X Y t a := by
  have := h.1
  let ρ : ℝ →* AF F :=
    { toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
        Ainf F), (1 : Af F))
      map_one' := Prod.ext (funext fun w => map_one _) rfl
      map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }
  let ι : AF F →* AF F ⊗[F] E := (Algebra.TensorProduct.includeLeftRingHom : AF F →+* AF F ⊗[F] E)
  let d : Fin r → (AF F ⊗[F] E)ˣ := fun i => Units.map (ι.comp ρ) (Units.mk0 (t i) (ht i))
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
      adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c1]; simp only [adMat, JR, Matrix.map_mul]
  obtain ⟨m, hm, hX, hY, he⟩ := exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X) (Y := adMat F Y)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    ((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))
    ((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) d
    (fun i => congrArg (ρ (t i) ⊗ₜ[F] ·) (map_one σ))
  refine ⟨⟨m, hm⟩, Units.ext (Matrix.ext fun i j => ?_), fun w τ => ?_⟩
  · let ψ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    have h1 : ∀ k, ψ (d k).1 = 1 := fun k => rfl
    have h2 : ∀ k, ψ (d k)⁻¹.1 = 1 := fun k => rfl
    change ψ (m.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [he]
    simp only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add, map_sum, map_mul, map_sub, h1,
      h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ, map_zero]
  · let φ := (infEmb τ).comp (compInf F E w)
    have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
    have h1 : ∀ x : ℝ, φ (ι (ρ x)) = x := fun x => by
      change infEmb τ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x ⊗ₜ[F] 1) = _
      rw [infEmb_tmul, map_one, mul_one,
        ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
      exact congrArg _ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply x)
    have h2 : ∀ Z : Matrix (Fin n) (Fin r) E, (adMat F Z).map φ = Z.map τ.1 := fun Z => Matrix.ext fun i j => h0 _
    have h3 : archMat σ J τ (projArch σ J w ⟨m, hm⟩) = m.1.map φ := rfl
    rw [h3]
    refine ⟨?_, ?_, fun z hz hz' => ?_⟩
    · rw [← h2, ← Matrix.map_mul, hX, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => h1 _)
    · rw [← h2, ← Matrix.map_mul, hY, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => (h1 (t i)⁻¹).trans (Complex.ofReal_inv _))
    · have h4 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (σ : E →+* E) Z * J) *ᵥ z = 0 →
          (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ (inclR (F := F) (AF F) ∘ z) = 0 := fun Z hZ => funext fun i => by
        have e : (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) =
          (cT (σ : E →+* E) Z * J).map (inclR (F := F) (AF F)) := by
          rw [c1, Matrix.map_mul]; rfl
        rw [e, ← RingHom.map_mulVec, hZ]; exact map_zero _
      have h5 : m.1 *ᵥ (inclR (F := F) (AF F) ∘ z) = inclR (F := F) (AF F) ∘ z := by
        rw [he, add_mulVec, add_mulVec, ← mulVec_mulVec, h4 Y hz', mulVec_zero, ← mulVec_mulVec, h4 X hz]
        simp
      funext i
      rw [show (fun i => τ.1 (z i)) = φ ∘ inclR (F := F) (AF F) ∘ z from funext fun i => (h0 _).symm,
        ← RingHom.map_mulVec, h5]
      exact h0 _

theorem exists_isRealLine (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0) :
    ∃ γ, IsRealLine σ J γ ∧ ∀ t : ℝ, archMat σ J τ (projArch σ J w (γ t)) = NormedSpace.exp (t • Z) := by
  have hd : IsUnit (J.map τ.1).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hy : ∀ t : ℝ, ∃ y : GArch σ J w, archMat σ J τ y = NormedSpace.exp (t • Z) := fun t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z) hd (by
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy
  exact ⟨fun t => embArch σ J w (y t), ⟨w, τ, Z, hZ, fun t => ⟨y t, rfl, hy t⟩⟩, fun t => by
    rw [projArch_embArch_self, hy]⟩

variable (σ J) in

theorem isSmoothModerate_const (c : ℂ) : IsSmoothModerate σ J fun _ => c := by
  refine ⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const, fun _ _ _ _ => contDiff_const, 0,
    fun l _ => ⟨‖c‖, fun g => ?_⟩⟩
  have : ∀ l : List (ℝ → GAd σ J), ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ l.foldr lineDer (fun _ => c) = fun _ => c' := fun l => by
    induction l with
    | nil => exact ⟨c, le_rfl, rfl⟩
    | cons γ l ih =>
      obtain ⟨c', -, h⟩ := ih
      exact ⟨0, by simp, by rw [List.foldr_cons, h]; funext g; simp [lineDer]⟩
  obtain ⟨c', h, e⟩ := this l
  simpa [e] using h

example (t : Fin 1 → ℝ) : modulus F 2 t = t 0 ^ (2 * Module.finrank ℚ F) := by
  simp [modulus, ← zpow_natCast]

example {c : ℝ} (h1 : c ≤ 1) : (fun _ => 1) ∈ cone r c := ⟨fun _ => one_pos, fun _ _ _ => by simpa, fun _ _ => h1⟩

theorem exists_isCompact_projFin {X Y : Matrix (Fin n) (Fin r) E} {Ω : Set (GAd σ J)} (hΩ : IsCompact Ω) (c : ℝ)
    {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J))) :
    ∃ C : Set (GFin σ J), IsCompact C ∧ ∀ s ∈ siegelSet σ J X Y Ω c K, projFin σ J s ∈ C := by
  refine ⟨_, (hΩ.mul hK).image (continuous_projFin σ J), ?_⟩
  rintro _ ⟨p, hp, t, -, a, ha, k, hk, rfl⟩
  exact ⟨p * k, ⟨p, hp, k, hk, rfl⟩, by simp only [map_mul, mem_infPts.1 ha.1, mul_one]⟩

theorem exists_cover (hP : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ S : Set (GAd σ J), IsClosed S ∧ (∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ S, g = γ * s) ∧
      (∃ C : Set (GFin σ J), IsCompact C ∧ ∀ s ∈ S, projFin σ J s ∈ C) ∧
      (∀ μ : Measure (GAd σ J), μ.IsHaarMeasure → μ S < ⊤) ∧
      ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ → ∀ N : ℕ,
        (∃ C : ℝ, ∀ g ∈ S, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C) ∧
        ∀ μ : Measure (GAd σ J), μ.IsHaarMeasure → IntegrableOn (fun g => ‖φ g‖ * (height σ J g : ℝ) ^ N) S μ := by
  obtain ⟨r, X, Y, hW⟩ := exists_isWittFrame h hJ
  obtain ⟨K, Ω, c, hK, hΩ, -, -, -, hcl, hcov, -, hμ, -, hφ⟩ := hP F E σ h n J hJ r X Y hW
  refine ⟨_, hcl, hcov, exists_isCompact_projFin hΩ c hK, fun μ h => (hμ μ h).1, fun φ h1 h2 N =>
    ⟨hφ φ h1 h2 N, fun μ h => ?_⟩⟩
  obtain ⟨C, hC⟩ := hφ φ h1 h2 N
  have hc : Continuous fun g => ‖φ g‖ * (height σ J g : ℝ) ^ N :=
    h1.cont.norm.mul ((NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)).pow N)
  refine Measure.integrableOn_of_bounded (M := C) (hμ μ h).1.ne hc.aestronglyMeasurable
    ((ae_restrict_iff' hcl.measurableSet).2 (.of_forall fun g hg => ?_))
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC g hg

omit [NumberField E] in

theorem ug_eq_hr (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) :
    GlobalTheory.WeilM.UG (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ) (adMat F J) = HR (AF F) σ (c • J.map σ) := by
  let s := sigR (AF F) σ
  have hs : ∀ a, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
  have hu : IsUnit (inclR (F := F) (AF F) c) := (IsUnit.mk0 c hc).map _
  have e : JR (F := F) (AF F) (c • J.map σ) = inclR (F := F) (AF F) c • (adMat F J).map s :=
    Matrix.ext fun i j => map_mul (inclR (F := F) (AF F)) c (σ (J i j))
  ext g
  change g.1ᵀ * adMat F J * g.1.map s = adMat F J ↔ cT s g.1 * JR (F := F) (AF F) _ * g.1 = JR (F := F) (AF F) _
  have e2 : (g.1ᵀ * adMat F J * g.1.map s).map s = cT s g.1 * (adMat F J).map s * g.1 := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    exact Matrix.ext fun i j => hs _
  rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel, ← e2]
  exact (Matrix.map_injective (Function.LeftInverse.injective hs)).eq_iff.symm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem conj_exp (Z : Matrix (Fin n) (Fin n) ℂ) :
    (starRingEnd ℂ).mapMatrix (NormedSpace.exp Z) = NormedSpace.exp ((starRingEnd ℂ).mapMatrix Z) :=
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  NormedSpace.map_exp _ (continuous_id.matrix_map Complex.continuous_conj) Z

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {φ : GA D V → ℂ}

theorem IsRealLine.eq_oneP (hθ : IsInfFam θ) {γ : ℝ → GA D V} (h : IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ, p.2 ∈ lieAt V p.1 ∧ γ = oneP θ V p.1 p.2 := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := h
  obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
  have key : ∀ Z', (∀ (t : ℝ) y, archMat _ _ τ y = NormedSpace.exp (t • Z) →
      archMat _ V.gram (embOverOf D ρ) y = NormedSpace.exp (t • Z')) → γ = oneP θ V ρ Z' := fun Z' hZ' => funext fun t => by
    obtain ⟨y, e1, e2⟩ := hγ t
    rw [e1, oneP, ← hZ' t y e2, GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), atTau_archEquiv hθ V _ rfl]
  have h0 : ∀ (τ : EmbOver D.host.E (placeOf D ρ)) x, infEmb τ (1 ⊗ₜ[D.host.F] x) = τ.1 x := fun τ x => by simp
  rcases infEmb_eq_or_conj (isCMExt_host D) τ (embOverOf D ρ) with e | e
  · refine ⟨(ρ, Z), ?_, key Z fun t y hy => by rw [← hy, GlobalTheory.Orb.archMat_apply, e]; rfl⟩
    have : gramAt D V ρ = V.gram.map τ.1 :=
      Matrix.ext fun i j => (h0 (embOverOf D ρ) _).symm.trans (by rw [e, h0]; rfl)
    exact show _ * _ + _ * _ = _ from this ▸ hZ
  · let c := (starRingEnd ℂ).mapMatrix (m := Fin V.rank)
    refine ⟨(ρ, c Z), ?_, key (c Z) fun t y hy => ?_⟩
    · have : gramAt D V ρ = c (V.gram.map τ.1) :=
        Matrix.ext fun i j => (h0 (embOverOf D ρ) _).symm.trans (by rw [e, RingHom.comp_apply, h0]; rfl)
      change (c Z)ᴴ * _ + _ * c Z = 0
      rw [this, show (c Z)ᴴ = c Zᴴ from rfl, ← map_mul, ← map_mul, ← map_add, hZ, map_zero]
    · rw [show t • c Z = c (t • Z) from Matrix.ext fun i j => by simp [c],
        ← conj_exp, ← hy, GlobalTheory.Orb.archMat_apply, e]
      rfl

theorem isSmoothModerate_of_isAutFunSm (hθ : IsInfFam θ) (h : IsAutFunSm θ V φ) :
    IsSmoothModerate D.sp.cm.sig V.gram φ := by
  refine ⟨h.left, h.level, h.cont, fun k γ hγ g => ?_, ?_⟩
  · choose p hp e using fun i => (hγ i).eq_oneP hθ
    simpa only [e] using h.smooth k (fun i => (p i).1) (fun i => (p i).2) hp g
  · obtain ⟨N, hN⟩ := GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ h
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨l', h1, h2⟩ : ∃ l' : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l', p.2 ∈ lieAt V p.1) ∧
        l.foldr lineDer φ = l'.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
      induction l with
      | nil => exact ⟨[], by simp, rfl⟩
      | cons γ l ih =>
        obtain ⟨l', h1, h2⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
        obtain ⟨p, hp, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
        exact ⟨p :: l', List.forall_mem_cons.2 ⟨hp, h1⟩, by rw [List.foldr_cons, h2]; rfl⟩
    exact h2 ▸ hN l' h1

example (D : D7) : ¬ IsCuspidal D.sp.cm.sig (GlobalTheory.CuspDecay.Model.plane D).gram fun _ => 1 :=
  GlobalTheory.CuspDecay.Model.not_isCuspFun_one_plane D

end Record

end GlobalTheory.SiegelSet

end
