import Mathlib
import Formalism.RealPlaceAnalysis.StatementA

noncomputable section

open scoped ContDiff Topology
open NumberField Matrix

namespace GlobalTheory.SmoothForms

section Chart

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]

structure IsLieData (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) : Prop where
  anti : ∀ a b, σ (a * b) = σ b * σ a
  one : σ 1 = 1
  invol : ∀ a, σ (σ a) = a
  inj : Function.Injective j
  skew : ∀ X, σ X = -X ↔ ∃ Y, j Y = X
  mul : ∀ a b, σ a * a = 1 → σ b * b = 1 → s (a * b) = s a * s b

def expMap (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (X : L) : G := s (NormedSpace.exp (j X))

def HasLog (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) : Prop :=
  ∃ Λ : 𝔸 → L, ContDiffAt ℝ ∞ Λ 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → NormedSpace.exp (j (Λ h)) = h) ∧
    ∀ᶠ X in 𝓝 (0 : L), Λ (NormedSpace.exp (j X)) = X

def Sm (e : L → G) (φ : G → ℂ) : Prop := ∀ g, ContDiff ℝ ∞ fun X : L => φ (g * e X)

def Der (e : L → G) (X : L) (φ : G → ℂ) : G → ℂ := fun g => deriv (fun t : ℝ => φ (g * e (t • X))) 0

open scoped ContDiff Topology in
open NumberField Matrix in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] in

theorem _root_.GlobalTheory.SmoothForms.contDiff_family [FiniteDimensional ℝ 𝔸] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸}
    {s : 𝔸 → G} (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) {φ : G → ℂ}
    (hφ : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * _root_.GlobalTheory.SmoothForms.expMap j s X)) 0)
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {c : P → 𝔸} (hc : ContDiff ℝ ∞ c)
    (hu : ∀ p, σ (c p) * c p = 1) (g : G) : ContDiff ℝ ∞ fun p => φ (g * s (c p)) := by
  have hmul := H.mul
  have anti := H.anti
  have invol := H.invol
  simp only [_root_.GlobalTheory.SmoothForms.expMap] at hφ
  haveI : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
  obtain ⟨Λ, hΛ, hexp, hlog⟩ := hl
  have hΛ0 : Λ 1 = 0 := by
    simpa using hlog.self_of_nhds
  rw [contDiff_iff_contDiffAt]
  intro p₀
  set u := c p₀
  have hu' : u * σ u = 1 := mul_eq_one_comm.mp (hu p₀)
  let k : P → 𝔸 := fun p => σ u * c p
  have hk : ContDiff ℝ ∞ k := contDiff_const.mul hc
  have hk0 : k p₀ = 1 := hu p₀
  have hku : ∀ p, σ (k p) * k p = 1 := by
    intro p
    simp only [k, anti, invol]
    calc σ (c p) * u * (σ u * c p) = σ (c p) * (u * σ u) * c p := by noncomm_ring
      _ = 1 := by rw [hu', mul_one, hu p]
  have hck : ∀ p, c p = u * k p := by
    intro p
    simp only [k]
    rw [← mul_assoc, hu', one_mul]
  have hev : ∀ᶠ p in 𝓝 p₀, NormedSpace.exp (j (Λ (k p))) = k p := by
    have := hk.continuous.continuousAt (x := p₀)
    rw [ContinuousAt, hk0] at this
    exact (this.eventually hexp).mono fun p hp => hp (hku p)
  have hF : ContDiffAt ℝ ∞ (fun p => φ ((g * s u) * s (NormedSpace.exp (j (Λ (k p)))))) p₀ := by
    have h1 : ContDiffAt ℝ ∞ (fun p => Λ (k p)) p₀ := by
      have : ContDiffAt ℝ ∞ Λ (k p₀) := by rw [hk0]; exact hΛ
      exact this.comp p₀ hk.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun X : L => φ ((g * s u) * s (NormedSpace.exp (j X)))) (Λ (k p₀)) := by
      rw [hk0, hΛ0]; exact hφ _
    exact ContDiffAt.comp (g := fun X : L => φ ((g * s u) * s (NormedSpace.exp (j X)))) p₀ h2 h1
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  rw [hp, hck p, hmul _ _ (hu p₀) (hku p), mul_assoc]

end Chart

section Words

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def gelfA (E : Fin n → Fin n → A) (k : ℕ) : A :=
  ∑ idx : Fin (k + 1) → Fin n, (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).prod

def wordMap (E : Fin n → Fin n → A) (d : ℕ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ →ₗ[ℂ] A where
  toFun M := ∑ I, ∑ K, M I K • (List.ofFn fun a : Fin d => E (I a) (K a)).prod
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, mul_smul]

def filt (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ A := ⨆ d' < d, LinearMap.range (wordMap E d')

def polar (n d : ℕ) (a b : Fin n) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∑ p, if I p = a ∧ K p = b ∧ ∀ q, q ≠ p → I q = K q then 1 else 0

def permMat (n d : ℕ) (π : Equiv.Perm (Fin d)) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => if I = K ∘ π then 1 else 0

end Words

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Sized {V : Type} [AddCommGroup V] [Module E V] (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ)
    (ν : V → ℝ) (B : ℝ) : Prop where
  symm : ∀ x y, h y x = star (h x y)
  nondeg : ∀ y, (∀ x, h y x = 0) → y = 0
  fg : Λ.FG
  stable : ∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ
  int : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)
  dual : ∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ
  two_le : 2 ≤ B
  nonneg : ∀ x, 0 ≤ ν x
  add_le : ∀ x y, ν (x + y) ≤ ν x + ν y
  smul_le : ∀ (a : E) x, ν (a • x) ≤ house a * ν x
  form_le : ∀ x y, house (h x y) ≤ ν x * ν y
  span : Submodule.span E {x | x ∈ Λ ∧ ν x ≤ B} = ⊤

open scoped ContDiff Topology in
open NumberField Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.SmoothForms.house_star (a : E) : house (star a) = house a := by
  have hs : star a = (NumberField.IsCMField.complexConj E) a := rfl
  have key : ∀ φ : E →+* ℂ, ‖canonicalEmbedding E (star a) φ‖ = ‖canonicalEmbedding E a φ‖ := by
    intro φ
    rw [canonicalEmbedding.apply_at, canonicalEmbedding.apply_at, hs,
      NumberField.IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  unfold house
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun φ => (key φ).le.trans (norm_le_pi_norm _ φ)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun φ => (key φ).ge.trans (norm_le_pi_norm _ φ)

variable (E)

def FrameSmall : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ[E] V →ₗ⋆[E] E)
    (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k

def ShortSmall : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ N : ℤ, N ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v ∈ Λ, v ≠ 0 ∧ house (h v v) ≤ C ∧ ν v ≤ B ^ k

def AnisoSmall : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ N : ℤ, N ≠ 0 → ∃ (S : Set E) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧
    ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v ∈ Λ, h v v ∈ S ∧ ν v ≤ B ^ k

def OrthoSmall : Prop :=
  ∀ n : ℕ, ∀ N : ℤ, N ≠ 0 → ∃ (S : Set E) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧
    ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ∈ S ∧ ν (v i) ≤ B ^ k

end Lattices

end GlobalTheory.SmoothForms

end
