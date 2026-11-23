import Mathlib
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta

namespace GlobalTheory.TorusAlg.Test

section General

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
  {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem exists_chart (hL : L.IsLB) (x : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  obtain ⟨y⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  have : x y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨i, fun w _ => ?_⟩
  rw [show w = y from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  exact hi

theorem law_forced (hL : L.IsLB) (u : HolUnif A L g) (th : L.Sec)
    (hs : τ.IsSymm) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))
    (hth : u.IsFn th (thetaChar τ a b)) (n : ℕ) (s : (lbPow L n).Sec) (θ : (Fin g → ℂ) → ℂ)
    (hθ : u.IsFnPow n s θ) (k k' : Fin g → ℤ) (z : Fin g → ℂ) (h0 : thetaChar τ a b z ≠ 0) :
    θ (z + τ *ᵥ ofIntVec k + ofIntVec k') =
      autFactor (fun i => (a i).re) (fun i => (b i).re) τ k k' z ^ n * θ z := by
  obtain ⟨i, hi⟩ := exists_chart hL (u.ex z).left
  have hl : u.ex (τ *ᵥ ofIntVec k + ofIntVec k') = 1 := (u.ker _).2 ((hΛ _).2 ⟨k', k, add_comm _ _⟩)
  have he : u.ex (z + τ *ᵥ ofIntVec k + ofIntVec k') = u.ex z := by
    rw [add_assoc, u.ex_add, hl, _root_.mul_one]
  have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U (fun _ => i) :=
    fun w hw => Set.mem_iInter.2 fun _ => hi hw
  have h1 := hθ (fun _ => i) z hi'
  have h2 := hθ (fun _ => i) (z + τ *ᵥ ofIntVec k + ofIntVec k') (by rw [he]; exact hi')
  rw [he, h1] at h2
  have hf := frame_eq_autFactor_mul u th hs ha hb hΛ hth k k' i z hi h0
  have hne := u.fr_ne i (z + τ *ᵥ ofIntVec k + ofIntVec k') (by rw [he]; exact hi)
  rw [hf, mul_pow] at h2
  apply mul_right_cancel₀ (pow_ne_zero n hne)
  rw [← h2]; ring

theorem section_ne_zero (hL : L.IsLB) (u : HolUnif A L g) (th : L.Sec)
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (hth : u.IsFn th (thetaChar τ a b)) :
    ∃ i z, valAt' (u.ex z).left (L.U i) (th.f i) ≠ 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 (thetaChar_level hs hp ha hb).1
  obtain ⟨i, hi⟩ := exists_chart hL (u.ex z).left
  exact ⟨i, z, by rw [hth i z hi]; exact mul_ne_zero hz (u.fr_ne i z hi)⟩

end General

theorem no_unif_of_zero_matrix {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L 1) :
    ¬ ∀ z, z ∈ u.Λ ↔ ∃ m n : Fin 1 → ℤ,
      z = (fun i => (m i : ℂ)) + (0 : Matrix (Fin 1) (Fin 1) ℂ).mulVec (fun i => (n i : ℂ)) := by
  intro h
  let φ : (Fin 1 → ℂ) →ₗ[ℝ] ℝ := Complex.imLm ∘ₗ LinearMap.proj 0
  have hle : Submodule.span ℝ (u.Λ : Set (Fin 1 → ℂ)) ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 fun z hz => ?_
    obtain ⟨m, n, rfl⟩ := (h z).1 hz
    simp [φ]
  rw [u.full] at hle
  have := hle (show (fun _ => Complex.I : Fin 1 → ℂ) ∈ ⊤ from trivial)
  simp [φ] at this

theorem square_lattice (H : TorusAlgebraic) :
    ∃ (P : Out.PolAV (Sp ℂ)) (th : P.L.Sec) (f : P.A ⟶ P.A), P.g = 1 ∧ IsMonHom f ∧ f ≠ 𝟙 _ ∧
      (∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x ≠ 1 ∧ x * x = 1) ∧
      (∃ (i : P.L.ι) (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A), valAt' x.left (P.L.U i) (th.f i) ≠ 0) ∧
      ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, (x ≫ f ≫ f) * x = 1 := by
  have hs : (!![Complex.I] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm := by
    ext i j; fin_cases i; fin_cases j; rfl
  have hp : ((!![Complex.I] : Matrix (Fin 1) (Fin 1) ℂ).map Complex.im).PosDef := by
    convert (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef) using 1
    ext i j; fin_cases i; fin_cases j; simp
  have ha : ∀ i : Fin 1, (fun _ => 1 / 2 : Fin 1 → ℂ) i = 0 ∨ (fun _ => 1 / 2 : Fin 1 → ℂ) i = 1 / 2 :=
    fun _ => Or.inr rfl
  obtain ⟨P, u, th, hg, hΛ, -, hth, -, -, hF⟩ := H 1 _ _ _ hs hp ha ha
  have mem : ∀ z : Fin 1 → ℂ, z ∈ u.Λ ↔ ∃ m n : ℤ, z 0 = m + Complex.I * n := by
    intro z
    rw [hΛ]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m 0, n 0, by simp [Matrix.mulVec, dotProduct]⟩
    · rintro ⟨m, n, h⟩
      refine ⟨fun _ => m, fun _ => n, funext fun i => ?_⟩
      fin_cases i
      simpa [Matrix.mulVec, dotProduct] using h
  obtain ⟨f, hf, hfz⟩ := hF (Complex.I • LinearMap.id) (by
    intro l hl
    obtain ⟨m, n, h⟩ := (mem l).1 hl
    refine (mem _).2 ⟨-n, m, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, h]
    push_cast
    linear_combination (n : ℂ) * Complex.I_mul_I)
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have half : ∀ m : ℤ, (m : ℝ) ≠ 1 / 2 := fun m h => by
    have : (2 * m : ℝ) = 1 := by linarith
    have : (2 * m : ℤ) = 1 := by exact_mod_cast this
    omega
  refine ⟨P, th, f, hg, hf, ?_, ⟨u.ex fun _ => 1 / 2, ?_, ?_⟩, ?_, ?_⟩
  · rintro rfl
    have h1 := hfz fun _ => 1 / 2
    rw [Category.comp_id] at h1
    have h2 : u.ex ((Complex.I • LinearMap.id : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) (fun _ => 1 / 2) + fun _ => 1 / 2) = 1 := by
      rw [u.ex_add, h1, ← u.ex_add, u.ker, mem]
      exact ⟨1, 0, by simp; norm_num⟩
    rw [u.ker, mem] at h2
    obtain ⟨m, n, h⟩ := h2
    have := congrArg Complex.re h
    simp at this
    exact half m (by linarith)
  · intro h
    rw [u.ker, mem] at h
    obtain ⟨m, n, h⟩ := h
    have := congrArg Complex.re h
    simp at this
    exact half m (by linarith)
  · rw [← u.ex_add, u.ker, mem]
    exact ⟨1, 0, by simp; norm_num⟩
  · obtain ⟨i, z, h⟩ := section_ne_zero P.isLB u th hs hp ha ha hth
    exact ⟨i, _, h⟩
  · intro x
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [← Category.assoc, ← hfz, ← hfz, ← u.ex_add, ← h0]
    congr 1
    simp [smul_smul]

end GlobalTheory.TorusAlg.Test
