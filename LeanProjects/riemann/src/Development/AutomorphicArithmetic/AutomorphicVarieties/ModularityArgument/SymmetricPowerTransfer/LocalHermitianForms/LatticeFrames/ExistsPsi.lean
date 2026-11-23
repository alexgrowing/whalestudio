import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.ExistsFrame
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

variable (τ) in

def Bf (c t : K) : K × Etau K τ →ₗ[K] K × Etau K τ →ₗ[K] K :=
  LinearMap.mk₂ K (fun v w => c * v.1 * w.1 + t * QuadraticAlgebra.trace (v.2 * star w.2))
    (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring) (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring)
    (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring) (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring)

theorem Bf_apply (c t : K) (v w : K × Etau K τ) : Bf τ c t v w = c * v.1 * w.1 + t * QuadraticAlgebra.trace (v.2 * star w.2) := rfl

theorem Bf_symm (c t : K) (v w : K × Etau K τ) : Bf τ c t v w = Bf τ c t w v := by
  simp [Bf_apply, QuadraticAlgebra.trace_def]; ring

def psi (s : K) (β : Etau K τ) : K × Etau K τ →ₗ[K] Etau K τ →ₗ[K] Etau K τ :=
  LinearMap.mk₂ K (fun v y => s • (v.1 • ((ω - star ω) * y) + v.2 * β * star y))
    (fun a b w => by ext <;> simp <;> ring) (fun a b w => by ext <;> simp <;> ring)
    (fun a b w => by ext <;> simp <;> ring) (fun a b w => by ext <;> simp <;> ring)

theorem psi_apply (s : K) (β : Etau K τ) (v : K × Etau K τ) (y : Etau K τ) :
    psi s β v y = s • (v.1 • ((ω - star ω) * y) + v.2 * β * star y) := rfl

theorem psi_anti {c t s ε : K} {β : Etau K τ} (hc : c = (τ ^ 2 - 4) * ε * s ^ 2) (hβ : QuadraticAlgebra.norm β * ε * s ^ 2 = 2 * t)
    (v w : K × Etau K τ) (y : Etau K τ) : ε • (psi s β v (psi s β w y) + psi s β w (psi s β v y)) = (2 * Bf τ c t v w) • y := by
  subst hc
  rw [QuadraticAlgebra.norm_def] at hβ
  ext <;> simp [psi_apply, Bf_apply, QuadraticAlgebra.trace_def]
  · linear_combination (2 * v.2.re * w.2.re + τ * v.2.re * w.2.im + 2 * v.2.im * w.2.im + τ * v.2.im * w.2.re) * y.re * hβ
  · linear_combination (2 * v.2.re * w.2.re + τ * v.2.re * w.2.im + 2 * v.2.im * w.2.im + τ * v.2.im * w.2.re) * y.im * hβ

theorem psi_quo (s : K) (β : Etau K τ) (z : (Etau K τ)ˣ) (v : K × Etau K τ) (y : Etau K τ) :
    psi s β (v.1, quo z * v.2) ((z : Etau K τ) * y) = (z : Etau K τ) * psi s β v y := by
  have h1 : star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  simp only [psi_apply, quo, star_mul, Algebra.smul_def]
  linear_combination (algebraMap K (Etau K τ) s * (z : Etau K τ) * v.2 * β * star y) * h1

theorem psi_inj {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) {v : K × Etau K τ} (h : ∀ y, psi s β v y = 0) : v = 0 := by
  have h1 := h 1
  have h2 := h ω
  simp only [psi_apply, Algebra.smul_def] at h1 h2
  have hs' : IsUnit (algebraMap K (Etau K τ) s) := (isUnit_iff_ne_zero.mpr hs).map _
  rw [hs'.mul_right_eq_zero] at h1 h2
  simp only [star_one, mul_one] at h1
  have hΩ2 : (ω - star ω : Etau K τ) * (ω - star ω) = algebraMap K (Etau K τ) (τ ^ 2 - 4) := by
    ext <;> simp [pow_two] <;> ring
  have key : algebraMap K (Etau K τ) (v.1 * (τ ^ 2 - 4)) = 0 := by
    rw [map_mul, ← hΩ2]; linear_combination h2 - star ω * h1
  have hv1 : v.1 = 0 :=
    (mul_eq_zero.mp ((algebraMap K (Etau K τ)).injective (key.trans (map_zero _).symm))).resolve_right hD
  have hv2 : v.2 = 0 := by
    rw [hv1, map_zero, zero_mul, zero_add] at h1
    exact hβ.mul_left_eq_zero.mp h1
  exact Prod.ext hv1 hv2

theorem exists_psi {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) (y y' : Etau K τ) :
    ∃ v, ∀ b, psi s β v b = (b * star y).im • y' + (b * star y').im • y := by
  have hDu : IsUnit (algebraMap K (Etau K τ) (τ ^ 2 - 4)) := (isUnit_iff_ne_zero.mpr hD).map _
  have hΩ2 : (ω - star ω : Etau K τ) * (ω - star ω) = algebraMap K (Etau K τ) (τ ^ 2 - 4) := by
    ext <;> simp [pow_two] <;> ring
  have hΩu : IsUnit (ω - star ω : Etau K τ) := isUnit_of_mul_isUnit_left (hΩ2 ▸ hDu)
  have htr : algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) = star y * y' + y * star y' := by
    ext <;> simp [QuadraticAlgebra.trace_def] <;> ring
  have hk : algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
      algebraMap K (Etau K τ) (τ ^ 2 - 4) = 1 := by
    rw [← map_mul, ← map_mul, ← map_one (algebraMap K (Etau K τ))]; congr 1; field_simp
  have hsub : ∀ z : Etau K τ, algebraMap K (Etau K τ) z.im * (ω - star ω) = z - star z := by
    intro z; rw [QuadraticAlgebra.sub_star z, Algebra.smul_def]
  have hinv : ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β = 1 := by
    have := hβ.unit.inv_mul; rwa [hβ.unit_spec] at this
  refine ⟨((s * (τ ^ 2 - 4))⁻¹ * QuadraticAlgebra.trace (star y * y'),
    -(2 * (algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
      (y * y' * (ω - star ω) * ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ))))), fun b => ?_⟩
  have hs1 := hsub (b * star y)
  have hs2 := hsub (b * star y')
  rw [star_mul, star_star] at hs1 hs2
  apply hΩu.mul_left_cancel
  simp only [psi_apply, Algebra.smul_def, map_mul]
  linear_combination
    (algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
        algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) * b -
      2 * algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ * y * y' *
        ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β * star b) * hΩ2 +
    (algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) * b -
      2 * y * y' * ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β * star b) * hk +
    (-2 * y * y' * star b) * hinv + b * htr - y' * hs1 - y * hs2

variable (O) in

def S0 (s : K) (β : Etau K τ) (Λ : Set (Etau K τ)) : Set (K × Etau K τ) := {v | ∀ y ∈ Λ, psi s β v y ∈ Λ}

variable (O) in

structure Uni (c t : K) (S : Set (K × Etau K τ)) : Prop where
  fg : ∃ s : Finset (K × Etau K τ), S = Submodule.span O (s : Set (K × Etau K τ))
  dual : ∀ y, y ∈ S ↔ ∀ x ∈ S, Bf τ c t x y ∈ (algebraMap O K).range

theorem coord {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) (b : Etau K τ) :
    b = (-(b * star y₂).im / (y₂ * star y₁).im) • y₁ + ((b * star y₁).im / (y₂ * star y₁).im) • y₂ := by
  have key : (y₂ * star y₁).im • b = (-(b * star y₂).im) • y₁ + (b * star y₁).im • y₂ := by
    ext <;> simp <;> ring
  calc b = ((y₂ * star y₁).im)⁻¹ • ((y₂ * star y₁).im • b) := by
        rw [smul_smul, inv_mul_cancel₀ hg, one_smul]
    _ = _ := by rw [key, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

theorem coord_uniq {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) {a b a' b' : K} (h : a • y₁ + b • y₂ = a' • y₁ + b' • y₂) : a = a' ∧ b = b' := by
  have e1 := congrArg (fun z => (z * star y₁).im) h
  have e2 := congrArg (fun z => (z * star y₂).im) h
  simp only [add_mul, smul_mul_assoc, im_add, im_smul, smul_eq_mul] at e1 e2
  have n1 : (y₁ * star y₁).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have n2 : (y₂ * star y₂).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have h12 : (y₁ * star y₂).im = -(y₂ * star y₁).im := by
    rw [← im_star, star_mul, star_star]
  rw [n1] at e1
  rw [n2, h12] at e2
  constructor
  · have : (a - a') * (y₂ * star y₁).im = 0 := by linear_combination -e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)
  · have : (b - b') * (y₂ * star y₁).im = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)

theorem exists_efh {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) {y₁ y₂ : Etau K τ}
    (hg : (y₂ * star y₁).im ≠ 0) : ∃ e f h, psi s β e y₁ = 0 ∧ psi s β e y₂ = y₁ ∧ psi s β f y₁ = y₂ ∧ psi s β f y₂ = 0 ∧
      psi s β h y₁ = -y₁ ∧ psi s β h y₂ = y₂ := by
  have n1 : (y₁ * star y₁).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have n2 : (y₂ * star y₂).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have h12 : (y₁ * star y₂).im = -(y₂ * star y₁).im := by
    rw [← im_star, star_mul, star_star]
  have hstar : ∀ (k : K) (x : Etau K τ), star (k • x) = k • star x := by
    intro k x; ext <;> simp <;> ring
  set G := (y₂ * star y₁).im with hG
  obtain ⟨e, he⟩ := exists_psi hD hs hβ y₁ ((2 * G)⁻¹ • y₁)
  obtain ⟨f, hf⟩ := exists_psi hD hs hβ y₂ ((-(2 * G))⁻¹ • y₂)
  obtain ⟨h, hh⟩ := exists_psi hD hs hβ y₁ (G⁻¹ • y₂)
  refine ⟨e, f, h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [he, hf, hh, hstar, mul_smul_comm, im_smul, smul_eq_mul, n1, n2, h12, ← hG, zero_smul,
      mul_zero, zero_add, add_zero, smul_smul, ← add_smul]
  all_goals (ext <;> simp <;> field_simp <;> ring)

end UpperTheory.V.Z.Sym.Loc.CP
