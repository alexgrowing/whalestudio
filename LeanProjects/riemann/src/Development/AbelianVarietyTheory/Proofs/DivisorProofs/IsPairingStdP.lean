import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

structure Setup (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V)) : Prop where
  pair : IsPairing P
  pair₁ : IsPairing P₁
  add : ∀ w w', j (w + w') = j w + j w'
  smul : ∀ (c : ℝ) w, j (c • w) = c • j w
  symp : ∀ w w', omega P (j w) (j w') = omega P₁ w w'
  iso : ∀ l ∈ L, ∀ l' ∈ L, omega P l l' = 0
  orth : ∀ l ∈ L, ∀ w, omega P l (j w) = 0
  max : ∀ v, (∀ l ∈ L, omega P v l = 0) → (∀ w, omega P v (j w) = 0) → v ∈ L

def Laws (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V))
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) : Prop :=
  (∀ w (f f₁ : 𝓢(V, ℂ)) (f₂ : 𝓢(V₁, ℂ)), ⇑f₁ = schrF P (j w) ⇑f → ⇑f₂ = schrF P₁ w ⇑(T f) → T f₁ = f₂) ∧
  ∀ l ∈ L, ∀ f f₁ : 𝓢(V, ℂ), ⇑f₁ = schrF P l ⇑f → T f₁ = T f

def stdP (P₁ : V₁ → V₁ → ℝ) (k : ℕ) (x y : V₁ × (Fin k → ℝ)) : ℝ := P₁ x.1 y.1 + ∑ i, x.2 i * y.2 i

def jStd (k : ℕ) (w : V₁ × V₁) : (V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ)) := ((w.1, 0), (w.2, 0))

variable (V₁) in

def LStd (k : ℕ) : Set ((V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ))) :=
  {l | ∃ b : Fin k → ℝ, l = ((0, 0), (0, b))}

theorem isPairing_stdP {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : IsPairing (stdP P₁ k) where
  addL x x' y := by
    simp only [stdP, Prod.fst_add, Prod.snd_add, h.addL, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
  addR x y y' := by
    simp only [stdP, Prod.fst_add, Prod.snd_add, h.addR, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  smulL c x y := by
    simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulL, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring
  smulR c x y := by
    simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulR, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      ← Finset.mul_sum]
    ring
  nondegL x hx := by
    have h1 : x.1 = 0 := h.nondegL _ fun y => by simpa [stdP] using hx (y, 0)
    have h2 : ∑ i, x.2 i * x.2 i = 0 := by
      have := hx (0, x.2)
      simp only [stdP] at this
      rwa [show P₁ x.1 0 = 0 by simpa using h.smulR 0 x.1 0, zero_add] at this
    have h3 : x.2 = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x.2 i))).1 h2 i (Finset.mem_univ _)
      simpa using this
    exact Prod.ext h1 h3
  nondegR y hy := by
    have h1 : y.1 = 0 := h.nondegR _ fun x => by simpa [stdP] using hy (x, 0)
    have h2 : ∑ i, y.2 i * y.2 i = 0 := by
      have := hy (0, y.2)
      simp only [stdP] at this
      rwa [show P₁ 0 y.1 = 0 by simpa using h.smulL 0 0 y.1, zero_add] at this
    have h3 : y.2 = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y.2 i))).1 h2 i (Finset.mem_univ _)
      simpa using this
    exact Prod.ext h1 h3

theorem IsPairing.zero_left {P : V → V → ℝ} (h : IsPairing P) (y : V) : P 0 y = 0 := by
  simpa using h.smulL 0 0 y

theorem IsPairing.zero_right {P : V → V → ℝ} (h : IsPairing P) (x : V) : P x 0 = 0 := by
  simpa using h.smulR 0 x 0

theorem setup_std {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : Setup (stdP P₁ k) P₁ (jStd k) (LStd V₁ k) where
  pair := isPairing_stdP h k
  pair₁ := h
  add w w' := by simp [jStd]
  smul c w := by simp [jStd]
  symp w w' := by simp [omega, stdP, jStd]
  iso := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    simp [omega, stdP, h.zero_left]
  orth := by
    rintro _ ⟨b, rfl⟩ w
    simp [omega, stdP, jStd, h.zero_left, h.zero_right]
  max := by
    rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hL hj
    have e2 : a₂ = 0 := by
      have := hL ((0, 0), (0, a₂)) ⟨a₂, rfl⟩
      simp only [omega, stdP, h.zero_right, h.zero_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        zero_add, sub_zero] at this
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (a₂ i))).1 this i (Finset.mem_univ _)
      simpa using this
    have e1 : a₁ = 0 := h.nondegL _ fun y => by
      have := hj (0, y)
      simpa [omega, stdP, jStd, h.zero_left] using this
    have e3 : b₁ = 0 := h.nondegR _ fun x => by
      have := hj (x, 0)
      simpa [omega, stdP, jStd, h.zero_right] using this
    exact ⟨b₂, by simp [e1, e2, e3]⟩

theorem isPairing_mul : IsPairing (fun x y : ℝ => x * y) where
  addL x x' y := add_mul x x' y
  addR x y y' := mul_add x y y'
  smulL c x y := by simp [mul_assoc]
  smulR c x y := by simp only [smul_eq_mul]; ring
  nondegL x hx := by simpa using hx 1
  nondegR y hy := by simpa using hy 1

example : Setup (stdP (fun x y : ℝ => x * y) 1) (fun x y : ℝ => x * y) (jStd 1) (LStd ℝ 1) :=
  setup_std isPairing_mul 1

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def jMap (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁)
    (w : (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) × (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  let c := M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (liftV w.1, liftV w.2) * (incM F H'.ι)ᵀ)
  (locV c.1, locV c.2)

def LSet (M : Model σ X W) {d₁ : ℕ} (H' : Plane E d d₁) :
    Set ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
  {l | ∃ u ∈ GlobalTheory.ThK.iso0 (F := F) n H', At (evI F) u ∧ l = (locV (M.co.e u).1, locV (M.co.e u).2)}

end Adelic

end GlobalTheory.ArchUniq
