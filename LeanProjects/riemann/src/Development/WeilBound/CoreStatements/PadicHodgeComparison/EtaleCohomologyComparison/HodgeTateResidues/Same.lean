import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Module

namespace CrystallineSemistableComparison.HT.H2

variable {K B B' E : Type} [Field K] [CommRing B] [CommRing B'] [CommRing E] [Algebra K B] [Algebra K B']
  {V V' V'' : ℕ → Type 1} [∀ a, AddCommGroup (V a)] [∀ a, Module K (V a)] [∀ a, AddCommGroup (V' a)] [∀ a, Module K (V' a)]
  [∀ a, AddCommGroup (V'' a)] [∀ a, Module K (V'' a)]
  {W : Type 1} [AddCommGroup W] [Module B W]

structure ACo (θ : B →+* E) (μ : ∀ a, V a →ₛₗ[algebraMap K B] W) (r : ℕ) (co : W →+ ∀ a, Dual K (V a) →+ E) : Prop where
  smul : ∀ (b : B) w a φ, co (b • w) a φ = θ b * co w a φ
  same : ∀ a ≤ r, ∀ y φ, co (μ a y) a φ = θ (algebraMap K B (φ y))
  diff : ∀ a a', a ≠ a' → ∀ y, co (μ a' y) a = 0
  span : Submodule.span B {w : W | ∃ a ≤ r, ∃ y, w = μ a y} = ⊤

theorem ACo.hom {W' : Type 1} [AddCommGroup W'] [Module B' W'] {θ : B →+* E} {θ' : B' →+* E}
    {μ : ∀ a, V a →ₛₗ[algebraMap K B] W} {μ' : ∀ a, V' a →ₛₗ[algebraMap K B'] W'} {r r' : ℕ}
    {co : W →+ ∀ a, Dual K (V a) →+ E} {co' : W' →+ ∀ a, Dual K (V' a) →+ E} (h : ACo θ μ r co) (h' : ACo θ' μ' r' co')
    (hr : r ≤ r') {sB : B →+* B'} (sC : E →+* E) (hθ : ∀ b, θ' (sB b) = sC (θ b))
    (ho : ∀ k : K, sB (algebraMap K B k) = algebraMap K B' k) (f : W →ₛₗ[sB] W') (p : ∀ a, V a →ₗ[K] V' a) (u : ℕ → B')
    (hμ : ∀ a ≤ r, ∀ y, f (μ a y) = u a • μ' a (p a y)) (w : W) (a : ℕ) (φ : Dual K (V' a)) :
    co' (f w) a φ = θ' (u a) * sC (co w a (φ ∘ₗ p a)) := by
  have hw : w ∈ Submodule.span B {w : W | ∃ a ≤ r, ∃ y, w = μ a y} := h.span ▸ trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a', ha', y, rfl⟩ := hw
    rw [hμ a' ha', h'.smul]
    by_cases e : a = a'
    · subst e
      rw [h'.same a (ha'.trans hr), h.same a ha', ← hθ, ho]; rfl
    · rw [h'.diff a a' e, h.diff a a' e]; simp
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Pi.add_apply, AddMonoidHom.add_apply, hx, hy, mul_add]
  | smul b x _ hx => rw [map_smulₛₗ, h'.smul, h.smul, hx, hθ, map_mul]; ring

theorem ACo.cup {W' W'' : Type 1} [AddCommGroup W'] [Module B W'] [AddCommGroup W''] [Module B W''] {θ : B →+* E}
    {μ : ∀ a, V a →ₛₗ[algebraMap K B] W} {μ' : ∀ a, V' a →ₛₗ[algebraMap K B] W'} {μ'' : ∀ a, V'' a →ₛₗ[algebraMap K B] W''}
    {r r' s : ℕ} {co : W →+ ∀ a, Dual K (V a) →+ E} {co' : W' →+ ∀ a, Dual K (V' a) →+ E} {co'' : W'' →+ ∀ a, Dual K (V'' a) →+ E}
    (h : ACo θ μ r co) (h' : ACo θ μ' r' co') (h'' : ACo θ μ'' s co'') (hs : r + r' = s) (o : K →+* E)
    (ho : ∀ k, θ (algebraMap K B k) = o k) (cu : W →ₗ[B] W' →ₗ[B] W'')
    (cV : ∀ {a a' c : ℕ}, a + a' = c → V a → V' a' → V'' c)
    (hV : ∀ {a a' c : ℕ} (e : a + a' = c), ∃ b : V a →ₗ[K] V' a' →ₗ[K] V'' c, ∀ x y, b x y = cV e x y)
    (hμ : ∀ {a a' c : ℕ} (e : a + a' = c), a ≤ r → a' ≤ r' → ∀ y y', cu (μ a y) (μ' a' y') = μ'' c (cV e y y'))
    {m m' : ℕ → ℕ} (b : ∀ a, Basis (Fin (m a)) K (V a)) (b' : ∀ a, Basis (Fin (m' a)) K (V' a)) (c : ℕ) (φ : Dual K (V'' c))
    (w : W) (w' : W') :
    co'' (cu w w') c φ = ∑ p : (Finset.HasAntidiagonal.antidiagonal c : Finset (ℕ × ℕ)), ∑ t, ∑ t',
      co w p.1.1 ((b p.1.1).coord t) * co' w' p.1.2 ((b' p.1.2).coord t') *
        o (φ (cV (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) (b p.1.1 t) (b' p.1.2 t'))) := by
  have hw : w ∈ Submodule.span B {w : W | ∃ a ≤ r, ∃ y, w = μ a y} := h.span ▸ trivial
  induction hw using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, AddMonoidHom.add_apply, hx, hy, add_mul, Finset.sum_add_distrib]
  | smul d x _ hx =>
    rw [map_smul, LinearMap.smul_apply, h''.smul, hx]
    simp only [h.smul, Finset.mul_sum, mul_assoc]
  | mem w hw =>
  obtain ⟨a, ha, y, rfl⟩ := hw
  have hw' : w' ∈ Submodule.span B {w : W' | ∃ a ≤ r', ∃ y, w = μ' a y} := h'.span ▸ trivial
  induction hw' using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, Pi.add_apply, AddMonoidHom.add_apply, hx, hy, add_mul, mul_add, Finset.sum_add_distrib]
  | smul d x _ hx =>
    rw [map_smul, h''.smul, hx]
    simp only [h'.smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  | mem w' hw' =>
  obtain ⟨a', ha', y', rfl⟩ := hw'
  have hz : ∀ p : (Finset.HasAntidiagonal.antidiagonal c : Finset (ℕ × ℕ)), p.1 ≠ (a, a') → (∑ t, ∑ t',
      co (μ a y) p.1.1 ((b p.1.1).coord t) * co' (μ' a' y') p.1.2 ((b' p.1.2).coord t') *
        o (φ (cV (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) (b p.1.1 t) (b' p.1.2 t')))) = 0 := by
    intro p hp
    by_cases e : p.1.1 = a
    · have e' : p.1.2 ≠ a' := fun e' => hp (Prod.ext e e')
      simp [h'.diff _ _ e']
    · simp [h.diff _ _ e]
  by_cases e : a + a' = c
  · rw [hμ e ha ha', h''.same c (by omega), ho,
      Finset.sum_eq_single ⟨(a, a'), Finset.HasAntidiagonal.mem_antidiagonal.2 e⟩ (fun p _ hp => hz p fun e => hp (Subtype.ext e))
        (fun hh => absurd (Finset.mem_univ _) hh)]
    obtain ⟨β, hβ⟩ := hV e
    simp only [h.same a ha, h'.same a' ha', ho, ← hβ, ← map_mul, ← map_sum]
    congr 1
    conv_lhs => rw [← (b a).sum_repr y, ← (b' a').sum_repr y']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [hμ rfl ha ha', h''.diff c _ (Ne.symm e), AddMonoidHom.zero_apply]
    refine (Finset.sum_eq_zero fun p _ => hz p fun e' => e ?_).symm
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    rw [e'] at this
    exact this

end CrystallineSemistableComparison.HT.H2
