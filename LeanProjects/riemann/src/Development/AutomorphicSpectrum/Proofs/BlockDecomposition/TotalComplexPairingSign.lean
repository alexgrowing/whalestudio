import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.TotPairing

variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R} {M : DCx.{w''} R}

theorem eq_sum_sgl (K : DCx.{w} R) {n : ℕ} {x : ∀ p q, K.X p q} (hx : x ∈ K.T n) :
    x = ∑ c ∈ Finset.HasAntidiagonal.antidiagonal n, K.sgl c.1 c.2 (x c.1 c.2) := by
  funext r s
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases h : r + s = n
  · rw [Finset.sum_eq_single (r, s)]
    · exact (K.sgl_self r s _).symm
    · rintro ⟨a, b⟩ _ hne
      refine K.sgl_ne _ ?_
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2])
    · intro hh
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hh
  · rw [hx r s h, Finset.sum_eq_zero]
    rintro ⟨a, b⟩ hab
    have hab' : a + b = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    exact K.sgl_ne _ (by omega)

def cmp (K : DCx.{w} R) (p q : ℕ) : (∀ a b, K.X a b) →ₗ[R] K.X p q :=
  (LinearMap.proj (R := R) (φ := fun b => K.X p b) q).comp
    (LinearMap.proj (R := R) (φ := fun a => ∀ b, K.X a b) p)

theorem cmp_apply (K : DCx.{w} R) (p q : ℕ) (x : ∀ a b, K.X a b) : cmp K p q x = x p q := rfl

def gen (P : DPairing K L M) (p q p' q' : ℕ) : K.X p q →ₗ[R] L.X p' q' →ₗ[R] (∀ a b, M.X a b) :=
  (-1 : ℤ) ^ (q * p') • (P.μ (p := p) (q := q) (p' := p') (q' := q') rfl rfl).compr₂ (M.sgl (p + p') (q + q'))

theorem gen_apply (P : DPairing K L M) (p q p' q' : ℕ) (x : K.X p q) (y : L.X p' q') :
    gen P p q p' q' x y = (-1 : ℤ) ^ (q * p') • M.sgl (p + p') (q + q') (P.μ rfl rfl x y) := by
  simp [gen, LinearMap.smul_apply, LinearMap.compr₂_apply]

def fam (P : DPairing K L M) (a b : ℕ) :
    (∀ p q, K.X p q) →ₗ[R] (∀ p q, L.X p q) →ₗ[R] (∀ p q, M.X p q) :=
  ∑ c ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ c' ∈ Finset.HasAntidiagonal.antidiagonal b,
    (gen P c.1 c.2 c'.1 c'.2).compl₁₂ (cmp K c.1 c.2) (cmp L c'.1 c'.2)

theorem fam_apply (P : DPairing K L M) (a b : ℕ) (x : ∀ p q, K.X p q) (y : ∀ p q, L.X p q) :
    fam P a b x y = ∑ c ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ c' ∈ Finset.HasAntidiagonal.antidiagonal b,
      gen P c.1 c.2 c'.1 c'.2 (x c.1 c.2) (y c'.1 c'.2) := by
  simp only [fam, LinearMap.sum_apply, LinearMap.compl₁₂_apply, cmp_apply]

theorem fam_sgl (P : DPairing K L M) {p q p' q' a b : ℕ} (h : p + q = a) (h' : p' + q' = b)
    (x : K.X p q) (y : L.X p' q') :
    fam P a b (K.sgl p q x) (L.sgl p' q' y) = gen P p q p' q' x y := by
  rw [fam_apply, Finset.sum_eq_single (p, q), Finset.sum_eq_single (p', q')]
  · simp only [DCx.sgl_self]
  · rintro ⟨r, s⟩ _ hne
    have : L.sgl p' q' y r s = 0 := L.sgl_ne _ (by
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2]))
    simp only [this, map_zero]
  · intro hh
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h') hh
  · rintro ⟨r, s⟩ _ hne
    have : K.sgl p q x r s = 0 := K.sgl_ne _ (by
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2]))
    simp only [this, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]
  · intro hh
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hh

theorem fam_mem (P : DPairing K L M) {a b n : ℕ} (h : a + b = n) (x : ∀ p q, K.X p q) (y : ∀ p q, L.X p q) :
    fam P a b x y ∈ M.T n := by
  rw [fam_apply]
  refine Submodule.sum_mem _ fun c hc => Submodule.sum_mem _ fun c' hc' => ?_
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hc
  have e' := Finset.HasAntidiagonal.mem_antidiagonal.1 hc'
  rw [gen_apply]
  refine Submodule.smul_of_tower_mem _ _ ?_
  intro r s hrs
  exact M.sgl_ne _ (by omega)

theorem sgl_mu (P : DPairing K L M) {p q p' q' a b : ℕ} (h : p + p' = a) (h' : q + q' = b)
    (x : K.X p q) (y : L.X p' q') :
    M.sgl a b (P.μ h h' x y) = M.sgl (p + p') (q + q') (P.μ rfl rfl x y) := by
  subst h h'
  rfl

theorem sign_id {A : Type*} [AddCommGroup A] (e s t r : ℤ) (ht : t * t = 1) (A₁ A₂ A₃ A₄ : A) :
    e • (A₁ + s • A₂ + (s * r) • (A₃ + t • A₄)) =
      e • A₁ + (s * (e * r)) • A₃ + (s * t) • ((e * t) • A₂ + (r * e) • A₄) := by
  match_scalars
  · ring
  · linear_combination (-e * s) * ht
  · ring
  · linear_combination (-e * s * r) * ht + (e * s * r) * ht

theorem leib_gen (P : DPairing K L M) (p q p' q' : ℕ) (x : K.X p q) (y : L.X p' q') :
    M.D (gen P p q p' q' x y) =
      gen P (p + 1) q p' q' (K.dh p q x) y + (-1 : ℤ) ^ p • gen P p (q + 1) p' q' (K.dv p q x) y +
        (-1 : ℤ) ^ (p + q) • (gen P p q (p' + 1) q' x (L.dh p' q' y) +
          (-1 : ℤ) ^ p' • gen P p q p' (q' + 1) x (L.dv p' q' y)) := by
  have e₁ := sgl_mu P (p := p + 1) (p' := p') (a := p + p' + 1) (by omega) (rfl : q + q' = q + q') (K.dh p q x) y
  have e₂ := sgl_mu P (p := p) (p' := p' + 1) (a := p + p' + 1) (by omega) (rfl : q + q' = q + q') x (L.dh p' q' y)
  have e₃ := sgl_mu P (q := q + 1) (q' := q') (b := q + q' + 1) (rfl : p + p' = p + p') (by omega) (K.dv p q x) y
  have e₄ := sgl_mu P (q := q) (q' := q' + 1) (b := q + q' + 1) (rfl : p + p' = p + p') (by omega) x (L.dv p' q' y)
  simp only [gen_apply, map_zsmul, DCx.D_sgl, P.lh rfl rfl, P.lv rfl rfl, map_add, e₁, e₂, e₃, e₄]
  have ht : ((-1 : ℤ) ^ q) * ((-1 : ℤ) ^ q) = 1 := by
    rw [← mul_pow]; simp
  have s₁ : (-1 : ℤ) ^ (p + p') = (-1) ^ p * (-1) ^ p' := pow_add _ _ _
  have s₂ : (-1 : ℤ) ^ (p + q) = (-1) ^ p * (-1) ^ q := pow_add _ _ _
  have s₃ : (-1 : ℤ) ^ ((q + 1) * p') = (-1) ^ (q * p') * (-1) ^ p' := by rw [add_mul, one_mul, pow_add]
  have s₄ : (-1 : ℤ) ^ (q * (p' + 1)) = (-1) ^ (q * p') * (-1) ^ q := by rw [mul_add, mul_one, pow_add]
  rw [s₁, s₂, s₃, s₄, smul_smul, smul_smul]
  exact sign_id _ _ _ _ ht _ _ _ _

theorem leib_fam (P : DPairing K L M) {a b : ℕ} {x : ∀ p q, K.X p q} {y : ∀ p q, L.X p q}
    (hx : x ∈ K.T a) (hy : y ∈ L.T b) :
    M.D (fam P a b x y) = fam P (a + 1) b (K.D x) y + (-1 : ℤ) ^ a • fam P a (b + 1) x (L.D y) := by
  rw [eq_sum_sgl K hx, eq_sum_sgl L hy]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun c' hc' => ?_
  have e' := Finset.HasAntidiagonal.mem_antidiagonal.1 hc
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hc'
  obtain ⟨p', q'⟩ := c
  obtain ⟨p, q⟩ := c'
  dsimp only at e e' ⊢
  rw [fam_sgl P e e', leib_gen, DCx.D_sgl, DCx.D_sgl]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [fam_sgl P (by omega) e', fam_sgl P (by omega) e', fam_sgl P e (by omega), fam_sgl P e (by omega), e]

def totP (P : DPairing K L M) : CxPairing K.tot L.tot M.tot where
  μ {a b n} h := LinearMap.mk₂ R (fun x y => ⟨fam P a b x.1 y.1, fam_mem P h _ _⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
    (fun x y y' => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
  leib {a b n} h x y := Subtype.ext (leib_fam P x.2 y.2)

end GlobalTheory.CompanionTheory.TotPairing
