import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowAlg

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem four (h : IsCub θ) (P q B b x : A) :
    θ (P * B) (q * b) x * θ P B x * θ q b x = θ (P * q) (B * b) x * θ P q x * θ B b x := by
  have c1 := h.coc P B (q * b) x
  have c2 := h.coc B q b x
  have c3 := h.coc P q (B * b) x
  have c4 := h.coc q B b x
  rw [mul_left_comm B q b] at c1
  rw [mul_comm q B, h.s01 q B x] at c4
  calc θ (P * B) (q * b) x * θ P B x * θ q b x
      = θ P (q * (B * b)) x * (θ B (q * b) x * θ q b x) := by rw [c1, mul_assoc]
    _ = θ P (q * (B * b)) x * (θ q (B * b) x * θ B b x) := by rw [← c2, c4]
    _ = θ (P * q) (B * b) x * θ P q x * θ B b x := by rw [c3, mul_assoc]

theorem cubic_norm_mul_identity (h : IsCub θ) (k : ℕ) (B b x : A) :
    θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x = cubN θ k 1 (B * b) x * θ B b x ^ k := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have f := four h (B ^ k) (b ^ k) B b x
    simp only [cubN, one_mul] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ B, pow_succ b,
      pow_succ (θ B b x), mul_pow]
    apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x)
    calc _ = (θ (B ^ k * B) (b ^ k * b) x * θ (B ^ k) B x * θ (b ^ k) b x) *
          (θ (B ^ k) (b ^ k) x * (∏ i ∈ Finset.range k, θ (B ^ i) B x) *
            ∏ i ∈ Finset.range k, θ (b ^ i) b x) := by ac_rfl
      _ = _ := by rw [f, ih]; ac_rfl

theorem cubN_mul (h : IsCub θ) (k : ℕ) (a B b x : A) :
    cubN θ k a B x * cubN θ k (a * B ^ k) b x * (θ B x b ^ k)⁻¹ = cubN θ k a (B * b) x := by
  have e1 := cubic_norm_mul_identity h k B b x
  have c := h.coc a (B ^ k) (b ^ k) x
  rw [h.N_split k a B x, h.N_split k (a * B ^ k) b x, h.N_split k a (B * b) x, mul_pow, h.s12 B x b]
  apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x * θ B b x ^ k)
  calc _ = (θ (a * B ^ k) (b ^ k) x * θ a (B ^ k) x) *
        (θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x) * ((θ B b x ^ k)⁻¹ * θ B b x ^ k) := by
        ac_rfl
    _ = (θ a (B ^ k * b ^ k) x * θ (B ^ k) (b ^ k) x) * (cubN θ k 1 (B * b) x * θ B b x ^ k) := by
        rw [c, e1, inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl

theorem hv_comp (h : IsCub θ) (k : ℕ) (a B b x : A) :
    hv θ k a B (x * b) * hv θ k (a * B ^ k) b x = hv θ k a (B * b) x * hv θ k a B b := by
  have n := h.N_add k a B x b
  have m := cubN_mul h k a B b x
  have t : ∀ u v, θ a u v = θ u v a := fun u v => (h.s01 a u v).trans (h.s12 u a v)
  have key : θ a x b * θ a (x * b) B = θ a x (B * b) * θ a b B := by
    have c := h.coc x b B a
    rw [t x b, t (x * b) B, t x (B * b), t b B, mul_comm B b, mul_comm (θ x b a)]
    exact c
  simp only [hv]
  apply mul_right_cancel (b := θ a x b * θ a (x * b) B * θ (a * B ^ k) x b * θ B x b ^ k)
  rw [← m]
  calc _ = (cubN θ k a B (x * b) * θ a x b * θ B x b ^ k) * cubN θ k (a * B ^ k) b x *
        ((θ a (x * b) B)⁻¹ * θ a (x * b) B) * ((θ (a * B ^ k) x b)⁻¹ * θ (a * B ^ k) x b) := by ac_rfl
    _ = θ (a * B ^ k) x b * cubN θ k a B x * cubN θ k a B b * cubN θ k (a * B ^ k) b x := by
        rw [n, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
    _ = (cubN θ k a B x * cubN θ k (a * B ^ k) b x * cubN θ k a B b * θ (a * B ^ k) x b) *
        ((θ B x b ^ k)⁻¹ * θ B x b ^ k) * ((θ a x (B * b))⁻¹ * θ a x (B * b)) * ((θ a b B)⁻¹ * θ a b B) := by
        rw [inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one, mul_one]; ac_rfl
    _ = _ := by rw [key]; ac_rfl

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
