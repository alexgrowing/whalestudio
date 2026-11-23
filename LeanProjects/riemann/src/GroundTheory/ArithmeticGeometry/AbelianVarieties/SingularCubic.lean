import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Generic

variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}

theorem map_add_of_triple {G : Type*} [AddCommGroup G] (Φ : V.toAffine.Point → G) (h0 : Φ 0 = 0)
    (hneg : ∀ P, Φ (-P) = -Φ P)
    (htri : ∀ {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : V.toAffine.Nonsingular x₁ y₁)
      (h₂ : V.toAffine.Nonsingular x₂ y₂) (h₃ : V.toAffine.Nonsingular x₃ y₃),
      Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0 →
        Φ (.some _ _ h₁) + Φ (.some _ _ h₂) + Φ (.some _ _ h₃) = 0)
    (P Q : V.toAffine.Point) : Φ (P + Q) = Φ P + Φ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change Φ (0 + Q) = Φ 0 + Φ Q; rw [zero_add, h0, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change Φ (_ + 0) = _ + Φ 0; rw [add_zero, h0, add_zero]
  set S := Point.some _ _ h₁ + Point.some _ _ h₂ with hS
  rcases hSc : S with _ | ⟨x₃, y₃, h₃⟩
  · have hQ : Point.some _ _ h₂ = -Point.some _ _ h₁ := by
      have : S = 0 := hSc
      rw [hS] at this
      exact eq_neg_of_add_eq_zero_right this
    change Φ 0 = _
    rw [h0, hQ, hneg, add_neg_cancel]
  · have hn := (nonsingular_neg (W' := V.toAffine) x₃ y₃).2 h₃
    have ht := htri h₁ h₂ hn (by
      have e : (Point.some _ _ hn : V.toAffine.Point) = -Point.some _ _ h₃ := by
        rw [Point.neg_some]
      rw [e, ← hSc, hS]; abel)
    have e : (Point.some _ _ hn : V.toAffine.Point) = -Point.some _ _ h₃ := by
      rw [Point.neg_some]
    rw [e, hneg, add_neg_eq_zero] at ht
    exact ht.symm

end Generic

section Origin

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0)
include h3 h4 h6

theorem origin_eq {x y : F} (h : V.toAffine.Equation x y) :
    y ^ 2 + V.a₁ * x * y - V.a₂ * x ^ 2 = x ^ 3 := by
  rw [equation_iff, h3, h4, h6] at h
  linear_combination h

theorem origin_x_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  subst hx
  have he := origin_eq V h3 h4 h6 h.1
  have hy : y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linear_combination he)
  subst hy
  have := (nonsingular_zero (W := V.toAffine)).1 h
  rcases this.2 with h' | h'
  · exact h' h3
  · exact h' h4

theorem origin_nonsingular {x y : F} (h : V.toAffine.Equation x y) (hx : x ≠ 0) :
    V.toAffine.Nonsingular x y := by
  rw [nonsingular_iff']
  refine ⟨h, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hA, hB⟩ := hc
  have he := origin_eq V h3 h4 h6 h
  rw [h4] at hA
  rw [h3] at hB
  apply hx
  apply pow_eq_zero_iff (n := 3) (by norm_num) |>.1
  linear_combination (-x) * hA + (-y) * hB + 2 * he

end Origin

section Cusp

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) (α : F) (h1 : V.a₁ = -2 * α) (h2 : V.a₂ = -α ^ 2)

def cuspMap : V.toAffine.Point → F
  | 0 => 0
  | .some x y _ => x / (y - α * x)

include h3 h4 h6 h1 h2

theorem cusp_eq {x y : F} (h : V.toAffine.Equation x y) : (y - α * x) ^ 2 = x ^ 3 := by
  have := origin_eq V h3 h4 h6 h
  rw [h1, h2] at this
  linear_combination this

theorem cusp_den_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : y - α * x ≠ 0 := by
  intro h0
  apply origin_x_ne_zero V h3 h4 h6 h
  have := cusp_eq V h3 h4 h6 α h1 h2 h.1
  rw [h0] at this
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 (by linear_combination -this)

theorem cuspMap_neg (P : V.toAffine.Point) : cuspMap V α (-P) = -cuspMap V α P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [cuspMap]; rfl
  · rw [Point.neg_some]
    simp only [cuspMap, negY, h1, h3]
    rw [show -y - -2 * α * x - 0 - α * x = -(y - α * x) by ring, div_neg]

theorem cuspMap_triple {x₁ y₁ x₂ y₂ x₃ y₃ : F} (g₁ : V.toAffine.Nonsingular x₁ y₁)
    (g₂ : V.toAffine.Nonsingular x₂ y₂) (g₃ : V.toAffine.Nonsingular x₃ y₃)
    (hs : Point.some _ _ g₁ + Point.some _ _ g₂ + Point.some _ _ g₃ = 0) :
    cuspMap V α (.some _ _ g₁) + cuspMap V α (.some _ _ g₂) + cuspMap V α (.some _ _ g₃) = 0 := by
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_line_of_add_eq_zero g₁ g₂ g₃ hs
  have d1 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₁
  have d2 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₂
  have d3 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₃
  simp only [cuspMap]
  rw [div_add_div _ _ d1 d2, div_add_div _ _ (mul_ne_zero d1 d2) d3, div_eq_zero_iff]
  left
  rw [h1, h2] at v1
  rw [h1, h3, h4] at v2
  rw [h3, h6] at v3
  rw [l1, l2, l3]
  linear_combination 3 * (ℓ - α) ^ 2 * v3 + 2 * (ℓ - α) * ν * v2 + ν ^ 2 * v1

def cuspHom : V.toAffine.Point →+ F :=
  AddMonoidHom.mk' (cuspMap V α) (map_add_of_triple (cuspMap V α) rfl
    (cuspMap_neg V h3 h4 h6 α h1 h2) (cuspMap_triple V h3 h4 h6 α h1 h2))

theorem cuspHom_bijective : Function.Bijective (cuspHom V h3 h4 h6 α h1 h2) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro (_ | ⟨x, y, h⟩) hP
    · rfl
    · change x / (y - α * x) = 0 at hP
      rw [div_eq_zero_iff] at hP
      rcases hP with hP | hP
      · exact absurd hP (origin_x_ne_zero V h3 h4 h6 h)
      · exact absurd hP (cusp_den_ne_zero V h3 h4 h6 α h1 h2 h)
  · intro s
    by_cases hs : s = 0
    · exact ⟨0, by rw [hs]; rfl⟩
    have he : V.toAffine.Equation (s⁻¹ ^ 2) ((α + s⁻¹) * s⁻¹ ^ 2) := by
      rw [equation_iff, h3, h4, h6, h1, h2]
      field_simp
      ring
    have hn := origin_nonsingular V h3 h4 h6 he (pow_ne_zero 2 (inv_ne_zero hs))
    refine ⟨.some _ _ hn, ?_⟩
    change s⁻¹ ^ 2 / ((α + s⁻¹) * s⁻¹ ^ 2 - α * s⁻¹ ^ 2) = s
    field_simp
    ring

def cuspEquiv : V.toAffine.Point ≃+ F :=
  AddEquiv.ofBijective (cuspHom V h3 h4 h6 α h1 h2) (cuspHom_bijective V h3 h4 h6 α h1 h2)

end Cusp

section Node

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) {L : Type*} [Field L] [Algebra F L] (α β : L)
  (hs : algebraMap F L V.a₁ = -(α + β)) (hp : algebraMap F L V.a₂ = -(α * β))

local notation "ι" => algebraMap F L

include h3 h4 h6 hs hp

theorem node_eq {x y : F} (h : V.toAffine.Equation x y) :
    (ι y - α * ι x) * (ι y - β * ι x) = ι x ^ 3 := by
  have := congrArg ι (origin_eq V h3 h4 h6 h)
  simp only [map_sub, map_add, map_mul, map_pow] at this
  rw [hs, hp] at this
  linear_combination this

theorem node_num_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : ι y - α * ι x ≠ 0 := by
  intro h0
  have := node_eq V h3 h4 h6 α β hs hp h.1
  rw [h0, zero_mul, eq_comm] at this
  exact origin_x_ne_zero V h3 h4 h6 h ((map_eq_zero _).1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this))

theorem node_den_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : ι y - β * ι x ≠ 0 := by
  intro h0
  have := node_eq V h3 h4 h6 α β hs hp h.1
  rw [h0, mul_zero, eq_comm] at this
  exact origin_x_ne_zero V h3 h4 h6 h ((map_eq_zero _).1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this))

def nodeVal : V.toAffine.Point → Lˣ
  | 0 => 1
  | .some x y h => Units.mk0 ((ι y - α * ι x) / (ι y - β * ι x))
      (div_ne_zero (node_num_ne_zero V h3 h4 h6 α β hs hp h) (node_den_ne_zero V h3 h4 h6 α β hs hp h))

theorem nodeVal_neg (P : V.toAffine.Point) :
    Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (-P)) =
      -Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [← ofMul_inv]
    congr 1
    rw [Point.neg_some]
    ext
    have hn := node_num_ne_zero V h3 h4 h6 α β hs hp h
    simp only [nodeVal, Units.val_mk0, Units.val_inv_eq_inv_val, negY, h3, map_sub, map_neg,
      map_mul, sub_zero, hs]
    rw [inv_div, div_eq_div_iff (by intro h0; apply hn; linear_combination -h0) hn]
    ring

theorem nodeVal_triple {x₁ y₁ x₂ y₂ x₃ y₃ : F} (g₁ : V.toAffine.Nonsingular x₁ y₁)
    (g₂ : V.toAffine.Nonsingular x₂ y₂) (g₃ : V.toAffine.Nonsingular x₃ y₃)
    (hsum : Point.some _ _ g₁ + Point.some _ _ g₂ + Point.some _ _ g₃ = 0) :
    Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ g₁)) +
      Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ g₂)) +
      Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ g₃)) = 0 := by
  rw [← ofMul_mul, ← ofMul_mul, ← ofMul_one]
  congr 1
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_line_of_add_eq_zero g₁ g₂ g₃ hsum
  rw [h3, h4] at v2
  rw [h3, h6] at v3
  have w1 := congrArg ι v1
  have w2 := congrArg ι v2
  have w3 := congrArg ι v3
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_ofNat, hs, hp] at w1 w2 w3
  have k1 := congrArg ι l1
  have k2 := congrArg ι l2
  have k3 := congrArg ι l3
  simp only [map_add, map_mul] at k1 k2 k3
  have hN : (ι y₁ - α * ι x₁) * (ι y₂ - α * ι x₂) * (ι y₃ - α * ι x₃) = ι ν ^ 3 := by
    rw [k1, k2, k3]
    linear_combination (ι ℓ - α) ^ 3 * w3 + (ι ℓ - α) ^ 2 * ι ν * w2 + (ι ℓ - α) * ι ν ^ 2 * w1
  have hD : (ι y₁ - β * ι x₁) * (ι y₂ - β * ι x₂) * (ι y₃ - β * ι x₃) = ι ν ^ 3 := by
    rw [k1, k2, k3]
    linear_combination (ι ℓ - β) ^ 3 * w3 + (ι ℓ - β) ^ 2 * ι ν * w2 + (ι ℓ - β) * ι ν ^ 2 * w1
  have hD0 : (ι y₁ - β * ι x₁) * (ι y₂ - β * ι x₂) * (ι y₃ - β * ι x₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (node_den_ne_zero V h3 h4 h6 α β hs hp g₁)
      (node_den_ne_zero V h3 h4 h6 α β hs hp g₂)) (node_den_ne_zero V h3 h4 h6 α β hs hp g₃)
  ext
  simp only [nodeVal, Units.val_mul, Units.val_mk0, Units.val_one]
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq hD0, hN, hD]

def nodeHom : V.toAffine.Point →+ Additive Lˣ :=
  AddMonoidHom.mk' (fun P => Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp P))
    (map_add_of_triple (V := V) (fun P => Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp P)) rfl
      (nodeVal_neg V h3 h4 h6 α β hs hp) (nodeVal_triple V h3 h4 h6 α β hs hp))

theorem nodeHom_injective (hαβ : α ≠ β) : Function.Injective (nodeHom V h3 h4 h6 α β hs hp) := by
  rw [injective_iff_map_eq_zero]
  rintro (_ | ⟨x, y, h⟩) hP
  · rfl
  · exfalso
    change Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ h)) = Additive.ofMul 1 at hP
    have hv := congrArg Units.val (Additive.ofMul.injective hP)
    simp only [nodeVal, Units.val_mk0, Units.val_one] at hv
    rw [div_eq_one_iff_eq (node_den_ne_zero V h3 h4 h6 α β hs hp h)] at hv
    have hx : (α - β) * ι x = 0 := by linear_combination -hv
    rcases mul_eq_zero.1 hx with h0 | h0
    · exact hαβ (sub_eq_zero.1 h0)
    · exact origin_x_ne_zero V h3 h4 h6 h ((map_eq_zero _).1 h0)

end Node

section NodeSplit

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) (α β : F) (hs : algebraMap F F V.a₁ = -(α + β))
  (hp : algebraMap F F V.a₂ = -(α * β))
include h3 h4 h6 hs hp

theorem node_point_of_value {u : F} (hαβ : α ≠ β) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ x y : F, V.toAffine.Nonsingular x y ∧ (y - α * x) / (y - β * x) = u := by
  have hs' : V.a₁ = -(α + β) := hs
  have hp' : V.a₂ = -(α * β) := hp
  have h1u : (1 : F) - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu1)
  have hab : α - β ≠ 0 := sub_ne_zero.2 hαβ
  set t := (α - u * β) / (1 - u)
  have hta : t - α = u * (α - β) / (1 - u) := by simp only [t]; field_simp; ring
  have htb : t - β = (α - β) / (1 - u) := by simp only [t]; field_simp; ring
  have hx : (t - α) * (t - β) ≠ 0 := by
    rw [hta, htb]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hu0 hab) h1u) (div_ne_zero hab h1u)
  have he : V.toAffine.Equation ((t - α) * (t - β)) (t * ((t - α) * (t - β))) := by
    rw [equation_iff, h3, h4, h6, hs', hp']
    ring
  refine ⟨_, _, origin_nonsingular V h3 h4 h6 he hx, ?_⟩
  rw [show t * ((t - α) * (t - β)) - α * ((t - α) * (t - β)) = (t - α) * ((t - α) * (t - β)) by ring,
    show t * ((t - α) * (t - β)) - β * ((t - α) * (t - β)) = (t - β) * ((t - α) * (t - β)) by ring,
    mul_div_mul_right _ _ hx, hta, htb]
  field_simp

def nodeEquiv (hαβ : α ≠ β) : V.toAffine.Point ≃+ Additive Fˣ :=
  AddEquiv.ofBijective (nodeHom V h3 h4 h6 α β hs hp) ⟨nodeHom_injective V h3 h4 h6 α β hs hp hαβ,
    by
      intro z
      by_cases hz : Additive.toMul z = 1
      · exact ⟨0, by rw [map_zero]; exact (Additive.toMul.injective (hz.trans rfl)).symm⟩
      · obtain ⟨x, y, h, hv⟩ := node_point_of_value V h3 h4 h6 α β hs hp hαβ
          (Additive.toMul z).ne_zero (fun h1 => hz (Units.ext h1))
        refine ⟨.some _ _ h, ?_⟩
        change Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ h)) = z
        rw [← ofMul_toMul z]
        congr 1
        ext
        simp only [nodeVal, Units.val_mk0, Algebra.algebraMap_self, RingHom.id_apply]
        exact hv⟩

end NodeSplit

section Torus

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) {L : Type*} [Field L] [Algebra F L] (α β : L)
  (hs : algebraMap F L V.a₁ = -(α + β)) (hp : algebraMap F L V.a₂ = -(α * β)) (σ : L ≃ₐ[F] L)

def normOne : Subgroup Lˣ where
  carrier := {u | (u : L) * σ u = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at *
    linear_combination (b : L) * σ b * ha + hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
    rw [← mul_inv, ha, inv_one]

local notation "ι" => algebraMap F L

include h3 h4 h6 hs hp

theorem nodeVal_mem (hσ : σ α = β) (P : V.toAffine.Point) :
    nodeVal V h3 h4 h6 α β hs hp P ∈ normOne σ := by
  have hσβ : σ β = α := by
    have h1 : σ (α + β) = α + β := by
      rw [← neg_neg (α + β), ← hs, map_neg, AlgEquiv.commutes]
    rw [map_add, hσ] at h1
    linear_combination h1
  rcases P with _ | ⟨x, y, h⟩
  · simp [nodeVal, normOne]
  · simp only [normOne, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
      nodeVal, Units.val_mk0, map_div₀, map_sub, map_mul, AlgEquiv.commutes, hσ, hσβ]
    rw [div_mul_div_comm, mul_comm (ι y - β * ι x), div_self (mul_ne_zero
      (node_num_ne_zero V h3 h4 h6 α β hs hp h) (node_den_ne_zero V h3 h4 h6 α β hs hp h))]

def nodeTorusHom (hσ : σ α = β) : V.toAffine.Point →+ Additive (normOne σ) :=
  AddMonoidHom.mk' (fun P => Additive.ofMul ⟨nodeVal V h3 h4 h6 α β hs hp P,
    nodeVal_mem V h3 h4 h6 α β hs hp σ hσ P⟩) (fun P Q => by
      have := (nodeHom V h3 h4 h6 α β hs hp).map_add P Q
      change Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _ at this
      rw [← ofMul_mul] at this ⊢
      congr 1
      exact Subtype.ext (Additive.ofMul.injective this))

def nodeTorusEquiv (hαβ : α ≠ β) (hσ : σ α = β)
    (hfix : ∀ z : L, σ z = z → ∃ a : F, ι a = z) :
    V.toAffine.Point ≃+ Additive (normOne σ) :=
  AddEquiv.ofBijective (nodeTorusHom V h3 h4 h6 α β hs hp σ hσ) ⟨fun P Q hPQ => by
      apply nodeHom_injective V h3 h4 h6 α β hs hp hαβ
      have := congrArg (fun z => ((Additive.toMul z : normOne σ) : Lˣ)) hPQ
      exact congrArg Additive.ofMul this, by
    intro z
    set u : Lˣ := ((Additive.toMul z : normOne σ) : Lˣ) with hu
    have hum : (u : L) * σ u = 1 := (Additive.toMul z).2
    by_cases h1 : u = 1
    · refine ⟨0, ?_⟩
      rw [map_zero, ← ofMul_toMul z]
      change Additive.ofMul 1 = _
      congr 1
      exact Subtype.ext h1.symm
    have hσβ : σ β = α := by
      have h1 : σ (α + β) = α + β := by
        rw [← neg_neg (α + β), ← hs, map_neg, AlgEquiv.commutes]
      rw [map_add, hσ] at h1
      linear_combination h1
    have hu0 : (u : L) ≠ 0 := u.ne_zero
    have hu1 : (1 : L) - u ≠ 0 := sub_ne_zero.2 (fun h => h1 (Units.ext h.symm))
    have hσu : σ u = (u : L)⁻¹ := eq_inv_of_mul_eq_one_right hum
    have hu1' : -1 + (u : L) ≠ 0 := by intro h; apply hu1; linear_combination -h
    have hu1'' : (u : L) - 1 ≠ 0 := by intro h; apply hu1; linear_combination -h
    have hσu1 : (1 : L) - σ u ≠ 0 := by
      rw [hσu]; intro h; apply hu1; field_simp at h ⊢; linear_combination -h
    have hab : α - β ≠ 0 := sub_ne_zero.2 hαβ
    set t := (α - u * β) / (1 - u) with ht
    have hσt : σ t = t := by
      rw [ht, map_div₀, map_sub, map_sub, map_mul, map_one, hσ, hσβ, hσu]
      field_simp
      ring
    obtain ⟨t₀, ht₀⟩ := hfix t hσt
    have hta : t - α = u * (α - β) / (1 - u) := by rw [ht]; field_simp; ring
    have htb : t - β = (α - β) / (1 - u) := by rw [ht]; field_simp; ring
    set x₀ := t₀ ^ 2 + V.a₁ * t₀ - V.a₂
    have hx₀ : ι x₀ = (t - α) * (t - β) := by
      simp only [x₀, map_sub, map_add, map_mul, map_pow, hs, hp, ht₀]; ring
    have hx0 : x₀ ≠ 0 := by
      intro h0
      have : ι x₀ = 0 := by rw [h0, map_zero]
      rw [hx₀, hta, htb] at this
      exact mul_ne_zero (div_ne_zero (mul_ne_zero hu0 hab) hu1) (div_ne_zero hab hu1) this
    have he : V.toAffine.Equation x₀ (t₀ * x₀) := by
      rw [equation_iff, h3, h4, h6]
      simp only [x₀]
      ring
    have hn := origin_nonsingular V h3 h4 h6 he hx0
    refine ⟨.some _ _ hn, ?_⟩
    rw [← ofMul_toMul z]
    change Additive.ofMul _ = Additive.ofMul _
    congr 1
    apply Subtype.ext
    apply Units.ext
    change (ι (t₀ * x₀) - α * ι x₀) / (ι (t₀ * x₀) - β * ι x₀) = u
    have hx0L : ι x₀ ≠ 0 := (map_ne_zero _).2 hx0
    rw [map_mul, ht₀, show t * ι x₀ - α * ι x₀ = (t - α) * ι x₀ by ring,
      show t * ι x₀ - β * ι x₀ = (t - β) * ι x₀ by ring, mul_div_mul_right _ _ hx0L, hta, htb]
    field_simp⟩

end Torus

end

end GroundTheory.Arith.Abelian
