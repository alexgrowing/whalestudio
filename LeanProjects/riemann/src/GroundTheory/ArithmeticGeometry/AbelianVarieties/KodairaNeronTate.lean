import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronSplitVal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing IsDiscreteValuationRing

noncomputable section

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]

local notation "ι" => algebraMap 𝒪 K
local notation "v" => addVal 𝒪

def iotaPt : (curveK K W).Point → ZMod (v W.a₆).toNat
  | 0 => 0
  | .some X Y _ => iotaN (v W.a₆).toNat (v (intPart K Y)) (v (intPart K Y + W.a₁ * intPart K X))

open Classical in

def phiT (P : (curveK K W).Point) : ZMod (v W.a₆).toNat :=
  if P ∈ E0Set K W then 0 else iotaPt K W P

theorem phiT_of_mem {P : (curveK K W).Point} (h : P ∈ E0Set K W) : phiT K W P = 0 := by
  simp [phiT, h]

theorem phiT_some {x y : 𝒪} (h : (curveK K W).Nonsingular (ι x) (ι y))
    (hP : Point.some _ _ h ∉ E0Set K W) :
    phiT K W (.some _ _ h) = iotaN (v W.a₆).toNat (v y) (v (y + W.a₁ * x)) := by
  simp only [phiT, hP, if_false, iotaPt, intPart_algebraMap]

variable {π : 𝒪} (hπ : Irreducible π)

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in
include hπ in
theorem isUnit_iff_not_dvd {a : 𝒪} : IsUnit a ↔ ¬π ∣ a := by
  rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, mem_maximalIdeal, mem_nonunits_iff,
    not_not]

theorem natCast_ne_zero_of_lt {n b : ℕ} (h1 : 1 ≤ b) (h2 : b < n) : ((b : ℕ) : ZMod n) ≠ 0 := by
  intro h
  rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
  exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

section Hensel

include hπ

theorem exists_root_cubic {α β γ δ : 𝒪} (hγ : IsUnit γ) (hδ : π ∣ δ) :
    ∃ Z, π ∣ Z ∧ α * Z ^ 3 + β * Z ^ 2 + γ * Z + δ = 0 := by
  open Polynomial in
  have hm : ∀ {a : 𝒪}, π ∣ a → a ∈ IsLocalRing.maximalIdeal 𝒪 := fun {a} h => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]; exact h
  have hu : ∀ {a : 𝒪}, IsUnit a → ∀ {b : 𝒪}, π ∣ b → IsUnit (a + b) := fun {a} ha {b} hb => by
    rw [isUnit_iff_not_dvd hπ] at ha ⊢
    intro h; exact ha (by have := dvd_sub h hb; rwa [add_sub_cancel_right] at this)
  obtain ⟨c1, hc1⟩ : ∃ c, c = β * δ := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c, c = α * δ ^ 2 := ⟨_, rfl⟩
  set f : Polynomial 𝒪 := X ^ 3 + C γ * X ^ 2 + C c1 * X + C c0 with hfdef
  have hf : f.Monic := by rw [hfdef]; monicity!
  have hev : ∀ V : 𝒪, f.eval V = V ^ 3 + γ * V ^ 2 + β * δ * V + α * δ ^ 2 := fun V => by
    simp [hfdef, hc0, hc1]
  have hder : ∀ V : 𝒪, f.derivative.eval V = 3 * V ^ 2 + 2 * γ * V + β * δ := fun V => by
    simp [hfdef, hc1]; ring
  obtain ⟨V, hV, hVm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal 𝒪) f hf (-γ)
    (by
      rw [hev]
      apply hm
      rw [show (-γ) ^ 3 + γ * (-γ) ^ 2 + β * δ * -γ + α * δ ^ 2 = δ * (-β * γ + α * δ) by ring]
      exact dvd_mul_of_dvd_left hδ _)
    (by
      rw [hder]
      apply IsUnit.map
      rw [show 3 * (-γ) ^ 2 + 2 * γ * -γ + β * δ = γ ^ 2 + β * δ by ring]
      exact hu (hγ.pow 2) (dvd_mul_of_dvd_right hδ β))
  have hV' : V ^ 3 + γ * V ^ 2 + β * δ * V + α * δ ^ 2 = 0 := by rw [← hev]; exact hV
  have hVu : IsUnit V := by
    have h1 : π ∣ V - -γ := by
      rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hVm
    have := hu (hγ.neg) h1
    convert this using 1; ring
  obtain ⟨Wv, hWv⟩ : ∃ Wv, V * Wv = 1 := ⟨_, hVu.mul_val_inv⟩
  refine ⟨δ * Wv, dvd_mul_of_dvd_left hδ _, ?_⟩
  linear_combination (δ * Wv ^ 3) * hV' -
    (β * δ ^ 2 * Wv ^ 2 + γ * δ * Wv * (V * Wv + 1) + δ * ((V * Wv) ^ 2 + V * Wv + 1)) * hWv

end Hensel

theorem zmod_two_eq_one {N : ℕ} (hN : N = 2) {z : ZMod N} (hz : z ≠ 0) : z = 1 := by
  subst hN
  fin_cases z
  · exact absurd rfl hz
  · rfl

section Hom

variable {W} (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (he : IsUnit W.a₁)
  (hq : π ∣ W.a₆)
include h2 h3 h4

omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic] in
theorem tate_eq {x y : 𝒪} (h : W.toAffine.Equation x y) :
    y * (y + W.a₁ * x) = x ^ 3 + W.a₆ := by
  rw [equation_iff, h2, h3, h4] at h
  linear_combination h

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
include K in
theorem a₆_ne_zero : W.a₆ ≠ 0 := by
  intro h0
  apply Δ_ne_zero_of_isElliptic K W
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h2, h3, h4, h0]
  ring

include hπ hq he

theorem phiT_neg (P : (curveK K W).Point) : phiT K W (-P) = -phiT K W P := by
  by_cases hP : P ∈ E0Set K W
  · rw [phiT_of_mem K W hP, phiT_of_mem K W (show -P ∈ E0 K W from (E0 K W).neg_mem hP),
      neg_zero]
  obtain ⟨x, y, h, rfl, e, dx, dy⟩ :=
    exists_of_notMem_E0Set K W hπ (by rw [h3]; exact dvd_zero _) (by rw [h4]; exact dvd_zero _) hq hP
  obtain ⟨hn, hneg⟩ := neg_some_integral K W h
  have hP' := neg_notMem_E0Set K W hP
  rw [hneg] at hP' ⊢
  rw [phiT_some K W h hP, phiT_some K W hn hP', h3, sub_zero,
    show -y - W.a₁ * x + W.a₁ * x = -y by ring, AddValuation.map_neg,
    show -y - W.a₁ * x = -(y + W.a₁ * x) by ring, AddValuation.map_neg]
  exact iotaN_swap fun ht => by
    rw [tie_two hπ he (a₆_ne_zero K h2 h3 h4) (tate_eq h2 h3 h4 e) dy ht,
      ENat.natCast_toNat (v_ne_top (a₆_ne_zero K h2 h3 h4))]

include K in

theorem iota_neg_data {x y : 𝒪} (e' : W.toAffine.Equation x y) (dy : π ∣ y) :
    iotaN (v W.a₆).toNat (v (-(y + W.a₁ * x))) (v (-(y + W.a₁ * x) + W.a₁ * x)) =
      -iotaN (v W.a₆).toNat (v y) (v (y + W.a₁ * x)) := by
  rw [AddValuation.map_neg, show -(y + W.a₁ * x) + W.a₁ * x = -y by ring, AddValuation.map_neg]
  exact iotaN_swap fun ht => by
    rw [tie_two hπ he (a₆_ne_zero K h2 h3 h4) (tate_eq h2 h3 h4 e') dy ht,
      ENat.natCast_toNat (v_ne_top (a₆_ne_zero K h2 h3 h4))]

theorem phiT_three {P Q R : (curveK K W).Point} (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W)
    (hR : R ∉ E0Set K W) (hs : P + Q + R = 0) : phiT K W P + phiT K W Q + phiT K W R = 0 := by
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩, ⟨g₃, rfl⟩, e₁, e₂, e₃, dx₁, dy₁, dx₂,
    dy₂, dx₃, dy₃, l1, l2, l3, v1, v2, v3⟩ := triple_origin K W hπ d3 d4 hq hP hQ hR hs
  rw [phiT_some K W g₁ hP, phiT_some K W g₂ hQ, phiT_some K W g₃ hR]
  have hq0 := a₆_ne_zero K h2 h3 h4
  rw [h2] at v1
  rw [h3, h4] at v2
  rw [h3] at v3
  have E₁ := tate_eq h2 h3 h4 e₁
  have E₂ := tate_eq h2 h3 h4 e₂
  have E₃ := tate_eq h2 h3 h4 e₃
  have hv3 : x₁ * x₂ * x₃ = ν ^ 2 - W.a₆ := by linear_combination v3
  have hσ : π ∣ ℓ * (ℓ + W.a₁) := by
    rw [show ℓ * (ℓ + W.a₁) = x₁ + x₂ + x₃ by linear_combination -v1]
    exact dvd_add (dvd_add dx₁ dx₂) dx₃
  have hne : ¬π ∣ W.a₁ := (isUnit_iff_not_dvd hπ).1 he
  rcases hπ.prime.dvd_or_dvd hσ with hℓ | hℓe
  · have hu : IsUnit (ℓ + W.a₁) := (isUnit_iff_not_dvd hπ).2 fun h => hne (by
      have := dvd_sub h hℓ; rwa [add_sub_cancel_left] at this)
    have hvw : (y₁ + W.a₁ * x₁) * (y₂ + W.a₁ * x₂) * (y₃ + W.a₁ * x₃) =
        ν ^ 3 - (ℓ + W.a₁) ^ 3 * W.a₆ := by
      rw [l1, l2, l3]
      linear_combination (ℓ + W.a₁) ^ 3 * v3 + (ℓ + W.a₁) ^ 2 * ν * v2 + (ℓ + W.a₁) * ν ^ 2 * v1
    exact iota_triple hπ hq0 hℓ hu E₁ E₂ E₃ dx₁ dx₂ dx₃ dy₁ l1 l2 l3 hv3 hvw
  · have hℓu : IsUnit (-ℓ) := (isUnit_iff_not_dvd hπ).2 fun h => hne (by
      have := dvd_add hℓe h; rwa [show ℓ + W.a₁ + -ℓ = W.a₁ by ring] at this)
    have neg_eq : ∀ {x y : 𝒪}, y * (y + W.a₁ * x) = x ^ 3 + W.a₆ →
        -(y + W.a₁ * x) * (-(y + W.a₁ * x) + W.a₁ * x) = x ^ 3 + W.a₆ := by
      intro x y h; linear_combination h
    have hvw : (-(y₁ + W.a₁ * x₁) + W.a₁ * x₁) * (-(y₂ + W.a₁ * x₂) + W.a₁ * x₂) *
        (-(y₃ + W.a₁ * x₃) + W.a₁ * x₃) = (-ν) ^ 3 - (-(ℓ + W.a₁) + W.a₁) ^ 3 * W.a₆ := by
      rw [l1, l2, l3]
      linear_combination (-ℓ ^ 3) * v3 - ℓ ^ 2 * ν * v2 - ℓ * ν ^ 2 * v1
    have := iota_triple hπ hq0 (ℓ := -(ℓ + W.a₁)) (ν := -ν) (dvd_neg.2 hℓe)
      (by rwa [show -(ℓ + W.a₁) + W.a₁ = -ℓ by ring]) (neg_eq E₁) (neg_eq E₂) (neg_eq E₃) dx₁ dx₂
      dx₃ (dvd_neg.2 (dvd_add dy₁ (dvd_mul_of_dvd_right dx₁ _))) (by rw [l1]; ring) (by rw [l2]; ring)
      (by rw [l3]; ring) (by rw [hv3]; ring) hvw
    rw [iota_neg_data K hπ h2 h3 h4 he hq (equation_of_map K W g₁.1) dy₁,
      iota_neg_data K hπ h2 h3 h4 he hq (equation_of_map K W g₂.1) dy₂,
      iota_neg_data K hπ h2 h3 h4 he hq (equation_of_map K W g₃.1) dy₃] at this
    rw [← neg_eq_zero, neg_add, neg_add]
    exact this

theorem phiT_pair_int {P Q : (curveK K W).Point} {xT yT : 𝒪}
    {hT : (curveK K W).Nonsingular (ι xT) (ι yT)} (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W)
    (hTm : Point.some _ _ hT ∈ E0Set K W) (hs : P + Q + Point.some _ _ hT = 0) :
    phiT K W P + phiT K W Q = 0 := by
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨xP, yP, gP, rfl, eP, dxP, dyP⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hP
  obtain ⟨xQ, yQ, gQ, rfl, eQ, dxQ, dyQ⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hQ
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_integral_line K W gP gQ hT hs
  rw [phiT_some K W gP hP, phiT_some K W gQ hQ]
  rw [h2] at v1
  rw [h3, h4] at v2
  rw [h3] at v3
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hTn : (curveRed W).Nonsingular (residue 𝒪 xT) (residue 𝒪 yT) := hTm xT yT hT rfl
  have hν : π ∣ ν := by
    rw [show ν = yP - ℓ * xP by rw [l1]; ring]
    exact dvd_sub dyP (dvd_mul_of_dvd_right dxP _)
  have hxT : ¬π ∣ xT := by
    intro hx
    have hy : π ∣ yT := by rw [l3]; exact dvd_add (dvd_mul_of_dvd_right hx _) hν
    exact singular_of_dvd_origin W hπ d3 d4 hx hy hTn
  have hprod : ¬π ∣ ℓ * (ℓ + W.a₁) := by
    intro h
    apply hxT
    rw [show xT = ℓ * (ℓ + W.a₁) - xP - xQ by linear_combination v1]
    exact dvd_sub (dvd_sub h dxP) dxQ
  have hℓ : IsUnit ℓ := (isUnit_iff_not_dvd hπ).2 fun h => hprod (dvd_mul_of_dvd_left h _)
  have hℓe : IsUnit (ℓ + W.a₁) := (isUnit_iff_not_dvd hπ).2 fun h => hprod (dvd_mul_of_dvd_right h _)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = ν * ↑hℓ.unit⁻¹ := ⟨_, rfl⟩
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ', ρ' = ν * ↑hℓe.unit⁻¹ := ⟨_, rfl⟩
  have hρ : ℓ * ρ = ν := by
    rw [hρdef, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have hρ' : (ℓ + W.a₁) * ρ' = ν := by
    rw [hρ'def, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have dρ : π ∣ ρ := hρdef ▸ dvd_mul_of_dvd_left hν _
  have dρ' : π ∣ ρ' := hρ'def ▸ dvd_mul_of_dvd_left hν _
  have unitU : ∀ {r : 𝒪}, π ∣ r → IsUnit (-(xT + r)) := fun {r} hr =>
    (isUnit_iff_not_dvd hπ).2 fun h => hxT (by
      have := dvd_sub (dvd_neg.1 h) hr; rwa [add_sub_cancel_right] at this)
  refine iota_pair (μ := 1) (l := ℓ) (l' := ℓ + W.a₁) (ρ := ρ) (ρ' := ρ') (U := -(xT + ρ))
    (U' := -(xT + ρ')) (xP := xP) (yP := yP) (xR := xQ) (yR := yQ)
    hπ he hq0 hℓ hℓe (unitU dρ) (unitU dρ') one_ne_zero (tate_eq h2 h3 h4 eP)
    (tate_eq h2 h3 h4 eQ) dxP dyP dyQ (by rw [l1]; linear_combination -hρ) (by
      rw [l1]; linear_combination -hρ') (by rw [l2]; linear_combination -hρ)
    (by rw [l2]; linear_combination -hρ') ?_ ?_ (by ring) (by rw [hρ, hρ'])
  · linear_combination ρ ^ 2 * v1 + ρ * v2 + v3 + (ℓ * ρ - ν + W.a₁ * ρ) * hρ
  · linear_combination ρ' ^ 2 * v1 + ρ' * v2 + v3 + (ℓ * ρ' - ν) * hρ'

theorem componentIndex_pair_nonintegral {P Q : (curveK K W).Point} {X Y : K} {hT : (curveK K W).Nonsingular X Y}
    (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W) (hX : X ∉ Set.range ι)
    (hs : P + Q + Point.some _ _ hT = 0) : phiT K W P + phiT K W Q = 0 := by
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨xP, yP, gP, rfl, eP, dxP, dyP⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hP
  obtain ⟨xQ, yQ, gQ, rfl, eQ, dxQ, dyQ⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hQ
  obtain ⟨L, N, l1, l2, -, v1, v2, v3⟩ := exists_line_of_add_eq_zero gP gQ hT hs
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, h2, h3, h4, map_zero] at v1 v2 v3
  rw [phiT_some K W gP hP, phiT_some K W gQ hQ]
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hinj := IsFractionRing.injective 𝒪 K
  have hL : L ∉ Set.range ι := by
    rintro ⟨ℓ, rfl⟩
    apply hX
    exact ⟨ℓ ^ 2 + W.a₁ * ℓ - xP - xQ, by
      simp only [map_sub, map_add, map_mul, map_pow]; linear_combination -v1⟩
  obtain ⟨μ, hμm, hμ⟩ := exists_inv_mem_of_notMem_range K hL
  have hL0 : L ≠ 0 := by rintro rfl; exact hL ⟨0, map_zero _⟩
  have hμL : ι μ * L = 1 := by rw [hμ, inv_mul_cancel₀ hL0]
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at hμL; exact zero_ne_one hμL
  have dμ : π ∣ μ := by
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hμm
  obtain ⟨ν', hν'def⟩ : ∃ ν', ν' = μ * yP - xP := ⟨_, rfl⟩
  have hνK : ι ν' = ι μ * N := by
    rw [hν'def, map_sub, map_mul]
    linear_combination (ι μ) * l1 + (ι xP) * hμL
  have lQ : μ * yQ = 1 * (xQ + ν') := by
    apply hinj
    simp only [map_mul, map_add, one_mul]
    rw [hνK]
    linear_combination (ι μ) * l2 + (ι xQ) * hμL
  obtain ⟨T', hTdef⟩ : ∃ T', T' = 1 + W.a₁ * μ - μ ^ 2 * (xP + xQ) := ⟨_, rfl⟩
  have hTK : ι T' = (ι μ) ^ 2 * X := by
    rw [hTdef]
    simp only [map_sub, map_add, map_mul, map_pow, map_one]
    linear_combination (-(ι μ * L + 1) - ι W.a₁ * ι μ) * hμL - (ι μ) ^ 2 * v1
  have S2 : μ ^ 2 * (xP * xQ) + T' * (xP + xQ) = -(2 + W.a₁ * μ) * ν' := by
    apply hinj
    simp only [map_mul, map_add, map_neg, map_pow, map_ofNat]
    rw [hTK, hνK]
    linear_combination (ι μ) ^ 2 * v2 - 2 * ι μ * N * hμL
  have S3 : xP * xQ * T' = ν' ^ 2 - μ ^ 2 * W.a₆ := by
    apply hinj
    simp only [map_mul, map_sub, map_pow]
    rw [hTK, hνK]
    linear_combination (ι μ) ^ 2 * v3
  have hl' : IsUnit (1 + W.a₁ * μ) := (isUnit_iff_not_dvd hπ).2 fun h => hπ.not_isUnit
    (isUnit_of_dvd_one (by have := dvd_sub h (dvd_mul_of_dvd_right dμ W.a₁); rwa [add_sub_cancel_right] at this))
  have dT : π ∣ T' - 1 := by
    rw [hTdef, show 1 + W.a₁ * μ - μ ^ 2 * (xP + xQ) - 1 = μ * (W.a₁ - μ * (xP + xQ)) by ring]
    exact dvd_mul_of_dvd_left dμ _
  have unitU : ∀ {r : 𝒪}, IsUnit (-(μ ^ 2 * r + T')) := fun {r} =>
    (isUnit_iff_not_dvd hπ).2 fun h => hπ.not_isUnit (isUnit_of_dvd_one (by
      have := dvd_add (dvd_add (dvd_neg.1 h) (dvd_neg.2 dT))
        (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow dμ two_ne_zero) r))
      convert this using 1; ring))
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ', ρ' = ν' * ↑hl'.unit⁻¹ := ⟨_, rfl⟩
  have hρ' : (1 + W.a₁ * μ) * ρ' = ν' := by
    rw [hρ'def, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  refine iota_pair (μ := μ) (l := 1) (l' := 1 + W.a₁ * μ) (ρ := ν') (ρ' := ρ')
    (U := -(μ ^ 2 * ν' + T')) (U' := -(μ ^ 2 * ρ' + T')) (xP := xP) (yP := yP) (xR := xQ)
    (yR := yQ) hπ he hq0 isUnit_one hl' unitU unitU hμ0 (tate_eq h2 h3 h4 eP)
    (tate_eq h2 h3 h4 eQ) dxP dyP dyQ (by rw [hν'def]; ring) (by linear_combination -hρ' - hν'def)
    lQ (by linear_combination lQ - hρ') ?_ ?_ (by ring) (by rw [one_mul, hρ'])
  · linear_combination ν' * S2 + S3 + ν' ^ 2 * hTdef
  · linear_combination ρ' * S2 + S3 + ρ' ^ 2 * hTdef + (ρ' - ν') * hρ'

theorem phiT_pair {P Q T : (curveK K W).Point} (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W)
    (hT : T ∈ E0Set K W) (hs : P + Q + T = 0) : phiT K W P + phiT K W Q = 0 := by
  rcases T with _ | ⟨X, Y, hT'⟩
  · have hQP : Q = -P := by
      change P + Q + 0 = 0 at hs
      rw [add_zero] at hs
      exact (neg_eq_of_add_eq_zero_right hs).symm
    rw [hQP, phiT_neg K hπ h2 h3 h4 he hq, add_neg_cancel]
  · by_cases hX : X ∈ Set.range ι
    · obtain ⟨xT, rfl⟩ := hX
      obtain ⟨yT, rfl⟩ := exists_y_of_equation K W hT'.1
      exact phiT_pair_int K hπ h2 h3 h4 he hq hP hQ hT hs
    · exact componentIndex_pair_nonintegral K hπ h2 h3 h4 he hq hP hQ hX hs

theorem componentIndex_sum_three {P Q R : (curveK K W).Point} (hs : P + Q + R = 0) :
    phiT K W P + phiT K W Q + phiT K W R = 0 := by
  have mem : ∀ {A B C : (curveK K W).Point}, A + B + C = 0 → B ∈ E0Set K W → C ∈ E0Set K W →
      A ∈ E0Set K W := by
    intro A B C h hB hC
    have : A = -(B + C) := by rw [← sub_eq_zero, sub_neg_eq_add, ← add_assoc]; exact h
    rw [this]
    exact (E0 K W).neg_mem ((E0 K W).add_mem hB hC)
  have hs₁ : Q + R + P = 0 := by rw [← hs]; abel
  have hs₂ : R + P + Q = 0 := by rw [← hs]; abel
  have hs₃ : P + R + Q = 0 := by rw [← hs]; abel
  by_cases hP : P ∈ E0Set K W <;> by_cases hQ : Q ∈ E0Set K W <;> by_cases hR : R ∈ E0Set K W
  · simp [phiT_of_mem K W hP, phiT_of_mem K W hQ, phiT_of_mem K W hR]
  · exact absurd (mem hs₂ hP hQ) hR
  · exact absurd (mem hs₁ hR hP) hQ
  · rw [phiT_of_mem K W hP, zero_add]
    exact phiT_pair K hπ h2 h3 h4 he hq hQ hR hP hs₁
  · exact absurd (mem hs hQ hR) hP
  · rw [phiT_of_mem K W hQ, add_zero]
    exact phiT_pair K hπ h2 h3 h4 he hq hP hR hQ hs₃
  · rw [phiT_of_mem K W hR, add_zero]
    exact phiT_pair K hπ h2 h3 h4 he hq hP hQ hR hs
  · exact phiT_three K hπ h2 h3 h4 he hq hP hQ hR hs

theorem phiT_add (P Q : (curveK K W).Point) : phiT K W (P + Q) = phiT K W P + phiT K W Q := by
  have h := componentIndex_sum_three K hπ h2 h3 h4 he hq (show P + Q + -(P + Q) = 0 by abel)
  rw [phiT_neg K hπ h2 h3 h4 he hq] at h
  linear_combination -h

def phiTHom : (curveK K W).Point →+ ZMod (v W.a₆).toNat :=
  AddMonoidHom.mk' (phiT K W) (phiT_add K hπ h2 h3 h4 he hq)

include K in
theorem one_le_n : 1 ≤ (v W.a₆).toNat := by
  have h1 := (one_le_v_iff hπ).2 hq
  have ht := v_ne_top (a₆_ne_zero K h2 h3 h4)
  lift v W.a₆ to ℕ using ht with n hn
  simp only [ENat.toNat_natCast]
  exact_mod_cast h1

theorem phiT_eq_zero_iff (P : (curveK K W).Point) : phiT K W P = 0 ↔ P ∈ E0Set K W := by
  refine ⟨fun h => ?_, phiT_of_mem K W⟩
  by_contra hP
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨x, y, g, rfl, e', dx, dy⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hP
  rw [phiT_some K W g hP] at h
  have E := tate_eq h2 h3 h4 e'
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hn : v W.a₆ = ((v W.a₆).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq0)).symm
  have hn1 := one_le_n K hπ h2 h3 h4 he hq
  set n := (v W.a₆).toNat
  have ha1 : 1 ≤ v y := (one_le_v_iff hπ).2 dy
  have hb1 : 1 ≤ v (y + W.a₁ * x) := (one_le_v_iff hπ).2 (dvd_add dy (dvd_mul_of_dvd_right dx _))
  have hsum := v_sum_eq E
  obtain ⟨hmin, -⟩ := v_x_of (x := x) (y := y) he
  obtain ⟨-, c2, -⟩ := v_cube_add x W.a₆
  rw [hn] at c2

  have key : ∀ {c : ℕ∞}, c = min (v y) (v (y + W.a₁ * x)) → (n : ℕ∞) ≤ c →
      v y + v (y + W.a₁ * x) = n := by
    intro c hc hcn
    rw [hsum]
    apply c2
    calc (n : ℕ∞) < 3 * n := by
          have : (n : ℕ∞) < 3 * (n : ℕ∞) := by
            have : n < 3 * n := by have := hn1; omega
            exact_mod_cast this
          exact this
      _ ≤ 3 * c := by gcongr
      _ ≤ 3 * v x := by gcongr; exact hc ▸ hmin
  have fin : v y + v (y + W.a₁ * x) = n → v y ≠ ⊤ ∧ v (y + W.a₁ * x) ≠ ⊤ := by
    intro hs'
    constructor <;> intro ht <;> rw [ht] at hs' <;> simp at hs'
  rcases le_or_gt (v (y + W.a₁ * x)) (v y) with hba | hab
  · rw [iotaN_of_le hba] at h
    have hbt : v (y + W.a₁ * x) ≠ ⊤ := by
      intro ht
      have hat : v y = ⊤ := top_le_iff.1 (ht ▸ hba)
      have hxt : v x = ⊤ := top_le_iff.1 (by rw [ht, hat, min_self] at hmin; exact hmin)
      have hx0 := addVal_eq_top_iff.1 hxt
      have hy0 := addVal_eq_top_iff.1 hat
      apply hq0
      rw [hx0, hy0] at E
      linear_combination -E
    have hlt : v (y + W.a₁ * x) < n := by
      by_contra hge
      push Not at hge
      have h' := key (by rw [min_eq_right hba]) hge
      obtain ⟨hat, -⟩ := fin h'
      lift v y to ℕ using hat with a ha
      lift v (y + W.a₁ * x) to ℕ using hbt with b hb
      have e1 : a + b = n := by exact_mod_cast h'
      have e2 : n ≤ b := by exact_mod_cast hge
      have e3 : b ≤ a := by exact_mod_cast hba
      omega
    lift v (y + W.a₁ * x) to ℕ using hbt with b hb
    simp only [ENat.toNat_natCast] at h
    exact natCast_ne_zero_of_lt (by exact_mod_cast hb1) (by exact_mod_cast hlt) h
  · rw [iotaN_of_lt hab, neg_eq_zero] at h
    have hat : v y ≠ ⊤ := hab.ne_top
    have hlt : v y < n := by
      by_contra hge
      push Not at hge
      have h' := key (by rw [min_eq_left hab.le]) hge
      obtain ⟨-, hbt⟩ := fin h'
      lift v y to ℕ using hat with a ha
      lift v (y + W.a₁ * x) to ℕ using hbt with b hb
      have e1 : a + b = n := by exact_mod_cast h'
      have e2 : n ≤ a := by exact_mod_cast hge
      have e3 : a < b := by exact_mod_cast hab
      omega
    lift v y to ℕ using hat with a ha
    simp only [ENat.toNat_natCast] at h
    exact natCast_ne_zero_of_lt (by exact_mod_cast ha1) (by exact_mod_cast hlt) h

theorem ker_phiTHom : (phiTHom K hπ h2 h3 h4 he hq).ker = E0 K W := by
  ext P
  rw [AddMonoidHom.mem_ker, mem_E0_iff]
  exact phiT_eq_zero_iff K hπ h2 h3 h4 he hq P

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem nonsingular_of_tate {x y : 𝒪} (h : y * (y + W.a₁ * x) = x ^ 3 + W.a₆) :
    (curveK K W).Nonsingular (ι x) (ι y) := by
  apply (equation_iff_nonsingular (W := W.map (algebraMap 𝒪 K))).1
  rw [equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, h2, h3, h4, map_zero]
  have := congrArg (algebraMap 𝒪 K) h
  simp only [map_mul, map_add, map_pow] at this
  linear_combination this

theorem exists_phiT_eq_one (hn2 : 2 ≤ (v W.a₆).toNat) : ∃ P, phiT K W P = 1 := by
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hn : v W.a₆ = ((v W.a₆).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq0)).symm
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  have hpow : ∀ k : ℕ, k ≤ (v W.a₆).toNat → π ^ k ∣ W.a₆ := fun k hk => by
    rw [← addVal_le_iff_dvd, hπ.addVal_pow, hn]; exact_mod_cast hk
  rcases Nat.lt_or_ge (v W.a₆).toNat 3 with h3n | h3n
  ·
    obtain ⟨q₂, hq₂⟩ := hpow 2 hn2
    obtain ⟨X₀, hX₀⟩ : ∃ X₀, W.a₁ * X₀ = q₂ - 1 := ⟨(q₂ - 1) * ↑he.unit⁻¹, by
      rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩
    have hγ : IsUnit (3 * π * X₀ ^ 2 - W.a₁) := by
      rw [isUnit_iff_not_dvd hπ]
      intro h
      apply (isUnit_iff_not_dvd hπ).1 he
      have := dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl π) 3) (X₀ ^ 2)) h
      convert this using 1; ring
    obtain ⟨Z, -, hZ⟩ := exists_root_cubic hπ (α := π) (β := 3 * π * X₀) hγ
      (δ := π * X₀ ^ 3 - W.a₁ * X₀ + q₂ - 1) ⟨X₀ ^ 3, by linear_combination -hX₀⟩
    have heq : π * (π + W.a₁ * (π * (X₀ + Z))) = (π * (X₀ + Z)) ^ 3 + W.a₆ := by
      rw [hq₂]; linear_combination (-π ^ 2) * hZ
    have hpt := nonsingular_of_tate K hπ h2 h3 h4 he hq heq
    have hP := notMem_E0Set_of_dvd K W hπ d3 d4 hpt (dvd_mul_right π _) (dvd_refl π)
    refine ⟨Point.some _ _ hpt, zmod_two_eq_one (by omega) ?_⟩
    rw [Ne, phiT_eq_zero_iff K hπ h2 h3 h4 he hq]
    exact hP
  ·
    obtain ⟨q₃, hq₃⟩ := hpow 3 h3n
    obtain ⟨Y, dY, hY⟩ := exists_root_cubic hπ (α := 0) (β := 1) he
      (δ := -(π * (1 + q₃))) (dvd_neg.2 (dvd_mul_right π _))
    have heq : π * Y * (π * Y + W.a₁ * π) = π ^ 3 + W.a₆ := by
      rw [hq₃]; linear_combination π ^ 2 * hY
    have hpt := nonsingular_of_tate K hπ h2 h3 h4 he hq heq
    have hP := notMem_E0Set_of_dvd K W hπ d3 d4 hpt (dvd_refl π) (dvd_mul_right π _)
    refine ⟨Point.some _ _ hpt, ?_⟩
    rw [phiT_some K W hpt hP]
    have hw : v (π * Y + W.a₁ * π) = 1 := by
      rw [show π * Y + W.a₁ * π = π * (Y + W.a₁) by ring, addVal_mul, addVal_uniformizer hπ,
        v_unit ((isUnit_iff_not_dvd hπ).2 fun h => (isUnit_iff_not_dvd hπ).1 he (by
          have := dvd_sub h dY; rwa [add_sub_cancel_left] at this)), add_zero]
    have hy : 1 ≤ v (π * Y) := by
      rw [addVal_mul, addVal_uniformizer hπ]; exact le_self_add
    rw [iotaN_of_le (hw ▸ hy), hw]
    simp

theorem phiTHom_surjective : Function.Surjective (phiTHom K hπ h2 h3 h4 he hq) := by
  intro k
  rcases Nat.lt_or_ge (v W.a₆).toNat 2 with h1 | h2n
  · have hn1 := one_le_n K hπ h2 h3 h4 he hq
    have : (v W.a₆).toNat = 1 := by omega
    refine ⟨0, ?_⟩
    have hsub : Subsingleton (ZMod (v W.a₆).toNat) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  · obtain ⟨P, hP⟩ := exists_phiT_eq_one K hπ h2 h3 h4 he hq h2n
    have : NeZero (v W.a₆).toNat := ⟨by omega⟩
    refine ⟨k.val • P, ?_⟩
    rw [map_nsmul]
    change k.val • phiT K W P = k
    rw [hP, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

def tateQuotientEquiv : (curveK K W).Point ⧸ E0 K W ≃+ ZMod (v W.a₆).toNat :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_phiTHom K hπ h2 h3 h4 he hq)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (phiTHom_surjective K hπ h2 h3 h4 he hq))

end Hom

end

end GroundTheory.Arith.Abelian
