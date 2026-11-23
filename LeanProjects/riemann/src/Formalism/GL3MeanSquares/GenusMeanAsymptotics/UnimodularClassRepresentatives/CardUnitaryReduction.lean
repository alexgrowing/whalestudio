import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSkewValue

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open HermitianSublattices idealPowerSpanBounds

namespace Cell

section Abs

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]

theorem map_skew (ρ : A →+* C) (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y))
    (hμm : ∀ a y, μ (ρ a * y) = a * μ y) (H : Matrix κ κ A) (Y : Matrix κ κ C) :
    (H.map ρ * Y + Yᴴ * H.map ρ).map μ = H * Y.map μ + (Y.map μ)ᴴ * H := by
  ext i l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, hμm,
    conjTranspose_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, hμm, hμs, mul_comm]

theorem quad_zero (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y)) (h2 : ∀ y z, μ y * μ z = 0)
    (H : Matrix κ κ A) (Y : Matrix κ κ C) : (Y.map μ)ᴴ * H * Y.map μ = 0 := by
  ext i l
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro m _
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hμs, mul_right_comm, h2, zero_mul]

theorem expand {H X0 : Matrix κ κ A} (hX0 : X0ᴴ * H * X0 = H) (D : Matrix κ κ A) :
    (X0 * (1 + D))ᴴ * H * (X0 * (1 + D)) = H + (H * D + Dᴴ * H) + Dᴴ * H * D := by
  rw [conjTranspose_mul, conjTranspose_add, conjTranspose_one]
  calc _ = (1 + Dᴴ) * (X0ᴴ * H * X0) * (1 + D) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hX0]; noncomm_ring

theorem card_unitary_reduction [Finite A] (π : A →+* A') (ρ : A →+* C) (μ : C →+ A)
    (hμi : Function.Injective μ) (hμr : ∀ a, π a = 0 ↔ ∃ y, μ y = a)
    (hμs : ∀ y, μ (star y) = star (μ y)) (hμm : ∀ a y, μ (ρ a * y) = a * μ y)
    (h2 : ∀ y z, μ y * μ z = 0) (H : Matrix κ κ A)
    (hu : ∀ X : Matrix κ κ A, Xᴴ * H * X = H → IsUnit X.det) :
    Nat.card {X : Matrix κ κ A // Xᴴ * H * X = H} =
      Nat.card {X' : Matrix κ κ A' // ∃ X : Matrix κ κ A, Xᴴ * H * X = H ∧ X.map π = X'} *
        Nat.card {Y : Matrix κ κ C // H.map ρ * Y + Yᴴ * H.map ρ = 0} := by
  rw [mul_comm]
  apply NormLifting.card_eq_mul_of_fibers (fun X : {X : Matrix κ κ A // Xᴴ * H * X = H} =>
    (⟨X.1.map π, X.1, X.2, rfl⟩ :
      {X' : Matrix κ κ A' // ∃ X : Matrix κ κ A, Xᴴ * H * X = H ∧ X.map π = X'}))
  rintro ⟨X', X0, hX0, rfl⟩
  have hmi : Function.Injective (fun Y : Matrix κ κ C => Y.map μ) := Matrix.map_injective hμi
  have hS : ∀ Y : Matrix κ κ C, H.map ρ * Y + Yᴴ * H.map ρ = 0 →
      (X0 * (1 + Y.map μ))ᴴ * H * (X0 * (1 + Y.map μ)) = H := by
    intro Y hY
    rw [expand hX0, quad_zero μ hμs h2, ← map_skew ρ μ hμs hμm, hY]
    simp
  have hπ : ∀ Y : Matrix κ κ C, (X0 * (1 + Y.map μ)).map π = X0.map π := by
    intro Y
    have h0 : (Y.map μ).map π = 0 := by
      ext i l
      exact (hμr _).2 ⟨_, rfl⟩
    rw [Matrix.map_mul, Matrix.map_add _ (map_add π), h0, add_zero, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.mul_one]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun Y => ⟨⟨X0 * (1 + Y.1.map μ), hS Y.1 Y.2⟩, Subtype.ext (hπ Y.1)⟩) ⟨?_, ?_⟩)
  · intro Y Y' h
    have h1 : X0 * (1 + Y.1.map μ) = X0 * (1 + Y'.1.map μ) :=
      congrArg (fun z => z.1.1) h
    have h2' := congrArg (fun z => X0⁻¹ * z) h1
    simp only [Matrix.nonsing_inv_mul_cancel_left _ _ (hu X0 hX0)] at h2'
    exact Subtype.ext (hmi (add_left_cancel h2'))
  · rintro ⟨⟨X, hX⟩, hfib⟩
    have hXπ : X.map π = X0.map π := congrArg Subtype.val hfib
    have hD : ∀ i l, ∃ y, μ y = (X0⁻¹ * (X - X0)) i l := by
      intro i l
      rw [← hμr, Matrix.mul_apply, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      have : π (X k l) = π (X0 k l) := congrFun (congrFun hXπ k) l
      rw [map_mul, Matrix.sub_apply, map_sub, this, sub_self, mul_zero]
    choose y hy using hD
    have hYD : (Matrix.of y).map μ = X0⁻¹ * (X - X0) := by
      ext i l
      exact hy i l
    have hXe : X0 * (1 + (Matrix.of y).map μ) = X := by
      rw [hYD, Matrix.mul_add, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hu X0 hX0)]
      abel
    have hsk : H.map ρ * Matrix.of y + (Matrix.of y)ᴴ * H.map ρ = 0 := by
      apply hmi
      show (H.map ρ * Matrix.of y + (Matrix.of y)ᴴ * H.map ρ).map μ = (0 : Matrix κ κ C).map μ
      have h3 := expand hX0 ((Matrix.of y).map μ)
      rw [hXe, hX, quad_zero μ hμs h2, add_zero] at h3
      rw [map_skew ρ μ hμs hμm, Matrix.map_zero _ (map_zero μ)]
      exact (left_eq_add.1 h3)
    exact ⟨⟨Matrix.of y, hsk⟩, Subtype.ext (Subtype.ext hXe)⟩

end Abs

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def muQ {𝔭 : Ideal (𝓞 F)} {j : ℕ} (c : ℕ) {d : 𝓞 F} (hd : d ∈ 𝔭 ^ j) :
    (𝓞 K ⧸ extP K 𝔭 ^ c) →+ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)) :=
  (Submodule.mapQ (extP K 𝔭 ^ c) (extP K 𝔭 ^ (j + c)) (LinearMap.mulLeft (𝓞 K) (ι d)) (by
    intro a ha
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, pow_add]
    exact Ideal.mul_mem_mul ((mem_pow_iff 𝔭 j d).2 hd) ha)).toAddMonoidHom

theorem muQ_mk {𝔭 : Ideal (𝓞 F)} {j : ℕ} (c : ℕ) {d : 𝓞 F} (hd : d ∈ 𝔭 ^ j) (a : 𝓞 K) :
    muQ (K := K) c hd (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ι d * a) := rfl

end Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

variable [Fact (IsFixF K F)]

theorem card_cell {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H)
    {j c : ℕ} (hcj : c ≤ j)
    (hu : ∀ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)),
      Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) → IsUnit X.det) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)) //
        Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c)} =
      Nat.card {X' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
          ∃ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)), Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) ∧
            X.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right j c))) = X'} *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ c) // Hq H 𝔭 c * Y + Yᴴ * Hq H 𝔭 c = 0} := by
  obtain ⟨d, hdj, hd⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot h𝔭) j)
  have hfin := finite_quot (K := K) h𝔭 (j + c)
  have hF : IsFixF K F := Fact.out
  have hHc : Hq H 𝔭 c = (Hq H 𝔭 (j + c)).map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left c j))) := by
    ext i l
    rfl
  rw [hHc]
  refine Cell.card_unitary_reduction _ _ (Cell.muQ (K := K) c hdj) ?_ ?_ ?_ ?_ ?_ _ hu
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Cell.muQ_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_of_mul_mem h𝔭 hd ha)
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (map_pow_le_span_sup h𝔭 hd (j + c) ha)
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      refine ⟨Ideal.Quotient.mk _ r, ?_⟩
      rw [Cell.muQ_mk, Ideal.Quotient.eq, ← e]
      have : algebraMap (𝓞 F) (𝓞 K) d * r - (r * algebraMap (𝓞 F) (𝓞 K) d + y) = -y := by ring
      rw [this]
      exact neg_mem hy
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Cell.muQ_mk, Ideal.Quotient.eq] at hy
      have h1 : algebraMap (𝓞 F) (𝓞 K) d * y ∈ extP K 𝔭 ^ j :=
        Ideal.mul_mem_right _ _ ((mem_pow_iff 𝔭 j d).2 hdj)
      have h2 : a = algebraMap (𝓞 F) (𝓞 K) d * y - (algebraMap (𝓞 F) (𝓞 K) d * y - a) := by ring
      rw [h2]
      exact sub_mem h1 (Ideal.pow_le_pow_right (Nat.le_add_right j c) hy)
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [star_mk, Cell.muQ_mk, Cell.muQ_mk, star_mk, star_mul', star_def (algebraMap (𝓞 F) (𝓞 K) d),
      conjO_map hF]
  · intro a y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.factor_mk, ← map_mul, Cell.muQ_mk, Cell.muQ_mk, ← map_mul]
    congr 1
    ring
  · intro y z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Cell.muQ_mk, Cell.muQ_mk, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.pow_le_pow_right (show j + c ≤ j + j by omega)
    rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ ((mem_pow_iff 𝔭 j d).2 hdj))
      (Ideal.mul_mem_right _ _ ((mem_pow_iff 𝔭 j d).2 hdj))

end Formalism.HermitianLattices.Ext.L3.HU
