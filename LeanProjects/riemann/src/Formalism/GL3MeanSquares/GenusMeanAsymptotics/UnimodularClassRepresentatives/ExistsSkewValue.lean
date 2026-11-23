import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open HermitianSublattices idealPowerSpanBounds

section Abstract

variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem card_skew_lift [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (H : Matrix m m A) (hH : Hᴴ = H)
    (hS : ∀ S ∈ hermSub m (RingHom.ker π), ∃ Y : Matrix m m A, H * Y + Yᴴ * H = S) :
    Nat.card {Y : Matrix m m A // H * Y + Yᴴ * H = 0} * Nat.card (hermSub m (RingHom.ker π)) =
      Nat.card (entSub m m (RingHom.ker π)) *
        Nat.card {Y' : Matrix m m A' // H.map π * Y' + Y'ᴴ * H.map π = 0} := by
  have hgH : ∀ Y : Matrix m m A, (H * Y + Yᴴ * H)ᴴ = H * Y + Yᴴ * H := by
    intro Y
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
      add_comm]
  have h1 := card_uniform (⊤ : AddSubgroup (Matrix m m A)) (hermSub m (RingHom.ker π))
    (fun Y : Matrix m m A => H * Y + Yᴴ * H) (fun _ => True) (fun _ _ _ => Iff.rfl) (by
      intro X _ _
      refine ⟨AddMonoidHom.mk' (fun Y => H * Y.1 + Y.1ᴴ * H) (fun a b => by
        simp only [AddSubgroup.coe_add, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; abel),
        ?_, ?_⟩
      · intro Y
        show H * (X + Y.1) + (X + Y.1)ᴴ * H = H * X + Xᴴ * H + (H * Y.1 + Y.1ᴴ * H)
        simp only [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
        abel
      · intro S hS'
        obtain ⟨Y, h⟩ := hS S hS'
        exact ⟨⟨Y, trivial⟩, h⟩)
  have e0 : {Y : Matrix m m A // H * Y + Yᴴ * H = 0} ≃
      {Y : Matrix m m A // True ∧ H * Y + Yᴴ * H = 0} :=
    Equiv.subtypeEquivRight fun X => by rw [true_and]
  rw [Nat.card_congr e0, ← h1]
  have hsurj : Function.Surjective (π.toAddMonoidHom.mapMatrix (m := m) (n := m)) := by
    intro X'
    choose f hf using hπ
    exact ⟨X'.map f, by ext i j; simp [hf]⟩
  have h2 := card_preimage (π.toAddMonoidHom.mapMatrix (m := m) (n := m)) hsurj
    (fun Y' => H.map π * Y' + Y'ᴴ * H.map π = 0)
  have hker : (π.toAddMonoidHom.mapMatrix (m := m) (n := m)).ker = entSub m m (RingHom.ker π) := by
    ext X
    rw [AddMonoidHom.mem_ker, mem_entSub]
    constructor
    · intro h i j
      have := congrFun (congrFun h i) j
      exact this
    · intro h
      ext i j
      exact h i j
  rw [← hker, ← h2]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
  show _ ↔ H.map π * X.map π + (X.map π)ᴴ * H.map π = 0
  have hm : H.map π * X.map π + (X.map π)ᴴ * H.map π = (H * X + Xᴴ * H).map π := by
    rw [Matrix.map_add π (map_add π), Matrix.map_mul, Matrix.map_mul,
      conjTranspose_map π (fun a => hπs a)]
  rw [hm, mem_hermSub, true_and]
  constructor
  · rintro ⟨-, h3⟩
    ext i j
    exact h3 i j
  · intro h3
    exact ⟨hgH X, fun i j => congrFun (congrFun h3 i) j⟩

end Abstract

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev Hq (H : Matrix κ κ (𝓞 K)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))

variable [Fact (IsFixF K F)]

theorem exists_theta_inv (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∃ θ e : 𝓞 K ⧸ extP K 𝔭 ^ k, (θ - star θ) * e = 1 := by
  obtain ⟨θ, hθ⟩ := exists_theta hK (Fact.out : IsFixF K F) h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ k
  refine ⟨Ideal.Quotient.mk _ θ, Ideal.Quotient.mk _ e, ?_⟩
  rw [star_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
  exact he

theorem Hq_conjTranspose {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (Hq H 𝔭 k)ᴴ = Hq H 𝔭 k := by
  conv_rhs => rw [← hH]
  exact (conjTranspose_map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) (fun a => (star_mk 𝔭 k a).symm)).symm

theorem exists_skew_value (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j)
    (S : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1))) (hS : S ∈ hermSub κ (RingHom.ker (piQ K 𝔭 j))) :
    ∃ Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)),
      Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = S := by
  obtain ⟨θ, u, hu⟩ := exists_theta_inv hK h𝔭 (j + 1)
  have hτ : θ * u + star (θ * u) = 1 := by
    rw [star_mul', star_inv_eq_neg hu]
    linear_combination hu
  set mk := Ideal.Quotient.mk (extP K 𝔭 ^ (j + 1)) with hmk
  set dq := mk (algebraMap (𝓞 F) (𝓞 K) d) with hdq
  have hds : star dq = dq := by
    rw [hdq, hmk, star_mk, star_def, conjO_map Fact.out]
  have hfill : ∀ a b, ∃ r : 𝓞 K, S a b = dq * mk r := by
    intro a b
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (S a b)
    have hs' : s ∈ extP K 𝔭 ^ j := by
      rw [← mk_mem_ker_piQ, hs]
      exact hS.2 a b
    obtain ⟨r, -, hr⟩ := exists_fillO h𝔭 hd hj hs'
    refine ⟨r, ?_⟩
    rw [← hs, hdq, ← map_mul]
    exact Ideal.Quotient.eq.2 hr
  choose r hr using hfill
  set R : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) := Matrix.of fun a b => mk (r a b) with hR
  have hSR : S = dq • R := by
    ext a b
    rw [hr a b]
    rfl
  have hSR' : S = dq • Rᴴ := by
    conv_lhs => rw [← hS.1, hSR, conjTranspose_smul, hds]
  have hHEq : Hq H 𝔭 (j + 1) * E₀.map mk = dq • (1 : Matrix κ κ _) := by
    rw [← Matrix.map_mul, hHE]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    rw [apply_ite mk, map_one, map_zero]
  have hEH : (E₀.map mk)ᴴ * Hq H 𝔭 (j + 1) = dq • (1 : Matrix κ κ _) := by
    have := congrArg conjTranspose hHEq
    rwa [conjTranspose_mul, Hq_conjTranspose hH, conjTranspose_smul, conjTranspose_one, hds] at this
  refine ⟨E₀.map mk * ((θ * u) • R), ?_⟩
  rw [← Matrix.mul_assoc, hHEq, conjTranspose_mul, Matrix.mul_assoc, hEH, conjTranspose_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_comm dq, ← hSR,
    smul_comm dq, ← hSR', ← add_smul, hτ, one_smul]

theorem card_sigma_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j) :
    Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) //
        Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = 0} =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) // Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} := by
  have hF : IsFixF K F := Fact.out
  have := finite_quot (K := K) h𝔭 (j + 1)
  have h1 := card_skew_lift (piQ K 𝔭 j) (piQ_surjective 𝔭 j) (piQ_star 𝔭 j) (Hq H 𝔭 (j + 1))
    (Hq_conjTranspose hH 𝔭 (j + 1)) (exists_skew_value hK h𝔭 hH hd hHE hj)
  have hmap : (Hq H 𝔭 (j + 1)).map (piQ K 𝔭 j) = Hq H 𝔭 j := by
    ext a b
    rfl
  rw [hmap] at h1
  obtain ⟨θ, u, hu⟩ := exists_theta_inv hK h𝔭 (j + 1)
  have hst : ∀ a ∈ RingHom.ker (piQ K 𝔭 j), star a ∈ RingHom.ker (piQ K 𝔭 j) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [piQ_star, ha, star_zero]
  have h2 := card_hermSub_sq (r := κ) hst hu
  have h3 : Nat.card (entSub κ κ (RingHom.ker (piQ K 𝔭 j))) =
      (Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2)) ^ 2 := by
    rw [card_entSub, card_ker_piQ hK hF h𝔭, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h3] at h2
  have h4 : Nat.card (hermSub κ (RingHom.ker (piQ K 𝔭 j))) = Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) :=
    Nat.pow_left_injective (n := 2) (by norm_num) h2
  rw [h3, h4] at h1
  have hpos : 0 < Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) := by
    apply pow_pos
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

end Formalism.HermitianLattices.Ext.L3.HU
