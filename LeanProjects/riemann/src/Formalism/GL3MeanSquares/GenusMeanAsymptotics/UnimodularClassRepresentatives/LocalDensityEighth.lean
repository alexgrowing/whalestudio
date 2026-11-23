import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySeventh

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms

open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m r : Type} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

abbrev mkk (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    𝓞 K →+* 𝓞 K ⧸ extP K 𝔭 ^ k := Ideal.Quotient.mk (extP K 𝔭 ^ k)

theorem exists_lift {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    ∃ Y : Matrix a b (𝓞 K), Y.map (mkk K 𝔭 k) = X := by
  choose f hf using fun x : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective x
  refine ⟨X.map f, ?_⟩
  ext i j
  simp [hf]

theorem map_conjTranspose {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K)) :
    (X.map (mkk K 𝔭 k))ᴴ = Xᴴ.map (mkk K 𝔭 k) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  exact idealPowerSpanBounds.star_mk 𝔭 k (X j i)

theorem map_form {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (X : Matrix m a (𝓞 K))
    (Y : Matrix m b (𝓞 K)) :
    (X.map (mkk K 𝔭 k))ᴴ * H.map (mkk K 𝔭 k) * Y.map (mkk K 𝔭 k) = (Xᴴ * H * Y).map (mkk K 𝔭 k) := by
  rw [map_conjTranspose, Matrix.map_mul, Matrix.map_mul]

theorem map_map_piQ {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K)) :
    (X.map (mkk K 𝔭 (k + 1))).map (piQ K 𝔭 k) = X.map (mkk K 𝔭 k) := rfl

theorem absNorm_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact idealPowerSpanBounds.ne_bot h𝔭)

theorem exists_unit_quot (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∃ θ e : 𝓞 K ⧸ extP K 𝔭 ^ k, (θ - star θ) * e = 1 := by
  obtain ⟨θ, hθ⟩ := exists_theta hK (Fact.out : IsFixF K F) h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ k
  refine ⟨Ideal.Quotient.mk _ θ, Ideal.Quotient.mk _ e, ?_⟩
  rw [idealPowerSpanBounds.star_mk, idealPowerSpanBounds.star_def, ← map_sub, ← map_mul,
    ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
  exact he

theorem card_hermSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (hermSub r (RingHom.ker (piQ K 𝔭 k))) =
      Ideal.absNorm 𝔭 ^ (Fintype.card r * Fintype.card r) := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hF : IsFixF K F := Fact.out
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 (k + 1)
  have hJ : ∀ a ∈ RingHom.ker (piQ K 𝔭 k), star a ∈ RingHom.ker (piQ K 𝔭 k) := by
    intro a ha
    rw [ker_piQ] at ha ⊢
    exact star_mem_idQ ha
  have h1 := card_hermSub_sq (r := r) hJ he
  rw [card_entSub, card_ker_piQ hK hF h𝔭 k, ← pow_mul, mul_comm 2, pow_mul] at h1
  exact Nat.pow_left_injective (by norm_num) h1

theorem card_rep_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (T : Matrix r r (𝓞 K)) (hT : Tᴴ = T) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ X Y : Matrix m r (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) →
      (p' ((X + Y).map (mkk K 𝔭 k)) ↔ p' (X.map (mkk K 𝔭 k))))
    (RC : ∀ X : Matrix m r (𝓞 K), p' (X.map (mkk K 𝔭 k)) →
      (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix r r (𝓞 K),
      (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) →
      ∃ Y : Matrix m r (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) ∧
        ∀ a b, (Xᴴ * H * Y + Yᴴ * H * X - S) a b ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) // p' (X.map (piQ K 𝔭 k)) ∧
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = T.map (mkk K 𝔭 (k + 1))} *
        Ideal.absNorm 𝔭 ^ (Fintype.card r * Fintype.card r) =
      Ideal.absNorm 𝔭 ^ (2 * (Fintype.card m * Fintype.card r)) *
        Nat.card {X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ k) // p' X ∧
          Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)} := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hF : IsFixF K F := Fact.out
  have hHq : (H.map (mkk K 𝔭 (k + 1)))ᴴ = H.map (mkk K 𝔭 (k + 1)) := by
    rw [map_conjTranspose, hH]
  have hTq : (T.map (mkk K 𝔭 (k + 1)))ᴴ = T.map (mkk K 𝔭 (k + 1)) := by
    rw [map_conjTranspose, hT]
  have hinv' : ∀ X Y : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)),
      Y ∈ entSub m r (idQ K 𝔭 (k + 1) j) →
      (p' ((X + Y).map (piQ K 𝔭 k)) ↔ p' (X.map (piQ K 𝔭 k))) := by
    intro X Y hY
    obtain ⟨X0, rfl⟩ := exists_lift 𝔭 (k + 1) X
    have hY1 : ∀ a b, Y a b ∈ idQ K 𝔭 (k + 1) j := hY
    have hY' : ∀ a b, ∃ z ∈ extP K 𝔭 ^ j, Ideal.Quotient.mk _ z = Y a b :=
      fun a b => mem_idQ.mp (hY1 a b)
    choose Y0 hY0 hY0' using hY'
    have hsum : X0.map (mkk K 𝔭 (k + 1)) + Y = (X0 + Matrix.of Y0).map (mkk K 𝔭 (k + 1)) := by
      ext a b
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, map_add, hY0']
    rw [hsum, map_map_piQ, map_map_piQ]
    exact hinv X0 (Matrix.of Y0) hY0
  have RC' : ∀ X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), p' (X.map (piQ K 𝔭 k)) →
      (∀ i j, (Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X - T.map (mkk K 𝔭 (k + 1))) i j ∈
        RingHom.ker (piQ K 𝔭 k)) →
      ∀ S ∈ hermSub r (RingHom.ker (piQ K 𝔭 k)), ∃ Y ∈ entSub m r (idQ K 𝔭 (k + 1) j),
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * Y + Yᴴ * H.map (mkk K 𝔭 (k + 1)) * X = S := by
    intro X hpX hX S hS
    obtain ⟨X0, rfl⟩ := exists_lift 𝔭 (k + 1) X
    rw [map_map_piQ] at hpX
    have hX0 : ∀ a b, (X0ᴴ * H * X0 - T) a b ∈ extP K 𝔭 ^ k := by
      intro a b
      have h1 := hX a b
      rw [map_form, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub,
        ← Matrix.sub_apply] at h1
      exact (mk_mem_ker_piQ 𝔭 k _).mp h1
    have hS1 := HermitianSublattices.mem_hermSub.mp hS
    have hSe : ∀ a b, ∃ z ∈ extP K 𝔭 ^ k, Ideal.Quotient.mk _ z = S a b := by
      intro a b
      have h2 := hS1.2 a b
      rw [ker_piQ] at h2
      exact mem_idQ.mp h2
    choose S0 hS0 hS0' using hSe
    have hSmap : S = (Matrix.of S0).map (mkk K 𝔭 (k + 1)) := by
      ext a b
      exact (hS0' a b).symm
    have hS0h : ∀ a b, ((Matrix.of S0)ᴴ - Matrix.of S0) a b ∈ extP K 𝔭 ^ (k + 1) := by
      intro a b
      have h3 := congrFun (congrFun hS1.1 a) b
      rw [hSmap, map_conjTranspose] at h3
      simp only [Matrix.map_apply] at h3
      rw [Matrix.sub_apply]
      exact Ideal.Quotient.eq.mp h3
    obtain ⟨Y0, hY0, hY0'⟩ := RC X0 hpX hX0 (Matrix.of S0) (fun a b => hS0 a b) hS0h
    refine ⟨Y0.map (mkk K 𝔭 (k + 1)), fun a b => mem_idQ.mpr ⟨Y0 a b, hY0 a b, rfl⟩, ?_⟩
    rw [hSmap, map_form, map_form]
    ext a b
    simp only [Matrix.add_apply, Matrix.map_apply]
    rw [← map_add, Ideal.Quotient.eq]
    have h4 := hY0' a b
    simpa only [Matrix.sub_apply, Matrix.add_apply] using h4
  have h := card_lift_matrix (piQ K 𝔭 k) (piQ_surjective 𝔭 k) (piQ_star 𝔭 k)
    (idQ K 𝔭 (k + 1) j) (fun a ha => star_mem_idQ ha) (fun a ha b hb => mul_eq_zero_idQ hj ha hb)
    (H.map (mkk K 𝔭 (k + 1))) hHq (T.map (mkk K 𝔭 (k + 1))) hTq p' hinv' RC'
  rw [card_hermSub hK h𝔭 k, card_entSub, card_ker_piQ hK hF h𝔭 k, map_map_piQ, map_map_piQ,
    ← pow_mul] at h
  exact h

end Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
