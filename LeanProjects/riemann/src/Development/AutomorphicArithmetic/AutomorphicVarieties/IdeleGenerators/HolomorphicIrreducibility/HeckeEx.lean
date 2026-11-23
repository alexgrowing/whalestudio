import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformModel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwoNeZeroNat

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd

private def hM (p : ℕ) : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some u => !![1, ((u : ℕ) : ℤ); 0, (p : ℤ)]

private theorem hM_det (p : ℕ) (x : Option (Fin p)) : (hM p x).det = p := by
  cases x <;> simp [hM, Matrix.det_fin_two_of]

private theorem hM_10 (p : ℕ) (x : Option (Fin p)) : hM p x 1 0 = 0 := by
  cases x <;> simp [hM]

private theorem hM_exists {p : ℕ} (hp : p.Prime) (δ : Matrix (Fin 2) (Fin 2) ℤ) (hδ : δ.det = p) :
    ∃ (γ : SL(2, ℤ)) (y : Option (Fin p)), δ = γ.1 * hM p y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  suffices h : ∃ (γ : Matrix (Fin 2) (Fin 2) ℤ) (y : Option (Fin p)), δ = γ * hM p y by
    obtain ⟨γ, y, h⟩ := h
    refine ⟨⟨γ, ?_⟩, y, h⟩
    rw [h, Matrix.det_mul, hM_det] at hδ
    exact mul_right_cancel₀ hp0 (by rw [hδ, one_mul])
  rw [Matrix.det_fin_two] at hδ
  have hz : (δ 0 0 : ZMod p) * δ 1 1 - (δ 0 1 : ZMod p) * δ 1 0 = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hδ
    simpa using this
  have key : ∀ u : ZMod p, (δ 0 1 : ZMod p) = δ 0 0 * u → (δ 1 1 : ZMod p) = δ 1 0 * u →
      ∃ (γ : Matrix (Fin 2) (Fin 2) ℤ) (y : Option (Fin p)), δ = γ * hM p y := by
    intro u h1 h2
    have d1 : (p : ℤ) ∣ δ 0 1 - δ 0 0 * (u.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp [h1]
    have d2 : (p : ℤ) ∣ δ 1 1 - δ 1 0 * (u.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp [h2]
    obtain ⟨b, hb⟩ := d1
    obtain ⟨d, hd⟩ := d2
    refine ⟨!![δ 0 0, b; δ 1 0, d], some ⟨u.val, ZMod.val_lt u⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [hM, Matrix.mul_fin_two] <;> simp at hb hd ⊢
    · linear_combination hb
    · linear_combination hd
  by_cases ha : (δ 0 0 : ZMod p) = 0
  · by_cases hc : (δ 1 0 : ZMod p) = 0
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hc
      obtain ⟨a, ha⟩ := ha
      obtain ⟨c, hc⟩ := hc
      refine ⟨!![a, δ 0 1; c, δ 1 1], none, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [hM, Matrix.mul_fin_two] <;> simp
      · linear_combination ha
      · linear_combination hc
    · refine key (δ 1 1 / δ 1 0) ?_ (by field_simp)
      field_simp
      linear_combination -hz
  · refine key (δ 0 1 / δ 0 0) (by field_simp) ?_
    field_simp
    linear_combination hz

private theorem hM_inj {p : ℕ} (hp : p.Prime) (γ : Matrix (Fin 2) (Fin 2) ℤ) {x y : Option (Fin p)}
    (h : hM p x = γ * hM p y) : x = y := by
  have hnd : ¬ (p : ℤ) ∣ 1 := fun h => hp.not_dvd_one (by exact_mod_cast h)
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  rcases x with _ | u <;> rcases y with _ | v <;>
    simp [hM, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11 ⊢
  · rw [← h10] at h11
    exact hnd ⟨γ 1 1, by linear_combination h11⟩
  · exact hnd ⟨γ 0 0, by linear_combination h00⟩
  · rw [← h00] at h01
    have : (u : ℤ) ≡ (v : ℤ) [ZMOD p] := (Int.modEq_iff_dvd.2 ⟨γ 0 1, by linear_combination h01⟩).symm
    have h2 : (u : ℕ) ≡ (v : ℕ) [MOD p] := Int.natCast_modEq_iff.1 this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 u.2 v.2)

private theorem hM_perm {p : ℕ} (hp : p.Prime) (γ : SL(2, ℤ)) :
    ∃ (σ : Option (Fin p) → Option (Fin p)) (δ : Option (Fin p) → SL(2, ℤ)), Function.Bijective σ ∧
      ∀ x, hM p x * γ.1 = (δ x).1 * hM p (σ x) := by
  choose δ σ h using fun x => hM_exists hp (hM p x * γ.1) (by rw [Matrix.det_mul, hM_det, γ.2, mul_one])
  refine ⟨σ, δ, Finite.injective_iff_bijective.1 fun x y e => ?_, h⟩
  refine hM_inj hp ((δ x * (δ y)⁻¹ : SL(2, ℤ))).1 ?_
  have e1 : γ.1 * (γ⁻¹ : SL(2, ℤ)).1 = 1 := congrArg Subtype.val (mul_inv_cancel γ)
  have e2 : ((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1 = 1 := congrArg Subtype.val (inv_mul_cancel (δ y))
  calc hM p x = (hM p x * γ.1) * (γ⁻¹ : SL(2, ℤ)).1 := by rw [mul_assoc, e1, mul_one]
    _ = (δ x).1 * (((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1) * hM p (σ y) * (γ⁻¹ : SL(2, ℤ)).1 := by
      rw [h x, e, e2, mul_one]
    _ = (δ x).1 * ((δ y)⁻¹ : SL(2, ℤ)).1 * ((hM p y * γ.1) * (γ⁻¹ : SL(2, ℤ)).1) := by
      rw [h y]; simp only [mul_assoc]
    _ = _ := by rw [mul_assoc (hM p y), e1, mul_one]; rfl

private def hG {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix (hM p x)) (by
    rw [← RingHom.map_det, hM_det]; simpa using hp.ne_zero)

private theorem hG_val {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) :
    (hG hp x).1 = (Int.castRingHom ℝ).mapMatrix (hM p x) := rfl

private theorem hG_det {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) : (hG hp x).det.val = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hG_val, ← RingHom.map_det, hM_det]; simp

private theorem hG_σ {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) (c : ℂ) : σ (hG hp x) c = c := by
  have : 0 < (hG hp x).det.val := by rw [hG_det]; exact_mod_cast hp.pos
  rw [σ, if_pos this]; rfl

private theorem hG_slash {p : ℕ} (hp : p.Prime) (k : ℤ) (f : ℍ → ℂ) {x y : Option (Fin p)} {γ δ : SL(2, ℤ)}
    (h : hM p x * γ.1 = δ.1 * hM p y) : (f ∣[k] hG hp x) ∣[k] γ = (f ∣[k] δ) ∣[k] hG hp y := by
  rw [SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
  congr 1
  apply Units.ext
  have := congrArg (Int.castRingHom ℝ).mapMatrix h
  rw [map_mul, map_mul] at this
  exact this

private def hT {p : ℕ} (hp : p.Prime) (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ x : Option (Fin p), χ ((hM p x 0 0 : ℤ) : ZMod N) • f ∣[(k : ℤ)] hG hp x

private theorem hT_slash {p : ℕ} (hp : p.Prime) (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ)
    (γ : SL(2, ℤ)) {s : Option (Fin p) → Option (Fin p)} {δ : Option (Fin p) → SL(2, ℤ)}
    (h : ∀ x, hM p x * γ.1 = (δ x).1 * hM p (s x)) :
    hT hp k χ f ∣[(k : ℤ)] γ =
      ∑ x : Option (Fin p), χ ((hM p x 0 0 : ℤ) : ZMod N) • (f ∣[(k : ℤ)] δ x) ∣[(k : ℤ)] hG hp (s x) := by
  rw [hT, SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [SL_smul_slash, hG_slash hp k f (h x)]

private theorem hT_char {p : ℕ} (hp : p.Prime) (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℍ → ℂ}
    (hf : HasChar k χ f) : HasChar k χ (hT hp k χ f) := by
  intro γ hγ
  obtain ⟨s, δ, hs, h⟩ := hM_perm hp γ
  rw [hT_slash hp k χ f γ h, hT, Finset.smul_sum,
    ← hs.sum_comp fun y => χ ((γ 1 1 : ℤ) : ZMod N) • χ ((hM p y 0 0 : ℤ) : ZMod N) • f ∣[(k : ℤ)] hG hp y]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Gamma0_mem] at hγ
  have h00 := congrArg (Int.cast : ℤ → ZMod N) (congrFun (congrFun (h x) 0) 0)
  have h10 := congrArg (Int.cast : ℤ → ZMod N) (congrFun (congrFun (h x) 1) 0)
  simp [Matrix.mul_apply, Fin.sum_univ_two, hM_10, hγ] at h00 h10
  have dγ := congrArg (Int.cast : ℤ → ZMod N) (γ.det_coe)
  have dδ := congrArg (Int.cast : ℤ → ZMod N) ((δ x).det_coe)
  rw [Matrix.det_fin_two] at dγ dδ
  push_cast at dγ dδ
  rw [hγ, mul_zero, sub_zero] at dγ
  by_cases hu : IsUnit ((hM p (s x) 0 0 : ℤ) : ZMod N)
  · have hc : (((δ x) 1 0 : ℤ) : ZMod N) = 0 := by
      exact hu.mul_left_eq_zero.1 h10.symm
    rw [hf (δ x) (Gamma0_mem.2 hc), smul_slash, hG_σ, smul_smul, smul_smul, ← map_mul, ← map_mul]
    congr 2
    rw [hc, mul_zero, sub_zero] at dδ
    linear_combination (((γ 1 1 : ℤ) : ZMod N) * (((δ x) 1 1 : ℤ) : ZMod N)) * h00
      - (((hM p x 0 0 : ℤ) : ZMod N) * (((δ x) 1 1 : ℤ) : ZMod N)) * dγ
      + (((hM p (s x) 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N)) * dδ
  · have hx : ¬ IsUnit ((hM p x 0 0 : ℤ) : ZMod N) := fun hx => hu <| by
      have := hx.mul (IsUnit.of_mul_eq_one _ dγ)
      rw [h00] at this
      exact isUnit_of_mul_isUnit_right this
    rw [χ.map_nonunit hu, χ.map_nonunit hx]
    simp

private theorem hT_apply {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ)
    (z : ℍ) : hT hp k χ f z = heckeOne 1 p f z +
      (χ (p : ZMod N) * (p : ℂ) ^ (k - 1) - 1) / (p - 1) * (heckeOne 2 p f z - heckeOne 1 p f z) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp.ne_one)
  have hpos : ∀ x, 0 < (hG hp x).det.val := fun x => by rw [hG_det]; exact_mod_cast hp.pos
  have e0 : (f ∣[(k : ℤ)] hG hp none) z = (p : ℂ) ^ (k - 1) * f (ofComplex (p * (z : ℂ))) := by
    rw [slash_apply, hG_σ, hG_det, ← ofComplex_apply (hG hp none • z), coe_smul_of_det_pos (hpos _)]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [num, denom, hG_val, hM, mul_comm]
  have e1 : ∀ u : Fin p, (f ∣[(k : ℤ)] hG hp (some u)) z = (p : ℂ)⁻¹ * f (ofComplex (((z : ℂ) + (u : ℕ)) / p)) := fun u => by
    rw [slash_apply, hG_σ, hG_det, ← ofComplex_apply (hG hp (some u) • z), coe_smul_of_det_pos (hpos _)]
    simp [num, denom, hG_val, hM, zpow_sub₀ hp0]
    field_simp
  rw [hT, Finset.sum_apply, Fintype.sum_option]
  simp only [Pi.smul_apply, e0, e1, heckeOne, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun b : ℕ => f (ofComplex (((z : ℂ) + b) / p))), Finset.mul_sum]
  simp [hM]
  field_simp
  ring

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.heckeEx :
    UpperTheory.V.Sd.HeckeEx :=
  _root_.UpperTheory.Reformulated.B.hecke_existence.heckeEx
