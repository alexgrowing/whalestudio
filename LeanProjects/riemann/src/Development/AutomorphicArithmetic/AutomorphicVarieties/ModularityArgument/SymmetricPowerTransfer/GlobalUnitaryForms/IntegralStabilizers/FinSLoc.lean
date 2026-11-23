import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Field

variable {K : Type} [Field K]

def Dm (Δ : K) : Subring (Matrix (Fin 2) (Fin 2) (Lsq K Δ)) where
  carrier := {m | m 1 1 = star (m 0 0) ∧ m 1 0 = - star (m 0 1)}
  mul_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4] <;> ring
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    constructor <;> simp [h1, h2, h3, h4, add_comm]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    obtain ⟨h1, h2⟩ := ha
    constructor <;> simp [h1, h2]

variable {Δ : K}

theorem mem_Dm {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} : m ∈ Dm Δ ↔ m 1 1 = star (m 0 0) ∧ m 1 0 = - star (m 0 1) := Iff.rfl

theorem mem_DX {g : GL (Fin 2) (Lsq K Δ)} : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) ∈ Dm Δ := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹ ↔ _
    rw [inv_inv, Units.ext_iff]
    rfl
  rw [e, mem_Dm, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  simp
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1.symm, by rw [h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem mt_mem (g : DX Δ) : mt g ∈ Dm Δ := mem_DX.1 g.2

theorem det_Dm {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : m ∈ Dm Δ) :
    m.det = algebraMap K _ ((m 0 0).re ^ 2 - Δ * (m 0 0).im ^ 2 + (m 0 1).re ^ 2 - Δ * (m 0 1).im ^ 2) := by
  rw [Matrix.det_fin_two, h.1, h.2]
  ext <;> simp [sq] <;> ring

variable {O : Type} [CommRing O] [Algebra O K]

theorem mem_KD {g : DX Δ} : g ∈ KD Δ O ↔ (∀ i j, IsIntegral O (mt g i j)) ∧ ∀ i j, IsIntegral O (mt g⁻¹ i j) := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : GeneralLinearGroup.map ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) u⁻¹ = (g⁻¹ : DX Δ) := by
      rw [map_inv, hu]; rfl
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have : mt g i j = (u i j : Lsq K Δ) := by
        change (g : GL (Fin 2) (Lsq K Δ)) i j = _
        have hu2 : (g : GL (Fin 2) (Lsq K Δ)) = _ := hu.symm
        rw [hu2]; rfl
      rw [this]; exact (u i j).2
    · have : mt g⁻¹ i j = ((u⁻¹ : GL (Fin 2) _) i j : Lsq K Δ) := by
        change ((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq K Δ)) i j = _
        rw [← hu']; rfl
      rw [this]; exact ((u⁻¹ : GL (Fin 2) _) i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (fun m : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) =>
        ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix m) :=
      Matrix.map_injective Subtype.val_injective
    let a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨_, h2 i j⟩
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · simp only [map_mul, map_one]
      exact (g : GL (Fin 2) (Lsq K Δ)).mul_inv
    · simp only [map_mul, map_one]
      exact (g : GL (Fin 2) (Lsq K Δ)).inv_mul

theorem isIntegral_star {a : Lsq K Δ} (h : IsIntegral O a) : IsIntegral O (star a) := by
  let f : Lsq K Δ →ₐ[O] Lsq K Δ := { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      change star (algebraMap O (Lsq K Δ) r) = _
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
      ext <;> simp }
  exact h.map f

theorem isIntegral_coords {a : Lsq K Δ} (h : IsIntegral O a) {m : K} (hm : IsIntegral O m) (hmΔ : IsIntegral O (m * Δ)) :
    IsIntegral O (2 * m * Δ * a.re) ∧ IsIntegral O (2 * m * Δ * a.im) := by
  have inj : Function.Injective (algebraMap K (Lsq K Δ)) := fun x y h => by simpa using congrArg QuadraticAlgebra.re h
  have h1 : IsIntegral O (2 * a.re) := by
    rw [← isIntegral_algebraMap_iff inj]
    convert h.add (isIntegral_star h) using 1
    ext <;> simp; ring
  have h2 : IsIntegral O (Δ * (2 * a.im) ^ 2) := by
    rw [← isIntegral_algebraMap_iff inj]
    convert (h.sub (isIntegral_star h)).pow 2 using 1
    ext <;> simp [sq] <;> ring
  refine ⟨by rw [show 2 * m * Δ * a.re = m * Δ * (2 * a.re) by ring]; exact hmΔ.mul h1, ?_⟩
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [show (2 * m * Δ * a.im) ^ 2 = m * (m * Δ) * (Δ * (2 * a.im) ^ 2) by ring]
  exact (hm.mul hmΔ).mul h2

theorem isIntegral_of_coords {a : Lsq K Δ} {m : K} (hm : IsIntegral O m) (hmΔ : IsIntegral O (m * Δ))
    (h1 : IsIntegral O a.re) (h2 : IsIntegral O a.im) : IsIntegral O (algebraMap K (Lsq K Δ) m * a) := by
  have h3 : IsIntegral O (⟨0, m⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    convert (hm.mul hmΔ).algebraMap (B := Lsq K Δ) using 1
    ext <;> simp [sq]; ring
  convert ((hm.mul h1).algebraMap (B := Lsq K Δ)).add (h3.mul (h2.algebraMap (B := Lsq K Δ))) using 1
  ext <;> simp

end Field

section Global

variable {F : Type} [Field F] [NumberField F]

theorem isIntegral_Ov {v : Pl F} {t : Kv v} : IsIntegral (Ov v) t ↔ t ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨t, h⟩, rfl⟩

theorem isIntegral_glob {t : F} : IsIntegral ℤ t ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v t) := by
  simp only [isIntegral_Ov]
  constructor
  · intro h v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t fun v => by
      have := h v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t]
      exact this
    exact y.2

theorem exists_nat_mul (t : F) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : F) * t) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) t)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

theorem exists_nat_mul_loc (v : Pl F) (t : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * t) := by
  obtain ⟨b, hb, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v t
  have hb0 : (b : F) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  obtain ⟨n, hn, h2⟩ := exists_nat_mul (b : F)⁻¹
  refine ⟨n, hn, ?_⟩
  have h' : IsIntegral (Ov v) (t * cv v (b : F)) := isIntegral_Ov.2 h
  have := (isIntegral_glob.1 h2 v).mul h'
  rwa [map_mul, map_natCast, mul_assoc, mul_left_comm _ t, ← map_mul, inv_mul_cancel₀ hb0, map_one, mul_one] at this

theorem exists_nat_mul_L {Δ : F} (v : Pl F) (a : Lsq (Kv v) (cv v Δ)) :
    ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * a) := by
  obtain ⟨m, hm, h⟩ := exists_nat_mul Δ
  obtain ⟨n1, hn1, h1⟩ := exists_nat_mul_loc v a.re
  obtain ⟨n2, hn2, h2⟩ := exists_nat_mul_loc v a.im
  refine ⟨m * (n1 * n2), by positivity, ?_⟩
  have := isIntegral_of_coords (O := Ov v) (a := ((n1 * n2 : ℕ) : Lsq (Kv v) (cv v Δ)) * a) (m := (m : Kv v))
    (isIntegral_natCast _) (by simpa using isIntegral_glob.1 h v)
    (by simpa [mul_assoc, mul_left_comm] using (isIntegral_natCast n2).mul h1)
    (by simpa [mul_assoc] using (isIntegral_natCast n1).mul h2)
  convert this using 1
  simp [mul_assoc]

theorem den_DA {Δ : F} (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ ∀ v i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * mt (g.1 v) i j) := by
  classical
  have hf : {v : Pl F | ¬ g.1 v ∈ KD (cv v Δ) (Ov v)}.Finite := g.2
  choose n hn h using fun (v : Pl F) (p : Fin 2 × Fin 2) => exists_nat_mul_L v (mt (g.1 v) p.1 p.2)
  refine ⟨∏ v ∈ hf.toFinset, ∏ p, n v p, Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun p _ => hn v p,
    fun v i j => ?_⟩
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact (isIntegral_natCast _).mul ((mem_KD.1 hv).1 i j)
  · obtain ⟨k, hk⟩ := (Finset.dvd_prod_of_mem (n v) (Finset.mem_univ (i, j))).trans
      (Finset.dvd_prod_of_mem (fun v => ∏ p, n v p) (hf.mem_toFinset.2 hv))
    rw [hk, Nat.cast_mul, mul_comm (n v (i, j) : Lsq (Kv v) (cv v Δ)), mul_assoc]
    exact (isIntegral_natCast _).mul (h v (i, j))

end Global

end UpperTheory.V.Z.Sym.Glob
