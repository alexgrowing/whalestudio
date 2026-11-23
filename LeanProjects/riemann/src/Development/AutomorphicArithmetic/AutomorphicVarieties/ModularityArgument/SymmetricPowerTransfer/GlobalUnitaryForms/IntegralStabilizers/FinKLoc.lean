import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.FK

open Matrix Loc

variable {K K' : Type} [Field K] [Field K'] {Δ : K}

def qm (a b : Lsq K Δ) : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := !![a, b; -star b, star a]

def Shape (m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : Prop := m 1 1 = star (m 0 0) ∧ m 1 0 = -star (m 0 1)

theorem shape_qm (a b : Lsq K Δ) : Shape (qm a b) := ⟨rfl, rfl⟩

theorem Shape.eq {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape m) : m = qm (m 0 0) (m 0 1) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm, h.1, h.2]

theorem mem_DX (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔ Shape (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
  change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = MulAut.conj (wJ Δ)⁻¹ g ↔ _
  rw [Units.ext_iff]
  simp [MulAut.conj_apply, wJ, Matrix.mul_apply, Fin.sum_univ_two, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, Shape, starRingEnd_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, -⟩
    exact ⟨h1.symm, by rw [h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1.symm, by rw [h2, neg_neg]⟩, by rw [h2, star_neg, star_star], by rw [h1, star_star]⟩

theorem shape_mt (g : DX Δ) : Shape (mt g) := (mem_DX _).1 g.2

theorem lmap_star (f : K →+* K') (x : Lsq K Δ) : lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

theorem lmap_inj (f : K →+* K') : Function.Injective (lmap f Δ) := fun x y h => by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  exact QuadraticAlgebra.ext (f.injective h1) (f.injective h2)

theorem qm_map (f : K →+* K') (a b : Lsq K Δ) : (qm a b).map (lmap f Δ) = qm (lmap f Δ a) (lmap f Δ b) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm, lmap_star]

theorem shape_of_map (f : K →+* K') {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape (m.map (lmap f Δ))) : Shape m := by
  obtain ⟨h1, h2⟩ := h
  simp only [Matrix.map_apply, ← lmap_star, ← map_neg] at h1 h2
  exact ⟨lmap_inj f h1, lmap_inj f h2⟩

theorem det_qm (a b : Lsq K Δ) :
    (qm a b).det = algebraMap K (Lsq K Δ) (a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2) := by
  rw [Matrix.det_fin_two]
  refine QuadraticAlgebra.ext ?_ ?_ <;> simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im] <;> simp [qm, pow_two] <;> ring

variable (O : Type) [CommRing O] [Algebra O K]

theorem int_star {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let φ : Lsq K Δ →ₐ[O] Lsq K Δ :=
    { starRingEnd (Lsq K Δ) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
        refine QuadraticAlgebra.ext ?_ ?_ <;> simp [starRingEnd_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] }
  exact h.map φ

variable (Δ) in

def RL : Subring (Matrix (Fin 2) (Fin 2) (Lsq K Δ)) where
  carrier := {m | Shape m ∧ ∀ i j, IsIntegral O (m i j)}
  mul_mem' := by
    rintro a b ⟨⟨h1, h2⟩, ha⟩ ⟨⟨h3, h4⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, fun i j => ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact ((ha _ _).mul (hb _ _)).add ((ha _ _).mul (hb _ _))
  one_mem' := ⟨⟨by simp, by simp⟩, fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_one, isIntegral_zero]⟩
  add_mem' := by
    rintro a b ⟨⟨h1, h2⟩, ha⟩ ⟨⟨h3, h4⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, fun i j => (ha i j).add (hb i j)⟩
    · simp [h1, h3]
    · simp [h2, h4]; ring
  zero_mem' := ⟨⟨by simp, by simp⟩, fun i j => isIntegral_zero⟩
  neg_mem' := by
    rintro a ⟨⟨h1, h2⟩, ha⟩
    exact ⟨⟨by simp [h1], by simp [h2]⟩, fun i j => (ha i j).neg⟩

theorem qm_mem {a b : Lsq K Δ} (ha : IsIntegral O a) (hb : IsIntegral O b) : qm a b ∈ RL Δ O := by
  refine ⟨shape_qm a b, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [qm]
  exacts [ha, hb, int_star O hb, int_star O ha]

theorem mem_KD (g : DX Δ) : g ∈ KD Δ O ↔ mt g ∈ RL Δ O ∧ mt g⁻¹ ∈ RL Δ O := by
  rw [KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    have e1 : mt g = (u : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).map Subtype.val := by
      show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [← hu]; rfl
    have e2 : mt g⁻¹ = ((u⁻¹ : GL (Fin 2) (integralClosure O (Lsq K Δ))) : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).map Subtype.val := by
      show (((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [Subgroup.coe_inv, ← hu, ← map_inv]; rfl
    refine ⟨⟨shape_mt g, fun i j => ?_⟩, ⟨shape_mt g⁻¹, fun i j => ?_⟩⟩
    · rw [e1]; exact ((u : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) i j).2
    · rw [e2]; exact (((u⁻¹ : GL (Fin 2) (integralClosure O (Lsq K Δ))) : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) i j).2
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    let f := (integralClosure O (Lsq K Δ)).val.toRingHom
    let A : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨mt g i j, h1 i j⟩
    let B : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨mt g⁻¹ i j, h2 i j⟩
    have hA : A.map f = mt g := rfl
    have hB : B.map f = mt g⁻¹ := rfl
    have inj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) => M.map f) :=
      fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    have hAB : A * B = 1 := inj (by
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one f (map_zero f) (map_one f)]
      show mt (g * g⁻¹) = 1
      rw [mul_inv_cancel]; rfl)
    have hBA : B * A = 1 := inj (by
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one f (map_zero f) (map_one f)]
      show mt (g⁻¹ * g) = 1
      rw [inv_mul_cancel]; rfl)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem mt_mul (g h : DX Δ) : mt (g * h) = mt g * mt h := rfl

theorem conj_mem {u : DX Δ} (hu : u ∈ ZD Δ ⊔ KD Δ O) {r : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (hr : r ∈ RL Δ O) :
    mt u * r * mt u⁻¹ ∈ RL Δ O := by
  have mt1 : mt (1 : DX Δ) = 1 := rfl
  have base : ∀ w : DX Δ, w ∈ ZD Δ ∨ w ∈ KD Δ O → ∀ s ∈ RL Δ O, mt w * s * mt w⁻¹ ∈ RL Δ O := by
    rintro w (hw | hw) s hs
    · rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hw
      obtain ⟨t, ht⟩ := hw
      have hc : Commute (mt w) s := by
        show Commute ((w : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) s
        rw [← ht]
        exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) s
      rw [hc.eq, mul_assoc, ← mt_mul, mul_inv_cancel, mt1, mul_one]
      exact hs
    · obtain ⟨h1, h2⟩ := (mem_KD O w).1 hw
      exact (RL Δ O).mul_mem ((RL Δ O).mul_mem h1 hs) h2
  rw [Subgroup.sup_eq_closure] at hu
  refine (Subgroup.closure_induction
    (p := fun v _ => (∀ s ∈ RL Δ O, mt v * s * mt v⁻¹ ∈ RL Δ O) ∧ (∀ s ∈ RL Δ O, mt v⁻¹ * s * mt v ∈ RL Δ O))
    ?_ ?_ ?_ ?_ hu).1 r hr
  · intro x hx
    refine ⟨base x hx, fun s hs => ?_⟩
    have hx' : x⁻¹ ∈ ZD Δ ∨ x⁻¹ ∈ KD Δ O := hx.imp (fun h => inv_mem h) (fun h => inv_mem h)
    simpa using base x⁻¹ hx' s hs
  · refine ⟨fun s hs => ?_, fun s hs => ?_⟩ <;> simpa [mt1] using hs
  · rintro x y - - ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have e : mt (x * y) * s * mt (x * y)⁻¹ = mt x * (mt y * s * mt y⁻¹) * mt x⁻¹ := by
        simp only [_root_.mul_inv_rev, mt_mul, mul_assoc]
      rw [e]; exact hx1 _ (hy1 s hs)
    · have e : mt (x * y)⁻¹ * s * mt (x * y) = mt y⁻¹ * (mt x⁻¹ * s * mt x) * mt y := by
        simp only [_root_.mul_inv_rev, mt_mul, mul_assoc]
      rw [e]; exact hy2 _ (hx2 s hs)
  · rintro x - ⟨hx1, hx2⟩
    exact ⟨hx2, by simpa using hx1⟩

theorem int_alg {x : K} : IsIntegral O (algebraMap K (Lsq K Δ) x) ↔ IsIntegral O x := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom O K (Lsq K Δ)) := by
    intro u v huv
    have := congrArg QuadraticAlgebra.re huv
    simpa using this
  exact isIntegral_algHom_iff _ hinj

theorem int_re {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (2 * x.re) := by
  have e : x + star x = algebraMap K (Lsq K Δ) (2 * x.re) := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] <;> ring
  rw [← int_alg O, ← e]
  exact h.add (int_star O h)

theorem int_om {c : ℕ} (hc : IsIntegral O ((c : K) * Δ)) : IsIntegral O (⟨0, c⟩ : Lsq K Δ) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  have e : (⟨0, c⟩ : Lsq K Δ) ^ 2 = algebraMap K (Lsq K Δ) (c * ((c : K) * Δ)) := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp [pow_two] <;> ring
  rw [e, int_alg O]
  exact (isIntegral_natCast c).mul hc

theorem int_im {c : ℕ} (hc : IsIntegral O ((c : K) * Δ)) {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (2 * c * Δ * x.im) := by
  have e : (⟨0, c⟩ : Lsq K Δ) * (x - star x) = algebraMap K (Lsq K Δ) (2 * c * Δ * x.im) := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] <;> ring
  rw [← int_alg O, ← e]
  exact (int_om O hc).mul (h.sub (int_star O h))

theorem int_mk {c : ℕ} (hc : IsIntegral O ((c : K) * Δ)) {r s : K} (hr : IsIntegral O r) (hs : IsIntegral O s) :
    IsIntegral O (⟨r, c * s⟩ : Lsq K Δ) := by
  have e : (⟨r, c * s⟩ : Lsq K Δ) = algebraMap K (Lsq K Δ) r + (⟨0, c⟩ : Lsq K Δ) * algebraMap K (Lsq K Δ) s := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  rw [e]
  exact ((int_alg O).2 hr).add ((int_om O hc).mul ((int_alg O).2 hs))

theorem mem_ZD [CharZero K] (hΔ : Δ ≠ 0) {c : K} (hc : c ≠ 0) (g : DX Δ) (h1 : mt g * qm ⟨0, c⟩ 0 = qm ⟨0, c⟩ 0 * mt g)
    (h2 : mt g * qm 0 1 = qm 0 1 * mt g) : g ∈ ZD Δ := by
  have hs := shape_mt g
  have a01 := congrFun (congrFun h1 0) 1
  have b00 := congrFun (congrFun h2 0) 0
  have b01 := congrFun (congrFun h2 0) 1
  simp [qm, Matrix.mul_apply, Fin.sum_univ_two, QuadraticAlgebra.ext_iff] at a01 b00 b01
  have two : (2 : K) ≠ 0 := two_ne_zero
  have q01 : mt g 0 1 = 0 := by
    refine QuadraticAlgebra.ext ?_ ?_
    · have e : (2 * c) * (mt g 0 1).re = 0 := by linear_combination -a01.2
      simpa [two, hc] using e
    · have e : (2 * Δ * c) * (mt g 0 1).im = 0 := by linear_combination -a01.1
      simpa [two, hc, hΔ] using e
  have r10 : mt g 1 0 = 0 := by
    refine QuadraticAlgebra.ext ?_ ?_
    · rw [← b00.1]; simp [q01]
    · rw [← b00.2]; simp [q01]
  have s11 : mt g 1 1 = mt g 0 0 := (QuadraticAlgebra.ext b01.1 b01.2).symm
  have pim : (mt g 0 0).im = 0 := by
    have e := congrArg QuadraticAlgebra.im hs.1
    rw [s11, QuadraticAlgebra.im_star] at e
    have e2 : 2 * (mt g 0 0).im = 0 := by linear_combination e
    simpa [two] using e2
  have hp : mt g 0 0 = algebraMap K (Lsq K Δ) (mt g 0 0).re :=
    QuadraticAlgebra.ext (by simp) (by simp [pim])
  have hre : (mt g 0 0).re ≠ 0 := by
    intro h0
    have e := congrFun (congrFun (show mt g * mt g⁻¹ = 1 by rw [← mt_mul, mul_inv_cancel]; rfl) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hp, h0, q01] at e
    have h3 := congrArg QuadraticAlgebra.re e
    have h11 : (1 : Lsq K Δ).re = 1 := rfl
    simp [h11] at h3
  rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine ⟨Units.mk0 _ hre, Units.ext (Matrix.ext fun i j => ?_)⟩
  fin_cases i <;> fin_cases j <;> simp
  · exact hp.symm
  · exact q01.symm
  · exact r10.symm
  · exact (s11.trans hp).symm

theorem exists_DX {a b : Lsq K Δ} (h : a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2 ≠ 0) : ∃ g : DX Δ, mt g = qm a b := by
  have hu : IsUnit (qm a b).det := by
    rw [det_qm]
    exact ((Units.mk0 _ h).map (algebraMap K (Lsq K Δ)).toMonoidHom).isUnit
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' (qm a b) hu, (mem_DX _).2 (shape_qm a b)⟩, rfl⟩

theorem shape_nat (n : ℕ) {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape m) :
    Shape ((n : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * m) := by
  obtain ⟨h1, h2⟩ := h
  rw [← Matrix.diagonal_natCast']
  constructor <;> simp [Matrix.diagonal_mul, h1, h2, mul_comm]

theorem den_mat {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral O ((c : K) * Δ)) (hd : ∀ x : K, ∃ n : ℕ, n ≠ 0 ∧ IsIntegral O ((n : K) * x))
    {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape m) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * m ∈ RL Δ O := by
  have one : ∀ x : Lsq K Δ, ∃ n : ℕ, n ≠ 0 ∧ IsIntegral O ((n : Lsq K Δ) * x) := by
    intro x
    obtain ⟨n1, hn1, h1⟩ := hd x.re
    obtain ⟨n2, hn2, h2⟩ := hd (x.im / c)
    refine ⟨n1 * n2, mul_ne_zero hn1 hn2, ?_⟩
    have e : ((n1 * n2 : ℕ) : Lsq K Δ) * x = ⟨n2 * (n1 * x.re), c * (n1 * (n2 * (x.im / c)))⟩ := by
      refine QuadraticAlgebra.ext ?_ ?_
      · simp; ring
      · simp; field_simp
    rw [e]
    exact int_mk O hc ((isIntegral_natCast n2).mul h1) ((isIntegral_natCast n1).mul h2)
  obtain ⟨na, hna, ha⟩ := one (m 0 0)
  obtain ⟨nb, hnb, hb⟩ := one (m 0 1)
  refine ⟨nb * na, mul_ne_zero hnb hna, shape_nat (nb * na) h, fun i j => ?_⟩
  have hA : IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 0 0) := by
    rw [Nat.cast_mul, mul_assoc]; exact (isIntegral_natCast nb).mul ha
  have hB : IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 0 1) := by
    rw [Nat.cast_mul, mul_comm (nb : Lsq K Δ), mul_assoc]; exact (isIntegral_natCast na).mul hb
  have st : ∀ x : Lsq K Δ, ((nb * na : ℕ) : Lsq K Δ) * star x = star (((nb * na : ℕ) : Lsq K Δ) * x) := by
    intro x; rw [star_mul, star_natCast, mul_comm]
  rw [← Matrix.diagonal_natCast', Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · exact hA
  · exact hB
  · show IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 1 0)
    rw [h.2, mul_neg, st]; exact (int_star O hB).neg
  · show IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 1 1)
    rw [h.1, st]; exact int_star O hA

end UpperTheory.V.Z.Sym.Glob.FK
