import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.PKappa
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RootEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem res_rep {k : Type} [Field k] [Finite k] (h2 : (2 : k) ≠ 0) {e u : k} (he : e ≠ 0) (he1 : 1 - e ≠ 0) (hu : u ≠ 0) :
    ∃ a b : k, a ≠ 0 ∧ a ^ 2 - e * b ^ 2 = u := by
  classical
  haveI := Fintype.ofFinite k
  have hodd : Fintype.card k % 2 = 1 := by
    have hc : ringChar k ≠ 2 := by
      intro hc
      apply h2
      have h0 := ringChar.Nat.cast_ringChar (R := k)
      rw [hc] at h0
      exact_mod_cast h0
    have := (FiniteField.even_card_iff_char_two (F := k)).not.1 hc
    omega
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C u) (g := Polynomial.C (-e) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) u) (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 he)) hodd
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at hab
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      apply hu
      linear_combination -hab
    refine ⟨e * b * (2 / (1 - e)), b * ((1 + e) / (1 - e)), ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero he hb) (div_ne_zero h2 he1)
    · have key : (e * b * (2 / (1 - e))) ^ 2 - e * (b * ((1 + e) / (1 - e))) ^ 2
          = -e * b ^ 2 * ((1 - e) / (1 - e)) ^ 2 := by ring
      rw [key, div_self he1, one_pow, mul_one]
      linear_combination hab
  · exact ⟨a, b, ha, by linear_combination hab⟩

private theorem int_rep {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ)
    (e u : Oˣ) (he : IsUnit (1 - (e : O))) : ∃ (x : Oˣ) (y : O), (x : O) ^ 2 - e * y ^ 2 = u := by
  classical
  haveI := L.fin
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) O := L.compl
  have hu0 : IsLocalRing.residue O u ≠ 0 := (u.isUnit.map (IsLocalRing.residue O)).ne_zero
  have he0 : IsLocalRing.residue O e ≠ 0 := (e.isUnit.map (IsLocalRing.residue O)).ne_zero
  have he1 : 1 - IsLocalRing.residue O e ≠ 0 := by
    rw [← map_one (IsLocalRing.residue O), ← map_sub]
    exact (he.map (IsLocalRing.residue O)).ne_zero
  have h2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    have h3 := L.two.map (IsLocalRing.residue O)
    rw [map_ofNat] at h3
    exact h3.ne_zero
  obtain ⟨a, b, ha, hab⟩ := res_rep h2 he0 he1 hu0
  obtain ⟨x0, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨y0, rfl⟩ := IsLocalRing.residue_surjective b
  have hx0 : IsUnit x0 := by
    by_contra hx
    apply ha
    exact (IsLocalRing.residue_eq_zero_iff x0).2 ((IsLocalRing.mem_maximalIdeal _).2 hx)
  obtain ⟨c, hc⟩ : ∃ c : O, c = (u : O) + e * y0 ^ 2 := ⟨_, rfl⟩
  let P : Polynomial O := Polynomial.X ^ 2 - Polynomial.C c
  have hPm : P.Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hP0 : P.eval x0 ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hc]
    simp only [map_sub, map_pow, map_add, map_mul]
    linear_combination hab
  have hd : P.derivative.eval x0 = 2 * x0 := by
    simp only [P, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    norm_num
  have hP1 : IsUnit (P.derivative.eval x0) := by
    rw [hd]
    exact L.two.mul hx0
  obtain ⟨x, hx, hxx⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O) P hPm x0 hP0
    (hP1.map _)
  have hxu : IsUnit x := by
    by_contra hn
    have h5 : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h6 := Ideal.sub_mem _ h5 hxx
    rw [sub_sub_cancel] at h6
    exact (IsLocalRing.mem_maximalIdeal _).1 h6 hx0
  refine ⟨hxu.unit, y0, ?_⟩
  have hx' : x ^ 2 - c = 0 := by
    have h4 := hx.eq_zero
    simpa [P] using h4
  rw [IsUnit.unit_spec]
  linear_combination hx' + hc

private theorem int_co {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ s : K} {e : O} (h : Δ * s ^ 2 = algebraMap O K e) (x y : O) :
    IsInt O (⟨algebraMap O K x, s * algebraMap O K y⟩ : Lsq K Δ) := by
  have hw : IsIntegral O (⟨0, s⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have hsq : (⟨0, s⟩ : Lsq K Δ) ^ 2 = algebraMap O (Lsq K Δ) e := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) e]
      ext
      · simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re]
        linear_combination h
      · simp only [pow_two, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_im]
        ring
    rw [hsq]
    exact isIntegral_algebraMap
  have he : (⟨algebraMap O K x, s * algebraMap O K y⟩ : Lsq K Δ)
      = algebraMap O (Lsq K Δ) x + algebraMap O (Lsq K Δ) y * ⟨0, s⟩ := by
    rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) x, IsScalarTower.algebraMap_apply O K (Lsq K Δ) y]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
        QuadraticAlgebra.algebraMap_im]
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
        QuadraticAlgebra.algebraMap_im]
      ring
  show IsIntegral O _
  rw [he]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hw)

private theorem unit_add {O : Type} [CommRing O] [IsLocalRing O] {a b : O} (ha : IsUnit a) (hb : b ∈ IsLocalRing.maximalIdeal O) :
    IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : a ∈ IsLocalRing.maximalIdeal O := by
    have h3 := Ideal.sub_mem _ h1 hb
    rwa [add_sub_cancel_right] at h3
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

private theorem choice {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ)
    (s : O) (ε : Oˣ) (hs0 : algebraMap O K s ≠ 0) (hm : s ∈ IsLocalRing.maximalIdeal O) :
    ∃ (r : K) (e : Oˣ) (ν p : Lsq K Δ) (b : K) (v w : Oˣ), Δ * r ^ 2 = algebraMap O K e ∧ IsInt O ν ∧ QuadraticAlgebra.norm ν = -1 ∧
      QuadraticAlgebra.norm p = -algebraMap O K (ε * s ^ 2) ∧ b ≠ 0 ∧ hs Δ b = hs Δ (algebraMap O K s) ∧
      p.im = r * (algebraMap O K v * b) ∧ algebraMap O K (ε * s ^ 2) + QuadraticAlgebra.trace (ν * p) = algebraMap O K w * b := by
  classical
  obtain ⟨u0, s0, hs00, hΔ⟩ := L.even
  have hL := hsLaw O K Δ L
  have hre : Δ * (s0⁻¹) ^ 2 = algebraMap O K u0 := by
    rw [hΔ]
    field_simp
  have hN : ∀ x y : K, QuadraticAlgebra.norm (⟨x, s0⁻¹ * y⟩ : Lsq K Δ) = x ^ 2 - algebraMap O K u0 * y ^ 2 := by
    intro x y
    rw [QuadraticAlgebra.norm_def]
    simp only
    linear_combination (-(y ^ 2)) * hre
  have hT : ∀ x1 y1 x2 y2 : K, QuadraticAlgebra.trace ((⟨x1, s0⁻¹ * y1⟩ : Lsq K Δ) * ⟨x2, s0⁻¹ * y2⟩)
      = 2 * (x1 * x2 + algebraMap O K u0 * y1 * y2) := by
    intro x1 y1 x2 y2
    show 2 * ((⟨x1, s0⁻¹ * y1⟩ : Lsq K Δ) * ⟨x2, s0⁻¹ * y2⟩).re + 0 * _ = _
    simp only [QuadraticAlgebra.re_mul]
    linear_combination (2 * y1 * y2) * hre
  have hS0 : (ε : O) * s ^ 2 ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 two_pos)
  by_cases hu1 : IsUnit (1 - (u0 : O))
  · have hinv1 : IsUnit (1 - ((u0⁻¹ : Oˣ) : O)) := by
      have e0 : 1 - ((u0⁻¹ : Oˣ) : O) = -((u0⁻¹ : Oˣ) : O) * (1 - u0) := by
        linear_combination -(Units.inv_mul u0)
      rw [e0]
      exact ((u0⁻¹).isUnit.neg).mul hu1
    obtain ⟨a2, a1, ha⟩ := int_rep L u0⁻¹ (u0⁻¹ * ε) hinv1
    obtain ⟨y, x, hxy⟩ := int_rep L u0⁻¹ u0⁻¹ hinv1
    rw [Units.val_mul] at ha
    have hu := Units.mul_inv u0
    have ha' : a1 ^ 2 - (u0 : O) * (a2 : O) ^ 2 = -(ε : O) := by
      linear_combination (-(u0 : O)) * ha - (a1 ^ 2 + ε) * hu
    have hxy' : x ^ 2 - (u0 : O) * (y : O) ^ 2 = -1 := by
      linear_combination (-(u0 : O)) * hxy - (x ^ 2 + 1) * hu
    obtain ⟨σ, hσ, hσu⟩ : ∃ σ : O, σ ^ 2 = 1 ∧ IsUnit (x * a1 + u0 * (σ * y) * a2) := by
      by_cases h1 : IsUnit (x * a1 + u0 * y * a2)
      · exact ⟨1, one_pow _, by simpa using h1⟩
      · refine ⟨-1, by ring, ?_⟩
        by_contra h2
        have m1 := (IsLocalRing.mem_maximalIdeal _).2 h1
        have m2 := (IsLocalRing.mem_maximalIdeal _).2 h2
        have m3 := Ideal.sub_mem _ m1 m2
        have e3 : x * a1 + (u0 : O) * y * a2 - (x * a1 + u0 * (-1 * y) * a2) = 2 * (u0 * (y * a2)) := by ring
        rw [e3] at m3
        exact (IsLocalRing.mem_maximalIdeal _).1 m3 (L.two.mul (u0.isUnit.mul (y.isUnit.mul a2.isUnit)))
    have hw := unit_add (L.two.mul hσu) (Ideal.mul_mem_left _ (ε : O) hm)
    refine ⟨s0⁻¹, u0, ⟨algebraMap O K x, s0⁻¹ * algebraMap O K (σ * y)⟩,
      ⟨algebraMap O K (s * a1), s0⁻¹ * algebraMap O K (s * a2)⟩, algebraMap O K s, a2, hw.unit,
      hre, int_co hre _ _, ?_, ?_, hs0, rfl, ?_, ?_⟩
    · rw [hN]
      have k1 : (x : O) ^ 2 - u0 * (σ * y) ^ 2 = -1 := by
        linear_combination hxy' - ((u0 : O) * (y : O) ^ 2) * hσ
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_mul, map_pow, map_neg, map_one] at k2
      simp only [map_mul]
      linear_combination k2
    · rw [hN]
      have k1 : (s * a1) ^ 2 - (u0 : O) * (s * a2) ^ 2 = -(ε * s ^ 2) := by
        linear_combination s ^ 2 * ha'
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_mul, map_pow, map_neg] at k2
      simp only [map_mul, map_pow, map_neg]
      linear_combination k2
    · show s0⁻¹ * algebraMap O K (s * a2) = s0⁻¹ * (algebraMap O K a2 * algebraMap O K s)
      rw [map_mul, mul_comm (algebraMap O K s)]
    · rw [hT, IsUnit.unit_spec]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring
  · have hm1 : (u0 : O) - 1 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro h
      apply hu1
      have h' := h.neg
      rwa [neg_sub, one_pow] at h'
    obtain ⟨c, hc, hc1⟩ := sqrtO O K Δ L u0 1 isUnit_one hm1
    have hcu : IsUnit c := by simpa using unit_add isUnit_one hc1
    have hΔ0 : Δ ≠ 0 := by
      rw [hΔ]
      exact mul_ne_zero (u0.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hs00)
    have hsq : IsSquare Δ := ⟨algebraMap O K c * s0, by rw [hΔ, ← hc, map_pow]; ring⟩
    have h1 := unit_add isUnit_one hS0
    have h12 := unit_add isUnit_one (Ideal.mul_mem_left _ 2 hS0)
    have hci := hcu.mul_val_inv
    have h2 := L.two.mul_val_inv
    have h1i := h1.mul_val_inv
    set ci : O := ((hcu.unit⁻¹ : Oˣ) : O)
    set h2i : O := ((L.two.unit⁻¹ : Oˣ) : O)
    set u1i : O := ((h1.unit⁻¹ : Oˣ) : O)
    have hbu : IsUnit (ci * h2i * (1 + ε * s ^ 2)) :=
      ((hcu.unit⁻¹).isUnit.mul (L.two.unit⁻¹).isUnit).mul h1
    refine ⟨s0⁻¹, u0, ⟨algebraMap O K 0, s0⁻¹ * algebraMap O K ci⟩,
      ⟨algebraMap O K (h2i * (1 - ε * s ^ 2)), s0⁻¹ * algebraMap O K (ci * h2i * (1 + ε * s ^ 2))⟩,
      algebraMap O K (ci * h2i * (1 + ε * s ^ 2)), 1, h12.unit * hcu.unit * L.two.unit * h1.unit⁻¹,
      hre, int_co hre _ _, ?_, ?_, (hbu.map (algebraMap O K)).ne_zero, ?_, ?_, ?_⟩
    · rw [hN]
      have k1 : (0 : O) ^ 2 - u0 * ci ^ 2 = -1 := by
        linear_combination (ci ^ 2) * hc - (c * ci + 1) * hci
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_mul, map_pow, map_neg, map_one] at k2
      linear_combination k2
    · rw [hN]
      have k1 : (h2i * (1 - ε * s ^ 2)) ^ 2 - (u0 : O) * (ci * h2i * (1 + ε * s ^ 2)) ^ 2 = -(ε * s ^ 2) := by
        linear_combination (ci ^ 2 * h2i ^ 2 * (1 + ε * s ^ 2) ^ 2) * hc
          - ((c * ci + 1) * h2i ^ 2 * (1 + ε * s ^ 2) ^ 2) * hci - ((ε * s ^ 2) * (2 * h2i + 1)) * h2
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_one] at k2
      simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_one]
      linear_combination k2
    · rw [hL.2.2.2 _ _ hΔ0 hsq, hL.2.2.2 _ _ hΔ0 hsq]
    · show s0⁻¹ * algebraMap O K (ci * h2i * (1 + ε * s ^ 2))
        = s0⁻¹ * (algebraMap O K ((1 : Oˣ) : O) * algebraMap O K (ci * h2i * (1 + ε * s ^ 2)))
      rw [Units.val_one, map_one, one_mul]
    · rw [hT]
      simp only [Units.val_mul, IsUnit.unit_spec]
      have k1 : ε * s ^ 2 + 2 * (0 * (h2i * (1 - ε * s ^ 2)) + (u0 : O) * ci * (ci * h2i * (1 + ε * s ^ 2)))
          = (1 + 2 * (ε * s ^ 2)) * c * 2 * u1i * (ci * h2i * (1 + ε * s ^ 2)) := by
        linear_combination (-(2 * ci ^ 2 * h2i * (1 + ε * s ^ 2))) * hc
          + ((1 + ε * s ^ 2) * (c * ci + 1) * (2 * h2i) - (1 + 2 * (ε * s ^ 2)) * (2 * h2i) * ((1 + ε * s ^ 2) * u1i)) * hci
          + ((1 + ε * s ^ 2) - (1 + 2 * (ε * s ^ 2)) * ((1 + ε * s ^ 2) * u1i)) * h2
          - (1 + 2 * (ε * s ^ 2)) * h1i
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_add, map_mul, map_pow, map_zero, map_ofNat, map_one] at k2
      simp only [map_add, map_mul, map_pow, map_zero, map_ofNat, map_one]
      linear_combination k2

private theorem root_tr {K : Type} [Field K] {τ : K} {u : Etau K τ} (hu : u ^ 2 = -ω) (hn : QuadraticAlgebra.norm u = 1) :
    QuadraticAlgebra.trace u ^ 2 = 2 - τ := by
  obtain ⟨x, y⟩ := u
  have e1 := congrArg QuadraticAlgebra.re hu
  have e2 := congrArg QuadraticAlgebra.im hu
  simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg,
    QuadraticAlgebra.im_neg, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im] at e1 e2
  simp only [QuadraticAlgebra.norm_def] at hn
  show (2 * x + τ * y) ^ 2 = 2 - τ
  linear_combination 2 * e1 + 2 * hn + τ * e2

private theorem move {K : Type} [Field K] {Δ τ : K} (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (hτ : 2 + τ ≠ 0) {u : Etau K τ} (hu : u ^ 2 = -ω)
    (hn : QuadraticAlgebra.norm u = 1) (z : (Etau K τ)ˣ) (hz : (z : Etau K τ) = 1 + ω) (ν p : Lsq K Δ)
    (hp : QuadraticAlgebra.norm p = -(2 + τ)) (hi : p.im ≠ 0) (r g : K) (hg : g * r * QuadraticAlgebra.trace u = 2 * p.im) :
    ∃ y : (EL Δ τ)ˣ, dLam (ν * p) z * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = ν • ofE Δ u ∧
      ∀ t : K, (t • (1 : EL Δ τ)) * (y : EL Δ τ) * star (sigL (y : EL Δ τ)) = ((t * g) • r • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ) := by
  obtain ⟨a, b⟩ := u
  have e1 := congrArg QuadraticAlgebra.re hu
  have e2 := congrArg QuadraticAlgebra.im hu
  simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg,
    QuadraticAlgebra.im_neg, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im] at e1 e2
  simp only [QuadraticAlgebra.norm_def] at hn
  have h0 : (2 + τ) * (b * (a + b)) = 0 := by linear_combination e2 + hn - e1
  have hb0 : b ≠ 0 := by
    intro hb
    subst hb
    have h3 : (1 : K) = 0 := by linear_combination -hn + e1
    exact one_ne_zero h3
  have hab : a = -b := by
    have h4 := (mul_eq_zero.1 h0).resolve_left hτ
    have h5 := (mul_eq_zero.1 h4).resolve_left hb0
    linear_combination h5
  subst hab
  have eb : (2 - τ) * b ^ 2 = 1 := by linear_combination hn
  obtain ⟨p1, p2⟩ := p
  simp only [QuadraticAlgebra.norm_def] at hp
  change p2 ≠ 0 at hi
  change g * r * (2 * (-b) + τ * b) = 2 * p2 at hg
  have hgr : g * r = -2 * b * p2 := by linear_combination (-(g * r)) * eb - b * hg
  have hc : (2 + τ)⁻¹ * (2 + τ) = 1 := inv_mul_cancel₀ hτ
  set c := (2 + τ)⁻¹ with hcdef
  have hZi : star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = (⟨c, c⟩ : Etau K τ) := by
    have hz1 : star (z : Etau K τ) * (⟨c, c⟩ : Etau K τ) = 1 := by
      rw [hz]
      refine QuadraticAlgebra.ext ?_ ?_
      · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
        linear_combination hc
      · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
        ring
    have hz2 : star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * star (z : Etau K τ) = 1 := by
      rw [← star_mul', Units.inv_mul, star_one]
    calc star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))
        = star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * (star (z : Etau K τ) * (⟨c, c⟩ : Etau K τ)) := by
          rw [hz1, mul_one]
      _ = ⟨c, c⟩ := by rw [← mul_assoc, hz2, one_mul]
  have h2τ : 2 - τ ≠ 0 := by
    intro h
    rw [h, zero_mul] at eb
    exact zero_ne_one eb
  have hD : τ ^ 2 - 4 ≠ 0 := by
    have h6 : τ ^ 2 - 4 = -((2 + τ) * (2 - τ)) := by ring
    rw [h6]
    exact neg_ne_zero.2 (mul_ne_zero hτ h2τ)
  have h4 : (4 : K) ≠ 0 := by
    have h7 : (4 : K) = 2 * 2 := by norm_num
    rw [h7]
    exact mul_ne_zero h2 h2
  let y0 : EL Δ τ := ⟨⟨p1 - τ * b, p2⟩, ⟨2 * b, 0⟩⟩
  let M : EL Δ τ := ⟨⟨0, 2 * τ * b * p2⟩, ⟨0, -4 * b * p2⟩⟩
  set κ : K := 4 * b ^ 2 * p2 ^ 2 * Δ * (τ ^ 2 - 4) with hκdef
  have hκ : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 (pow_ne_zero _ hb0)) (pow_ne_zero _ hi)) hΔ) hD
  have hM : y0 * star (sigL y0) = M := by
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination hp + (2 + τ) * eb
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
  have hMM : M * M = κ • (1 : EL Δ τ) := by
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [M, hκdef, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [M, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [M, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [M, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
  have hinv : y0 * (star (sigL y0) * (κ⁻¹ • M)) = 1 := by
    rw [← mul_assoc, hM, mul_smul_comm, hMM, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  have hI3 : dLam (ν * (⟨p1, p2⟩ : Lsq K Δ)) z * sigL y0 = (ν • ofE Δ (⟨-b, b⟩ : Etau K τ)) * y0 := by
    unfold dLam
    rw [hZi]
    obtain ⟨n1, n2⟩ := ν
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * (c * hp - (1 + b * p1) * hc + eb) + Δ * n2 * ((-b * p2) * hc)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * ((-b * p2) * hc) + n2 * (c * hp - (1 + b * p1) * hc + eb)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * (c * hp + (b * p1 - 1) * hc + eb) + Δ * n2 * ((b * p2) * hc)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * ((b * p2) * hc) + n2 * (c * hp + (b * p1 - 1) * hc + eb)
  let y : (EL Δ τ)ˣ := Units.mkOfMulEqOne y0 _ hinv
  refine ⟨y, ?_, ?_⟩
  · show dLam (ν * (⟨p1, p2⟩ : Lsq K Δ)) z * sigL y0 * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = _
    rw [hI3, mul_assoc]
    have h8 : y0 * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = 1 := Units.mul_inv y
    rw [h8, mul_one]
  · intro t
    show (t • (1 : EL Δ τ)) * y0 * star (sigL y0) = _
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination t * hp + t * (2 + τ) * eb
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination t * τ * hgr
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination (-2 * t) * hgr

private theorem hs_sq {K : Type} [Field K] (D x : K) : hs D x * hs D x = 1 := by
  unfold hs
  split_ifs <;> norm_num

theorem UpperTheory.V.Z.Sym.Loc.kapM :
    UpperTheory.V.Z.Sym.Loc.KapM := by
  unfold UpperTheory.V.Z.Sym.Loc.KapM
  intro O K _ _ _ _ _ Δ τ L hD hu0e s ε hm h2τ c hc z hz lam hlam hT
  classical
  obtain ⟨u0, hu0⟩ := hu0e
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hunit : ∀ x : O, IsUnit x → algebraMap O K x ≠ 0 := fun x hx => (hx.map (algebraMap O K)).ne_zero
  have hevu : ∀ x : Oˣ, EvenVal O (algebraMap O K x) := fun x => ⟨x, 1, one_ne_zero, by simp⟩
  have h2K : (2 : K) ≠ 0 := by
    have h3 := hunit 2 L.two
    rwa [map_ofNat] at h3
  have hΔ : Δ ≠ 0 := by
    obtain ⟨uu, ss, hss, hΔe⟩ := L.even
    rw [hΔe]
    exact mul_ne_zero (hunit _ uu.isUnit) (pow_ne_zero 2 hss)
  have hc0 : c ≠ 0 := by
    obtain ⟨cu, cs, hcs, hce⟩ := hc
    rw [hce]
    exact mul_ne_zero (hunit _ cu.isUnit) (pow_ne_zero 2 hcs)
  have h2t : (2 : K) + τ ≠ 0 := by
    intro h0
    apply hD
    linear_combination (τ - 2) * h0
  have hs0 : algebraMap O K s ≠ 0 := by
    intro h0
    apply h2t
    rw [h2τ, map_mul, map_pow, h0]
    ring
  have h2τ' : (2 : K) + τ = algebraMap O K ε * algebraMap O K s ^ 2 := by
    rw [h2τ, map_mul, map_pow]
  have hDalg : τ ^ 2 - 4 = algebraMap O K (((-(u0 * ε) : Oˣ) : O) * s ^ 2) := by
    simp only [Units.val_neg, Units.val_mul, map_mul, map_neg, map_pow]
    linear_combination (algebraMap O K ε * algebraMap O K s ^ 2) * hu0 - (2 - τ) * h2τ'
  have hDv : EvenVal O (τ ^ 2 - 4) := ⟨-(u0 * ε), algebraMap O K s, hs0, by rw [hDalg, map_mul, map_pow]⟩
  have hL := hsLaw O K Δ L
  have hτ0 : algebraMap O K ((ε : O) * s ^ 2 - 2) = τ := by
    rw [map_sub, map_ofNat, ← h2τ]
    ring
  have hm0 : ((ε : O) * s ^ 2 - 2) + 2 ∈ IsLocalRing.maximalIdeal O := by
    rw [sub_add_cancel, pow_two, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ hm
  have hre : ((ε : O) * s ^ 2 - 2) - 2 * (((-1 : ℤˣ) : ℤ) : O) = ((ε : O) * s ^ 2 - 2) + 2 := by
    push_cast
    ring
  obtain ⟨xr, yr, hyr, hsq, hnorm⟩ := rootEx O K Δ τ L ((ε : O) * s ^ 2 - 2) (-1) hτ0 (by rw [hre]; exact hm0)
  have hu2 : (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ) ^ 2 = -ω := by
    rw [hsq]
    simp
  have htr : QuadraticAlgebra.trace (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ)
      = algebraMap O K (2 * xr + ((ε : O) * s ^ 2 - 2) * yr) := by
    show 2 * algebraMap O K xr + τ * algebraMap O K yr = _
    rw [map_add, map_mul, map_mul, hτ0, map_ofNat]
  have ht2 := root_tr hu2 hnorm
  have ht0u : IsUnit (2 * xr + ((ε : O) * s ^ 2 - 2) * yr) := by
    have h5 : (2 * xr + ((ε : O) * s ^ 2 - 2) * yr) ^ 2 = u0 := by
      apply hinj
      rw [map_pow, ← htr, ht2, hu0]
    have h6 : IsUnit ((2 * xr + ((ε : O) * s ^ 2 - 2) * yr) ^ 2) := by
      rw [h5]
      exact u0.isUnit
    exact (isUnit_pow_iff (by norm_num)).1 h6
  obtain ⟨r, e, ν, p, b, v, w, hr, hν, hnν, hnp, hb0, hsb, hpim, hT2⟩ := choice L s ε hs0 hm
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hunit _ e.isUnit
    rw [← hr]
    ring
  have htr0 : QuadraticAlgebra.trace (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ) ≠ 0 := by
    rw [htr]
    exact hunit _ ht0u
  have hpim0 : p.im ≠ 0 := by
    rw [hpim]
    exact mul_ne_zero hr0 (mul_ne_zero (hunit _ v.isUnit) hb0)
  obtain ⟨g, hgdef⟩ : ∃ g : K, g = 2 * p.im / (r * QuadraticAlgebra.trace
      (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ)) := ⟨_, rfl⟩
  have hg : g * r * QuadraticAlgebra.trace (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ) = 2 * p.im := by
    rw [hgdef]
    field_simp
  have hg0 : g ≠ 0 := by
    rw [hgdef]
    exact div_ne_zero (mul_ne_zero h2K hpim0) (mul_ne_zero hr0 htr0)
  have hnp' : QuadraticAlgebra.norm p = -(2 + τ) := by rw [hnp, h2τ]
  obtain ⟨y, hy1, hy2⟩ := move h2K hΔ h2t hu2 hnorm z hz ν p hnp' hpim0 r g hg
  have hcase : ∀ t : Kˣ, lcount O c (ν • ofE Δ (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ))
      (((↑t * g) • r • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ))
      = pcount O τ (↑t * (g * (τ ^ 2 - 4))) := by
    intro t
    have h7 := caseM O K Δ τ L hD ((ε : O) * s ^ 2 - 2) hτ0 hm0 c hc _ hu2 hnorm ν hν hnν r e hr
      (t * Units.mk0 g hg0)
    rw [Units.val_mul, Units.val_mk0, mul_assoc] at h7
    exact h7
  have hK2 : kapSum O c (dLam (ν * p) z) 1 = ∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K)
      * pcount O τ (((Quotient.out t : Kˣ) : K) * (g * (τ ^ 2 - 4))) := by
    unfold UpperTheory.V.Z.Sym.Loc.kapSum
    refine finsum_congr (fun t => ?_)
    congr 1
    rw [(datIso O K Δ τ c (dLam (ν * p) z) (((Quotient.out t : Kˣ) : K) • (1 : EL Δ τ)) y).1, hy1, hy2,
      hcase]
  have hinvf : ∀ t ∈ NE τ, ∀ x : Kˣ, (fun t : Kˣ => pcount O τ (t : K)) (t * x)
      = (fun t : Kˣ => pcount O τ (t : K)) x := by
    intro t ht x
    simp only [Units.val_mul]
    exact pNorm O K Δ τ L t ht x
  have hSS := (sumShift O K Δ τ L hD (fun t : Kˣ => pcount O τ (t : K)) hinvf
    (Units.mk0 g hg0 * Units.mk0 _ hD)).2.1
  simp only [Units.val_mul, Units.val_mk0] at hSS
  have hPK := pKappa O K Δ τ L hD ⟨_, hτ0⟩ s (-(u0 * ε)) hDalg
  rw [hPK] at hSS
  rw [hSS] at hK2
  have hsDD : hs (τ ^ 2 - 4) (τ ^ 2 - 4) = 1 := by
    have h8 : hs (τ ^ 2 - 4) (-(τ ^ 2 - 4)) = 1 := by
      unfold UpperTheory.V.Z.Sym.Loc.hs
      rw [if_pos ⟨0, 1, by ring⟩]
    have h9 : hs (τ ^ 2 - 4) (-1) = 1 := hL.2.1 _ _ hDv ⟨-1, 1, one_ne_zero, by simp⟩
    have h10 := hsMul O K Δ L (τ ^ 2 - 4) (-1) (-(τ ^ 2 - 4)) hD (by norm_num) (neg_ne_zero.2 hD)
    rw [show (-1 : K) * -(τ ^ 2 - 4) = τ ^ 2 - 4 by ring, h9, h8, one_mul] at h10
    exact h10
  have e2v : EvenVal O (algebraMap O K (2 * v)) := by
    have h11 := hevu (L.two.unit * v)
    simpa using h11
  have et0 : EvenVal O (algebraMap O K (2 * xr + ((ε : O) * s ^ 2 - 2) * yr)) := by
    have h11 := hevu ht0u.unit
    simpa using h11
  have hgb : g / b = algebraMap O K (2 * v) * (algebraMap O K (2 * xr + ((ε : O) * s ^ 2 - 2) * yr))⁻¹ := by
    rw [hgdef, hpim, htr, map_mul, map_ofNat]
    field_simp
  have hevgb : EvenVal O (g / b) := by
    rw [hgb]
    exact PS.even_mul e2v (PS.even_inv et0)
  have hsDg : hs (τ ^ 2 - 4) (g * (τ ^ 2 - 4)) = hs (τ ^ 2 - 4) b := by
    rw [hsMul O K Δ L _ _ _ hD hg0 hD, hsDD, mul_one,
      show g = g / b * b by field_simp,
      hsMul O K Δ L _ _ _ hD (div_ne_zero hg0 hb0) hb0, hL.2.1 _ _ hDv hevgb, one_mul]
  have heps2 : eps τ (ν * p) = hs Δ (algebraMap O K s) * hs (τ ^ 2 - 4) b := by
    unfold UpperTheory.V.Z.Sym.Loc.eps
    rw [show (2 : K) + τ + QuadraticAlgebra.trace (ν * p) = algebraMap O K w * b by rw [h2τ, hT2],
      hsMul O K Δ L _ _ _ hD (hunit _ w.isUnit) hb0, hsMul O K Δ L _ _ _ hΔ (hunit _ w.isUnit) hb0,
      hL.2.1 _ _ hDv (hevu w), hL.2.1 _ _ L.even (hevu w), hsb]
    ring
  have heps1 : eps τ lam * eps τ lam = 1 := by
    unfold UpperTheory.V.Z.Sym.Loc.eps
    linear_combination (hs Δ (2 + τ + QuadraticAlgebra.trace lam) * hs Δ (2 + τ + QuadraticAlgebra.trace lam))
      * hs_sq (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) + hs_sq Δ (2 + τ + QuadraticAlgebra.trace lam)
  have hnνp : QuadraticAlgebra.norm (ν * p) = 2 + τ := by
    rw [map_mul, hnν, hnp, ← h2τ]
    ring
  have hTνp : 2 + τ + QuadraticAlgebra.trace (ν * p) ≠ 0 := by
    rw [h2τ, hT2]
    exact mul_ne_zero (hunit _ w.isUnit) hb0
  have hM := kapMove O K Δ τ L hD c hc0 z hz lam (ν * p) hlam hnνp hT hTνp
  rw [hK2, heps2, hsDg] at hM
  linear_combination (-(kapSum O c (dLam lam z) 1)) * heps1 + eps τ lam * hM
    + (eps τ lam * hs Δ (algebraMap O K s) * (Nat.card (O ⧸ Ideal.span {s}) : ℂ)) * hs_sq (τ ^ 2 - 4) b
