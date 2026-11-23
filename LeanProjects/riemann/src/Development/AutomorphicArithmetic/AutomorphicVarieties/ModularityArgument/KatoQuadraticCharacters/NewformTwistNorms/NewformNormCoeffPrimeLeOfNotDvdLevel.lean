import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace GlobalTheory.HeckeBd

private theorem one_mem_strictPeriods_map_gamma1 (M : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 M)).strictPeriods := by
  rw [show (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 M)) =
    ((Gamma1 M : Subgroup (GL (Fin 2) ℝ))) from rfl, strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem no_weight_zero (g : Newform 0) : False := by
  haveI : NeZero g.M := ⟨g.pos.ne'⟩
  let F : ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 g.M)) 0 :=
    { toFun := g.f
      holo' := ModularFormClass.holo g.f
      bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps g.f hc
      slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq g.f γ hγ }
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  have hF : (F : ℍ → ℂ) = g.f := rfl
  have hz := CuspFormClass.zero_at_infty g.f
  rw [← hF, hc] at hz
  have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  have h0 : (g.f : ℍ → ℂ) = 0 := by
    rw [← hF, hc, hc0]
    rfl
  have h1 := g.one
  rw [h0, UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at h1
  simp at h1

theorem expand (k : ℕ) (g : Newform k) (τ : ℍ) :
    HasSum (fun m : ℕ => g.a m * Function.Periodic.qParam 1 τ ^ m) (g.f τ) := by
  haveI : NeZero g.M := ⟨g.pos.ne'⟩
  have := ModularForm.hasSum_qExpansion (f := g.f) one_pos (one_mem_strictPeriods_map_gamma1 g.M) τ
  simpa [Newform.a, UpperTheory.V.Af.coef, Nat.cast_one] using this

theorem a_zero (k : ℕ) (g : Newform k) : g.a 0 = 0 := by
  haveI : NeZero g.M := ⟨g.pos.ne'⟩
  simpa [Newform.a, UpperTheory.V.Af.coef] using CuspFormClass.qExpansion_coeff_zero g.f one_pos (one_mem_strictPeriods_map_gamma1 g.M)

theorem im_shift (z : ℍ) (b p : ℕ) (hp : 0 < p) : (((z : ℂ) + b) / p).im = z.im / p := by
  simp [Complex.div_natCast_im]

theorem im_scale (z : ℍ) (p : ℕ) : ((p : ℂ) * z).im = p * z.im := by
  simp

end GlobalTheory.HeckeBd

namespace GlobalTheory.HeckeBd

theorem qParam_shift (z : ℍ) (b p : ℕ) (hp : 0 < p) (m : ℕ) :
    Function.Periodic.qParam 1 (((z : ℂ) + b) / p) ^ m =
      Complex.exp (2 * Real.pi * Complex.I * z / p) ^ m *
        (Complex.exp (2 * Real.pi * Complex.I / p) ^ m) ^ b := by
  have e : Function.Periodic.qParam 1 (((z : ℂ) + b) / p) =
      Complex.exp (2 * Real.pi * Complex.I * z / p) * Complex.exp (2 * Real.pi * Complex.I / p) ^ b := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, mul_pow, ← pow_mul, ← pow_mul, mul_comm m b]

theorem geom_root (p : ℕ) (hp : p.Prime) (m : ℕ) :
    ∑ b ∈ Finset.range p, (Complex.exp (2 * Real.pi * Complex.I / p) ^ m) ^ b =
      if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne_zero
  split_ifs with h
  · have : Complex.exp (2 * Real.pi * Complex.I / p) ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).mpr h
    simp [this]
  · have hc : Nat.Coprime m p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
    exact (hζ.pow_of_coprime m hc).geom_sum_eq_zero hp.one_lt

theorem sum_shift (k : ℕ) (g : Newform k) (p : ℕ) (hp : p.Prime) (z : ℍ) :
    HasSum (fun n : ℕ => (p : ℂ) * g.a (p * n) * Function.Periodic.qParam 1 z ^ n)
      (∑ b ∈ Finset.range p, g.f (ofComplex (((z : ℂ) + b) / p))) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : ∀ b ∈ Finset.range p, HasSum
      (fun m : ℕ => g.a m * Function.Periodic.qParam 1 (((z : ℂ) + b) / p) ^ m)
      (g.f (ofComplex (((z : ℂ) + b) / p))) := by
    intro b _
    have him : 0 < (((z : ℂ) + b) / p).im := by
      rw [im_shift z b p hp.pos]
      exact div_pos z.im_pos hpos
    have e : ((ofComplex (((z : ℂ) + b) / p) : ℍ) : ℂ) = ((z : ℂ) + b) / p := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    have := expand k g (ofComplex (((z : ℂ) + b) / p))
    rwa [e] at this
  have hs := hasSum_sum hb
  have key : ∀ m : ℕ, (∑ b ∈ Finset.range p,
      g.a m * Function.Periodic.qParam 1 (((z : ℂ) + b) / p) ^ m) =
      if p ∣ m then (p : ℂ) * g.a m * Complex.exp (2 * Real.pi * Complex.I * z / p) ^ m else 0 := by
    intro m
    calc (∑ b ∈ Finset.range p, g.a m * Function.Periodic.qParam 1 (((z : ℂ) + b) / p) ^ m)
        = ∑ b ∈ Finset.range p, g.a m * Complex.exp (2 * Real.pi * Complex.I * z / p) ^ m *
            (Complex.exp (2 * Real.pi * Complex.I / p) ^ m) ^ b :=
          Finset.sum_congr rfl (fun b _ => by rw [qParam_shift z b p hp.pos m]; ring)
      _ = g.a m * Complex.exp (2 * Real.pi * Complex.I * z / p) ^ m *
            ∑ b ∈ Finset.range p, (Complex.exp (2 * Real.pi * Complex.I / p) ^ m) ^ b := by
          rw [Finset.mul_sum]
      _ = _ := by
          rw [geom_root p hp m]
          split_ifs <;> ring
  have hs' : HasSum (fun m : ℕ => if p ∣ m then
      (p : ℂ) * g.a m * Complex.exp (2 * Real.pi * Complex.I * z / p) ^ m else 0)
      (∑ b ∈ Finset.range p, g.f (ofComplex (((z : ℂ) + b) / p))) := by
    convert hs using 1
    funext m
    exact (key m).symm
  have hinj : Function.Injective (fun n : ℕ => p * n) := fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h
  have hz : ∀ x ∉ Set.range (fun n : ℕ => p * n), (if p ∣ x then
      (p : ℂ) * g.a x * Complex.exp (2 * Real.pi * Complex.I * z / p) ^ x else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨n, rfl⟩
    exact hx ⟨n, rfl⟩
  have := (hinj.hasSum_iff hz).mpr hs'
  convert this using 1
  funext n
  simp only [Function.comp_apply, if_pos (dvd_mul_right p n)]
  congr 1
  rw [pow_mul, ← Complex.exp_nat_mul, Function.Periodic.qParam]
  congr 2
  have : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp

end GlobalTheory.HeckeBd

namespace GlobalTheory.HeckeBd

theorem scale (k : ℕ) (g : Newform k) (p : ℕ) (hp : p.Prime) (z : ℍ) :
    HasSum (fun n : ℕ => (if p ∣ n then g.a (n / p) else 0) * Function.Periodic.qParam 1 z ^ n)
      (g.f (ofComplex ((p : ℂ) * z))) := by
  have him : 0 < ((p : ℂ) * z).im := by
    rw [im_scale z p]
    exact mul_pos (by exact_mod_cast hp.pos) z.im_pos
  have e : ((ofComplex ((p : ℂ) * z) : ℍ) : ℂ) = (p : ℂ) * z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have h0 := expand k g (ofComplex ((p : ℂ) * z))
  rw [e] at h0
  have hinj : Function.Injective (fun n : ℕ => p * n) := fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h
  have hz : ∀ x ∉ Set.range (fun n : ℕ => p * n),
      (if p ∣ x then g.a (x / p) else 0) * Function.Periodic.qParam 1 z ^ x = 0 := by
    intro x hx
    rw [if_neg, zero_mul]
    rintro ⟨n, rfl⟩
    exact hx ⟨n, rfl⟩
  refine (hinj.hasSum_iff hz).mp ?_
  convert h0 using 1
  funext m
  simp only [Function.comp_apply, if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos]
  congr 1
  rw [pow_mul, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hecke_identity (k : ℕ) (g : Newform k) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ g.M) (z : ℍ) :
    g.a p * g.f z = (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, g.f (ofComplex (((z : ℂ) + b) / p))
      + g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1) * g.f (ofComplex ((p : ℂ) * z)) := by
  have e := g.eig p hp hpM
  unfold UpperTheory.V.Af.IsEigAt at e
  have ea : ∀ m, g.a m = UpperTheory.V.Af.coef g.f m := fun m => rfl
  have h1 := (expand k g z).mul_left (g.a p)
  have h2 := ((sum_shift k g p hp z).mul_left ((p : ℂ)⁻¹)).add
    ((scale k g p hp z).mul_left (g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1)))
  refine h1.unique ?_
  convert h2 using 1
  funext n
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_zero]
  · have hn' := e n hn
    simp only [ea]
    rw [← mul_assoc, ← hn']
    field_simp

end GlobalTheory.HeckeBd

namespace GlobalTheory.HeckeBd

theorem norm_a_le : ∀ (k : ℕ) (g : Newform k) (p : ℕ), p.Prime → ¬ p ∣ g.M →
    ‖g.a p‖ ≤ (p : ℝ) ^ ((k : ℝ) / 2) + (p : ℝ) ^ ((k : ℝ) / 2 - 1) := by
  intro k g p hp hpM
  haveI : NeZero g.M := ⟨g.pos.ne'⟩
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact (no_weight_zero g).elim
    · exact h
  set r : ℝ := (k : ℝ) / 2 with hr
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound g.f
  let φ : ℍ → ℝ := fun τ => ‖g.f τ‖ * τ.im ^ r
  have hφC : ∀ τ, φ τ ≤ C := by
    intro τ
    have h := hC τ
    have hpos : 0 < τ.im ^ r := Real.rpow_pos_of_pos τ.im_pos r
    have hc : ((((k : ℤ)) : ℝ) / 2) = r := by simp [hr]
    rw [hc, le_div_iff₀ hpos] at h
    exact h
  have hbdd : BddAbove (Set.range φ) := ⟨C, by rintro _ ⟨τ, rfl⟩; exact hφC τ⟩
  set S := ⨆ τ, φ τ with hSdef
  have hφS : ∀ τ, φ τ ≤ S := fun τ => le_ciSup hbdd τ
  have hfS : ∀ τ : ℍ, ‖g.f τ‖ ≤ S / τ.im ^ r := by
    intro τ
    rw [le_div_iff₀ (Real.rpow_pos_of_pos τ.im_pos r)]
    exact hφS τ
  have key : ∀ z : ℍ, ‖g.a p‖ * φ z ≤ ((p : ℝ) ^ r + (p : ℝ) ^ (r - 1)) * S := by
    intro z
    have hy := z.im_pos
    have hid := hecke_identity k g p hp hpM z
    have hnorm : ‖g.a p‖ * ‖g.f z‖ ≤ (p : ℝ)⁻¹ * ∑ b ∈ Finset.range p,
        ‖g.f (ofComplex (((z : ℂ) + b) / p))‖ + (p : ℝ) ^ (k - 1) * ‖g.f (ofComplex ((p : ℂ) * z))‖ := by
      rw [← norm_mul, hid]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_inv, Complex.norm_natCast]
        gcongr
        exact norm_sum_le _ _
      · rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
        have hχ : ‖g.χ (p : ZMod g.M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        calc _ ≤ 1 * (p : ℝ) ^ (k - 1) * ‖g.f (ofComplex ((p : ℂ) * z))‖ := by gcongr
          _ = _ := by ring
    have hb : ∀ b ∈ Finset.range p, ‖g.f (ofComplex (((z : ℂ) + b) / p))‖ ≤ S / (z.im / p) ^ r := by
      intro b _
      have him : 0 < (((z : ℂ) + b) / p).im := by
        rw [im_shift z b p hp.pos]
        exact div_pos hy hp0
      have e : (ofComplex (((z : ℂ) + b) / p)).im = z.im / p := by
        (rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, ← im_shift z b p hp.pos]) <;> rfl
      have := hfS (ofComplex (((z : ℂ) + b) / p))
      rwa [e] at this
    have hs : ‖g.f (ofComplex ((p : ℂ) * z))‖ ≤ S / (p * z.im) ^ r := by
      have him : 0 < ((p : ℂ) * z).im := by
        rw [im_scale z p]
        exact mul_pos hp0 hy
      have e : (ofComplex ((p : ℂ) * z)).im = p * z.im := by
        (rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, ← im_scale z p]) <;> rfl
      have := hfS (ofComplex ((p : ℂ) * z))
      rwa [e] at this
    have hsum : ∑ b ∈ Finset.range p, ‖g.f (ofComplex (((z : ℂ) + b) / p))‖ ≤
        p * (S / (z.im / p) ^ r) := by
      calc _ ≤ ∑ b ∈ Finset.range p, S / (z.im / p) ^ r := Finset.sum_le_sum hb
        _ = _ := by simp
    have hyr : 0 < z.im ^ r := Real.rpow_pos_of_pos hy r
    have hpr : 0 < (p : ℝ) ^ r := Real.rpow_pos_of_pos hp0 r
    have e1 : (p : ℝ) ^ (k - 1) = (p : ℝ) ^ (r - 1) * (p : ℝ) ^ r := by
      rw [← Real.rpow_add hp0, ← Real.rpow_natCast, Nat.cast_sub hk]
      congr 1
      rw [hr]
      push_cast
      ring
    have hbound : ‖g.a p‖ * ‖g.f z‖ ≤ (p : ℝ)⁻¹ * (p * (S / (z.im / p) ^ r)) +
        (p : ℝ) ^ (k - 1) * (S / (p * z.im) ^ r) := by
      refine hnorm.trans (add_le_add ?_ ?_)
      · gcongr
      · gcongr
    calc ‖g.a p‖ * φ z = (‖g.a p‖ * ‖g.f z‖) * z.im ^ r := by simp only [φ]; ring
      _ ≤ ((p : ℝ)⁻¹ * (p * (S / (z.im / p) ^ r)) +
          (p : ℝ) ^ (k - 1) * (S / (p * z.im) ^ r)) * z.im ^ r := by gcongr
      _ = _ := by
        rw [e1, Real.div_rpow hy.le hp0.le, Real.mul_rpow hp0.le hy.le]
        field_simp
  have hne : ∃ τ, 0 < φ τ := by
    by_contra hcon
    push_neg at hcon
    have h0 : (g.f : ℍ → ℂ) = 0 := by
      funext τ
      have h1 := hcon τ
      have hpos : 0 < τ.im ^ r := Real.rpow_pos_of_pos τ.im_pos r
      have h2 : ‖g.f τ‖ ≤ 0 := by
        by_contra h'
        push_neg at h'
        exact absurd (mul_pos h' hpos) (not_lt.mpr h1)
      simpa using norm_le_zero_iff.mp h2
    have h1 := g.one
    rw [h0, UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at h1
    simp at h1
  obtain ⟨τ0, hτ0⟩ := hne
  have hSpos : 0 < S := lt_of_lt_of_le hτ0 (hφS τ0)
  have hmain : ‖g.a p‖ * S ≤ ((p : ℝ) ^ r + (p : ℝ) ^ (r - 1)) * S := by
    rw [hSdef, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    exact ciSup_le key
  exact le_of_mul_le_mul_right hmain hSpos

end GlobalTheory.HeckeBd

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_norm_coeff_prime_le_of_not_dvd_level : ∀ (k : ℕ) (g : Newform k) (p : ℕ), p.Prime → ¬ p ∣ g.M → ‖g.a p‖ ≤ (p : ℝ) ^ ((k : ℝ) / 2) + (p : ℝ) ^ ((k : ℝ) / 2 - 1) := by
  first | exact @GlobalTheory.HeckeBd.norm_a_le | exact GlobalTheory.HeckeBd.norm_a_le | (intros; apply GlobalTheory.HeckeBd.norm_a_le <;> assumption)

end
