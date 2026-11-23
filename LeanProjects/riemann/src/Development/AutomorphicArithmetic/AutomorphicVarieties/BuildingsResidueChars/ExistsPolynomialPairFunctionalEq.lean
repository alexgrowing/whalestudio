import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalGammaFactorExponentialForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FunctionalEquationFromContinuation
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductAdjointEqStandard
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductNonvanishingRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem fac_mul (c c' : ℂ) (t t' q : ℝ) (P P' : ℂ[X]) (s : ℂ) :
    fac c t q P s * fac c' t' q P' s = fac (c * c') (t + t') q (P * P') s := by
  simp only [fac, eval_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [div_mul_div_comm]
  congr 1
  ring

private theorem fac_one (c : ℂ) (t q q' : ℝ) (s : ℂ) : fac c t q 1 s = fac c t q' 1 s := by
  simp only [fac, eval_one]

private def IsFac (f : ℂ → ℂ) (q : ℝ) (P : ℂ[X]) : Prop := ∃ (c : ℂ) (t : ℝ), ∀ s : ℂ, f s = fac c t q P s

private theorem IsFac.mul {f g : ℂ → ℂ} {q : ℝ} {P Q : ℂ[X]} (hf : IsFac f q P) (hg : IsFac g q Q) :
    IsFac (fun s => f s * g s) q (P * Q) := by
  obtain ⟨c, t, h⟩ := hf
  obtain ⟨c', t', h'⟩ := hg
  exact ⟨c * c', t + t', fun s => by rw [← fac_mul, ← h, ← h']⟩

private theorem IsFac.one {f : ℂ → ℂ} {q : ℝ} (q' : ℝ) (hf : IsFac f q 1) : IsFac f q' 1 := by
  obtain ⟨c, t, h⟩ := hf
  exact ⟨c, t, fun s => (h s).trans (fac_one c t q q' s)⟩

private theorem isFac_prod_one {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (q : ℝ) (h : ∀ u ∈ S, IsFac (f u) q 1) :
    IsFac (fun s => ∏ u ∈ S, f u s) q 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 0, fun s => by simp [fac]⟩
  | insert a S ha ih =>
    have h1 := (h a (Finset.mem_insert_self _ _)).mul (ih fun u hu => h u (Finset.mem_insert_of_mem hu))
    rw [mul_one] at h1
    simpa only [Finset.prod_insert ha] using h1

private theorem isFac_prod {ι : Type} (S : Finset ι) (v : ι) (hv : v ∈ S) (f : ι → ℂ → ℂ) (q : ℝ) (P : ℂ[X])
    (h0 : IsFac (f v) q P) (h : ∀ u ∈ S, u ≠ v → IsFac (f u) q 1) : IsFac (fun s => ∏ u ∈ S, f u s) q P := by
  have h1 := h0.mul (isFac_prod_one (S.erase v) f q fun u hu => h u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu))
  rw [mul_one] at h1
  obtain ⟨c, t, h1⟩ := h1
  exact ⟨c, t, fun s => by rw [← h1 s]; exact (Finset.mul_prod_erase S (fun u => f u s) hv).symm⟩

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem unit_mul {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (h' : Ad3.IsUnit1 c) : Ad3.IsUnit1 (ν * c) :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h.2, h'.2, mul_one]⟩

private theorem unit_inv {ν : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) : Ad3.IsUnit1 ν⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2, inv_one]⟩

private theorem lin_ne {ν : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (x : ℂ) (hx : 1 < ‖x‖) : (lin ν).eval x ≠ 0 := by
  unfold lin
  split_ifs
  · simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro h0
    have h1 := congrArg norm (sub_eq_zero.1 h0)
    rw [norm_one, norm_mul, h.2, one_mul] at h1
    linarith
  · simp

private theorem local_linear_factor_ne_zero {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (h' : Ad3.IsUnit1 c) (x : ℂ) (hx : 1 < ‖x‖) :
    (lin3 ν c).eval x ≠ 0 := by
  simp only [lin3, eval_mul]
  exact mul_ne_zero (mul_ne_zero (lin_ne (unit_mul h h') x hx) (lin_ne h' x hx)) (lin_ne (unit_mul (unit_inv h) h') x hx)

private theorem local_linear_factor_ramified {ν c : Fˣ →* ℂˣ} (h : Ram3 ν c) : lin3 ν c = 1 := by
  simp only [lin3, lin, if_neg h.1, if_neg h.2.1, if_neg h.2.2, mul_one]

private theorem gamma_factor_rank_three_form [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν)
    (h' : Ad3.IsUnit1 c) : IsFac (Ad3.gam3 ψ ν c) (residueCard F : ℝ) (lin3 ν c) :=
  IsFac.mul (f := fun s => Ad3.gam ψ (ν * c) s * Ad3.gam ψ c s)
    (IsFac.mul (UpperTheory.local_gamma_factor_exponential_form F ψ _ (unit_mul h h').1) (UpperTheory.local_gamma_factor_exponential_form F ψ _ h'.1))
    (UpperTheory.local_gamma_factor_exponential_form F ψ _ (unit_mul (unit_inv h) h').1)

end Loc

private theorem lR_ne (k : ℕ) (hk : 3 ≤ k) (δ : Bool) (s : ℂ) (hs : 0 < s.re) : Ad3.lR k δ s ≠ 0 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  refine mul_ne_zero ?_ (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
  · rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
    · rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h, -⟩
      simp at h
    · simp
      linarith
  · cases δ <;> simp <;> linarith

private theorem arch_eq (k : ℕ) (δ : Bool) (s : ℂ) : arch k s = Ad3.lR k δ s * Ad3.lR k (!δ) s := by
  cases δ
  · exact mul_comm _ _
  · rfl

private theorem gamR_pair (k : ℕ) (hk : 3 ≤ k) (δ : Bool) : ∃ g : ℂ, ∀ s : ℂ, 0 < s.re →
    Ad3.gamR k δ s * Ad3.gamR k (!δ) s * arch k s = g * arch k (1 - s) := by
  refine ⟨(-Complex.I) ^ (2 * k - if δ then 1 else 0) * (-Complex.I) ^ (2 * k - if (!δ) then 1 else 0), fun s hs => ?_⟩
  have h1 := lR_ne k hk δ s hs
  have h2 := lR_ne k hk (!δ) s hs
  rw [arch_eq k δ, arch_eq k δ, Ad3.gamR, Ad3.gamR]
  field_simp

private theorem loc_unit (c : HeckeCharacter ℚ) (v : Ad3.Pl) : Ad3.IsUnit1 (localChar c v) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c v, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar, Circle.norm_coe]⟩

private theorem loc_fac (D : Ad3.Dat) (c : HeckeCharacter ℚ) (v : Ad3.Pl) :
    IsFac (Ad3.gam3 (localAdelicChar ℚ v) (D.ν v) (localChar c v)) (Ideal.absNorm v.asIdeal : ℝ) (lin3 (D.ν v) (localChar c v)) := by
  have h := gamma_factor_rank_three_form (localAdelicChar ℚ v) (D.unit v) (loc_unit c v)
  rwa [residueCard_adicCompletion] at h

private theorem fin_fac (D : Ad3.Dat) (c : HeckeCharacter ℚ) (S : Finset Ad3.Pl) (v : Ad3.Pl) (hv : v ∈ S)
    (h : ∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c u)) :
    IsFac (fun s => ∏ u ∈ S, Ad3.gam3 (localAdelicChar ℚ u) (D.ν u) (localChar c u) s) (Ideal.absNorm v.asIdeal : ℝ)
      (lin3 (D.ν v) (localChar c v)) :=
  isFac_prod S v hv (fun u => Ad3.gam3 (localAdelicChar ℚ u) (D.ν u) (localChar c u)) _ _ (loc_fac D c v) fun u hu huv => by
    have h1 := loc_fac D c u
    rw [local_linear_factor_ramified (h u hu huv)] at h1
    exact h1.one _

private theorem eul_ne (D : Ad3.Dat) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Ad3.Pl) (h : Ad3.admitted D c δ S) :
    Ad3.eul D c S 3 ≠ 0 := by
  rw [(UpperTheory.euler_product_adjoint_eq_standard D c δ S h 3).1]
  exact UpperTheory.euler_product_nonvanishing_right D c S 3 (by norm_num)

theorem UpperTheory.exists_polynomial_pair_functional_eq :
    ∀ D : Ad3.Dat, Ad3.An D → ∀ (c₁ c₂ : HeckeCharacter ℚ) (δ : Bool) (S : Finset Ad3.Pl) (v : Ad3.Pl),
        Ad3.admitted D c₁ δ S → Ad3.admitted D c₂ (!δ) S → v ∈ S →
        (∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c₁ u) ∧ Ram3 (D.ν u) (localChar c₂ u)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG (fun s => Ad3.eul D c₁ S s * Ad3.eul D c₂ S s)
          (fun s => Ad3.eul D c₁⁻¹ S (1 - s) * Ad3.eul D c₂⁻¹ S (1 - s)) β (Ideal.absNorm v.asIdeal : ℝ)
          (lin3 (D.ν v) (localChar c₁ v) * lin3 (D.ν v) (localChar c₂ v)) := by
  intro D hD c₁ c₂ δ S v h₁ h₂ hv hr
  obtain ⟨Λ₁, Λ₁', a₁, b₁, e₁⟩ := hD c₁ δ S h₁
  obtain ⟨Λ₂, Λ₂', a₂, b₂, e₂⟩ := hD c₂ (!δ) S h₂
  obtain ⟨g, hg⟩ := gamR_pair D.k D.three δ
  obtain ⟨c₀, t, hf⟩ := (fin_fac D c₁ S v hv fun u hu h => (hr u hu h).1).mul (fin_fac D c₂ S v hv fun u hu h => (hr u hu h).2)
  refine UpperTheory.functional_equation_from_continuation D.k _ _ (fun s => Λ₁ s * Λ₂ s) (fun s => Λ₁' s * Λ₂' s) g c₀ t _ _ D.three
    (by exact_mod_cast one_lt_absNorm_asIdeal v) (a₁.1.mul a₂.1) (b₁.1.mul b₂.1) (fun s hs => ?_) (fun s hs => ?_)
    ⟨3, by norm_num, mul_ne_zero (eul_ne D c₁ δ S h₁) (eul_ne D c₂ _ S h₂)⟩ (fun x hx => ?_) (fun s hs hs' => ?_)
  · simp only [a₁.2.2 s hs, a₂.2.2 s hs, pow_zero, one_mul]
  · have h : 1 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    simp only [b₁.2.2 _ h, b₂.2.2 _ h, pow_zero, one_mul]
  · rw [eval_mul]
    exact mul_ne_zero (local_linear_factor_ne_zero (D.unit v) (loc_unit c₁ v) x hx) (local_linear_factor_ne_zero (D.unit v) (loc_unit c₂ v) x hx)
  · rw [← hf s, ← hg s (by linarith)]
    simp only [e₁ s hs hs', e₂ s hs hs', Ad3.gamS]
    ring
