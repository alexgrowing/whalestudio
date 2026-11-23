import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.StabilizerEqScalarMulCongruenceMulFinset
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsInGScalarMulAndAbsNormDetMulAbsFEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicBoundAlgebraProperties
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) : reAt v x = rhom x v := by
  simp only [reAt, rhom, Pi.ringHom_apply]
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem scal_comm {R : Type} [CommRing R] (z : Rˣ) (A : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * A = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, mul_comm]

theorem norm_rat {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (q : ℚ) : ‖ι.symm (q : ℂ)‖ = ‖(q : ℚ_[p])‖ := by
  rw [map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]

theorem fermat {p : ℕ} [hp : Fact p.Prime] (r : ℚ) (hr : ‖(r : ℚ_[p])‖ = 1) :
    ‖((r : ℚ_[p]) ^ (p - 1) - 1)‖ ≤ (p : ℝ)⁻¹ := by
  set x : ℤ_[p] := ⟨r, hr.le⟩ with hxdef
  have hxn : ‖x‖ = 1 := hr
  have hx : IsUnit x := PadicInt.isUnit_iff.mpr hxn
  have h0 : PadicInt.toZMod x ≠ 0 := by
    intro h
    have : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
    rw [PadicInt.ker_toZMod] at this
    exact (IsLocalRing.mem_maximalIdeal x).mp this hx
  have h1 : x ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one h0, sub_self]
  have h2 : ‖x ^ (p - 1) - 1‖ < 1 := PadicInt.mem_nonunits.mp h1
  have h3 : ‖x ^ (p - 1) - 1‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using h2
  have h4 : ‖x ^ (p - 1) - 1‖ = ‖((r : ℚ_[p]) ^ (p - 1) - 1)‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [← h4]; simpa using h3

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "S" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem tp_mul {a b : F} (ha : TP a) (hb : TP b) : TP (a * b) := fun v => by
  rw [reAt_eq, map_mul, Pi.mul_apply, ← reAt_eq, ← reAt_eq]; exact mul_pos (ha v) (hb v)

theorem tp_one : TP (1 : F) := fun v => by rw [reAt_eq, map_one]; exact one_pos

theorem stab_one (g : GL (Fin 2) (Af F)) : Stab g (1 : GL (Fin 2) F) :=
  ⟨by simpa using (tp_one : TP (1 : F)), 1, 1, (KLev F 2 1).one_mem, by simp⟩

theorem stab_mul (g : GL (Fin 2) (Af F)) (γ γ' : GL (Fin 2) F) (h : Stab g γ) (h' : Stab g γ') : Stab g (γ * γ') := by
  obtain ⟨ht, z, u, hu, he⟩ := h
  obtain ⟨ht', z', u', hu', he'⟩ := h'
  refine ⟨?_, z' * z, u * u', (KLev F 2 1).mul_mem hu hu', ?_⟩
  · rw [Units.val_mul, Matrix.det_mul]; exact tp_mul ht ht'
  · rw [map_mul, mul_assoc, he', ← mul_assoc, ← mul_assoc, ← scal_comm, mul_assoc (S z'), he, map_mul]
    simp only [mul_assoc]

theorem stab_inv (g : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) (h : Stab g γ) : Stab g γ⁻¹ := by
  obtain ⟨ht, z, u, hu, he⟩ := h
  refine ⟨?_, z⁻¹, u⁻¹, (KLev F 2 1).inv_mem hu, ?_⟩
  · have h1 : γ.val.det * (γ⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    intro v
    have hv := congrArg (fun x => rhom x v) h1
    simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply] at hv
    have hp := ht v
    rw [reAt_eq] at hp ⊢
    exact (pos_iff_pos_of_mul_pos (by rw [hv]; exact one_pos)).mp hp
  · rw [map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← scal_comm, mul_assoc (S z⁻¹), he]
    simp only [map_inv]
    group

theorem absF_ne_zero (y : (Af F)ˣ) : absF y ≠ 0 := by
  classical
  unfold absF
  rw [finprod_def]
  split_ifs with h
  · rw [Finset.prod_ne_zero_iff]
    intro w _
    rw [norm_ne_zero_iff]
    exact ((Units.map (pLoc F w).toMonoidHom y).ne_zero)
  · exact one_ne_zero

end GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness

namespace GlobalTheory.HilbertThetaSeries

open GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness in

theorem orbit_seed_finite_congr : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → {f | ∃ γ, Stab (aff y 0) γ ∧ f = sl (p - 1) (toInf γ) θ}.Finite ∧ (∀ γ, Stab (aff y 0) γ → ∀ γ', InG p δ γ' → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1)) ∧ Stab (aff y 0) (1 : GL (Fin 2) F) ∧ ∀ γ γ' : GL (Fin 2) F, Stab (aff y 0) γ → Stab (aff y 0) γ' → Stab (aff y 0) (γ * γ') ∧ Stab (aff y 0) γ⁻¹ := by
  intro F _ _ _ p _ ι hp2 δ hδ θ hθ y hy
  have hk : Even (p - 1) := (Fact.out : p.Prime).even_sub_one hp2
  obtain ⟨-, hsl, hscal, htS, -⟩ := GlobalTheory.T.hilbert_slash_rational_matrix_properties F (p - 1) θ
  have hpos : ∀ γ : GL (Fin 2) F, TP γ.val.det → Pos (toInf γ) := fun γ h => (hsl γ).1.mpr h

  have hsc : ∀ (η : Fˣ) (γ : GL (Fin 2) F), TP γ.val.det →
      sl (p - 1) (toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ)) θ = sl (p - 1) (toInf γ) θ := by
    intro η γ h
    rw [map_mul, htS η]
    exact (hscal hk _ _ (hpos γ h)).2
  refine ⟨?_, ?_, stab_one _, fun γ γ' h h' => ⟨stab_mul _ γ γ' h h', stab_inv _ γ h⟩⟩
  ·
    obtain ⟨N, hN, hlev⟩ := hθ.lev
    obtain ⟨T, hT, hcov⟩ := GlobalTheory.T.stabilizer_eq_scalar_mul_congruence_mul_finset F (aff y 0) N hN
    refine ((Polynomial.nthRoots 8 (1 : ℂ)).toFinset.finite_toSet.image2
      (fun ζ τ => ζ • sl (p - 1) (toInf τ) θ) T.finite_toSet).subset ?_
    rintro f ⟨γ, hγ, rfl⟩
    obtain ⟨η, γ₀, τ, hτ, hγ₀, rfl⟩ := hcov γ hγ
    obtain ⟨ζ, hζ, hζe⟩ := hlev γ₀ hγ₀
    refine ⟨ζ, ?_, τ, hτ, ?_⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots (by norm_num)).mpr hζ
    have hdet0 : γ₀.val.det = 1 := hγ₀.1
    have hp0 : Pos (toInf γ₀) := hpos γ₀ (by rw [hdet0]; exact tp_one)
    have hpτ : Pos (toInf τ) := hpos τ (hT τ hτ).1
    have hd : TP (γ₀ * τ).val.det := by
      rw [Units.val_mul, Matrix.det_mul, hdet0, one_mul]; exact (hT τ hτ).1
    symm
    show sl (p - 1) (toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ)) θ = ζ • sl (p - 1) (toInf τ) θ
    rw [mul_assoc, hsc η _ hd, map_mul,
      (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F (p - 1) _ _ θ hp0 hpτ).2.2.2.1, (hsl γ₀).2, hdet0, hζe]
    simp only [map_one, Rat.cast_one, abs_one, Real.one_rpow, Complex.ofReal_one, one_smul]
    exact ((slash_add_smul_pow F (p - 1) 1 (toInf τ) θ θ ζ).2.2.2.2.1)
  ·
    intro γ hγ γ' hγ'
    obtain ⟨htp, z, u, hu, he⟩ := hγ
    obtain ⟨hmulG, -, hcmp⟩ := GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq F p δ hδ
    obtain ⟨η, r, hG, hr0, hr1, hnorm⟩ := hcmp y y z γ u hy hy htp hu he
    set γ₁ := Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ with hγ₁
    have hN : |((Algebra.norm ℚ γ₁.val.det : ℚ) : ℝ)| = (r : ℝ) ^ 2 :=
      mul_right_cancel₀ (absF_ne_zero y) hnorm
    have hpow : (|((Algebra.norm ℚ γ₁.val.det : ℚ) : ℝ)| ^ (((p - 1 : ℕ) : ℝ) / 2) : ℝ) = (r : ℝ) ^ (p - 1) := by
      rw [hN, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast]
      congr 1; ring
    have hp1 : Pos (toInf γ₁) := hpos γ₁ hG.2.2.2.2.2
    have hp' : Pos (toInf γ') := hpos γ' hγ'.2.2.2.2.2
    set c : ℂ := (((r ^ (p - 1) : ℚ) : ℝ) : ℂ) with hc
    have e1 : sl (p - 1) (toInf γ) θ = c • sl0 (p - 1) (toInf γ₁) θ := by
      rw [← hsc η γ htp, (hsl γ₁).2, hpow, hc]; push_cast; rfl
    have hS := hθ.one (γ₁ * γ') (hmulG γ₁ γ' hG hγ')
    set F0 := sl0 (p - 1) (toInf (γ₁ * γ')) θ with hF0
    have e2 : sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1 = c • (F0 - 1) + (fun _ => c - 1) := by
      rw [e1, (slash_add_smul_pow F (p - 1) 1 (toInf γ') (sl0 (p - 1) (toInf γ₁) θ) θ c).2.1,
        ← (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F (p - 1) _ _ θ hp1 hp').2.2.1, ← map_mul, hF0]
      funext w; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]; ring
    have hcn : ‖ι.symm c‖ = 1 := by
      rw [hc, Complex.ofReal_ratCast, norm_rat, Rat.cast_pow, norm_pow, hr1, one_pow]
    have hc1 : ‖ι.symm (c - 1)‖ ≤ (p : ℝ)⁻¹ := by
      have : c - 1 = (((r ^ (p - 1) - 1 : ℚ)) : ℂ) := by rw [hc]; push_cast; ring
      rw [this, norm_rat]; push_cast; exact fermat r hr1
    obtain ⟨-, -, hA, -, -, -⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c hS hS
    obtain ⟨-, -, -, -, -, hB⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ (c - 1) hS hS
    obtain ⟨hsum, -, -, -, -, -⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ 0 hA hB
    rw [e2]
    refine (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ 0 hsum hS).2.2.2.1 ?_
    rw [hcn, one_mul]
    exact max_le le_rfl hc1

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_seed_orbit_finite_and_congruence : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → {f | ∃ γ, Stab (aff y 0) γ ∧ f = sl (p - 1) (toInf γ) θ}.Finite ∧ (∀ γ, Stab (aff y 0) γ → ∀ γ', InG p δ γ' → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1)) ∧ Stab (aff y 0) (1 : GL (Fin 2) F) ∧ ∀ γ γ' : GL (Fin 2) F, Stab (aff y 0) γ → Stab (aff y 0) γ' → Stab (aff y 0) (γ * γ') ∧ Stab (aff y 0) γ⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr | exact GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr | (intros; apply GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr <;> assumption)
