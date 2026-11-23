import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenMain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqCexpQuadraticOfEquivalentFactors
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CharEqOfThetaCharEqMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.NormalUnique

section
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

theorem autFactor_eq_exp (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (n m : Fin g → ℤ) :
    ∃ c : ℂ, ∀ z, autFactor a b τ n m z =
      Complex.exp (-(2 * Real.pi * Complex.I) * (ofIntVec n ⬝ᵥ z) + c) := by
  refine ⟨2 * Real.pi * Complex.I * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec b ⬝ᵥ ofIntVec n
    - (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n)) / 2), fun z => ?_⟩
  rw [autFactor, eC, eC, ← Complex.exp_add]
  congr 1
  ring

theorem exists_symplectic {τ τ' : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (hτ' : τ' ∈ SiegelH (Fin g))
    (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hφ : ∀ m' n' : Fin g → ℤ, ∃ m n : Fin g → ℤ,
      φ ((fun i => (m' i : ℂ)) + τ' *ᵥ (fun i => (n' i : ℂ))) = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))
    {a b a' b' : Fin g → ℝ} {e : (Fin g → ℂ) → ℂ} (he : Differentiable ℂ e) (he0 : ∀ z, e z ≠ 0)
    (h : ∀ z, theta a' b' z τ' = e z * theta a b (φ z) τ) :
    ∃ δ ∈ Matrix.symplecticGroup (Fin g) ℤ, τ' = spAct δ τ ∧ ∀ z, φ z = (jAut δ τ)ᵀ *ᵥ z := by
  classical
  let m' : Fin g ⊕ Fin g → Fin g → ℤ := fun s i => (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) (Sum.inr i)
  let n' : Fin g ⊕ Fin g → Fin g → ℤ := fun s i => (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) (Sum.inl i)
  choose m n hmn using fun s => hφ (m' s) (n' s)
  let p : Fin g ⊕ Fin g → Fin g → ℂ := fun s => ofIntVec (m' s) + τ' *ᵥ ofIntVec (n' s)
  have hp : ∀ s, φ (p s) = ofIntVec (m s) + τ *ᵥ ofIntVec (n s) := hmn
  choose c' hc' using fun s => autFactor_eq_exp a' b' τ' (n' s) (m' s)
  choose c hc using fun s => autFactor_eq_exp a b τ (n s) (m s)
  have hφd : Differentiable ℂ φ := (LinearMap.toContinuousLinearMap φ).differentiable
  have key := alternating_eq_of_equivalent_factors p
    (fun s => (-(2 * Real.pi * Complex.I) : ℂ) • dotProductBilin ℂ ℂ (ofIntVec (n' s)))
    (fun s => (-(2 * Real.pi * Complex.I) : ℂ) • (dotProductBilin ℂ ℂ (ofIntVec (n s)) ∘ₗ φ)) c' c he.continuous he0
    (fun s v => by
      have hd : ∀ r : Fin g → ℂ, Differentiable ℂ fun z : Fin g → ℂ => r ⬝ᵥ z := fun r => by
        simp only [dotProduct]; fun_prop
      have := entire_eq_zero_or_eq_zero_of_mul_eq_zero
        (fun z => Complex.exp (-(2 * Real.pi * Complex.I) * (ofIntVec (n' s) ⬝ᵥ z) + c' s) * e z -
          Complex.exp (-(2 * Real.pi * Complex.I) * (ofIntVec (n s) ⬝ᵥ φ z) + c s) * e (z + p s))
        (fun z => theta a' b' z τ')
        (((((hd _).const_mul _).add_const _).cexp.mul he).sub
          (((((hd _).comp hφd).const_mul _).add_const _).cexp.mul (he.comp (differentiable_id.add_const _))))
        (differentiable_theta hτ' _ _) (fun z => by
          have h1 := h (z + p s)
          rw [map_add, hp] at h1
          simp only [p] at h1 ⊢
          rw [add_comm (ofIntVec (m' s)), add_comm (ofIntVec (m s)), ← add_assoc, ← add_assoc,
            thetaQuasiPeriod_holds _ _ _ _ _ _ _ hτ.1, thetaQuasiPeriod_holds _ _ _ _ _ _ _ hτ'.1, hc, hc'] at h1
          rw [add_comm (ofIntVec (m' s)), ← add_assoc]
          have h2 := h z
          linear_combination e z * h1 - Complex.exp (-(2 * Real.pi * Complex.I) * (ofIntVec (n s) ⬝ᵥ φ z) + c s) *
            e (z + τ' *ᵥ ofIntVec (n' s) + ofIntVec (m' s)) * h2)
      rcases this with h0 | h0
      · simpa [sub_eq_zero] using h0 v
      · exact absurd (funext h0) (theta_ne_zero hτ' _ _))
  have symm : ∀ {σ : Matrix (Fin g) (Fin g) ℂ}, σ.IsSymm → ∀ x y : Fin g → ℂ, x ⬝ᵥ σ *ᵥ y = y ⬝ᵥ σ *ᵥ x :=
    fun {σ} hσ x y => by rw [dotProduct_mulVec, ← mulVec_transpose, hσ.eq, dotProduct_comm]
  have cast : ∀ x y : Fin g → ℤ, ofIntVec x ⬝ᵥ ofIntVec y = ((x ⬝ᵥ y : ℤ) : ℂ) := fun x y => by
    simp [dotProduct, ofIntVec]
  have alt : ∀ s t, n' s ⬝ᵥ m' t - n' t ⬝ᵥ m' s = n s ⬝ᵥ m t - n t ⬝ᵥ m s := fun s t => by
    have h1 := key s t
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, hp, dotProductBilin_apply_apply, smul_eq_mul] at h1
    simp only [p, dotProduct_add, cast, symm hτ.1 (ofIntVec (n s)) (ofIntVec (n t)),
      symm hτ'.1 (ofIntVec (n' s)) (ofIntVec (n' t))] at h1
    have h2 : ((n' s ⬝ᵥ m' t - n' t ⬝ᵥ m' s : ℤ) : ℂ) = ((n s ⬝ᵥ m t - n t ⬝ᵥ m s : ℤ) : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      push_cast
      linear_combination -h1
    exact_mod_cast h2
  let δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := Matrix.of fun s => Sum.elim (n s) (m s)
  have hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ := by
    rw [SymplecticGroup.mem_iff]
    ext s t
    have h1 : (δ * J (Fin g) ℤ * δᵀ) s t = -(n s ⬝ᵥ m t - n t ⬝ᵥ m s) := by
      simp [δ, Matrix.mul_apply, J, Fintype.sum_sum_type, Matrix.one_apply, dotProduct, mul_comm]
      ring
    rw [h1, ← alt]
    rcases s with s | s <;> rcases t with t | t <;>
      simp [m', n', J, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]
  have per : ∀ s, φ (p s) = (jAut δ τ)ᵀ *ᵥ (ofIntVec (m' s) + spAct δ τ *ᵥ ofIntVec (n' s)) := fun s => by
    have h1 := SpMove.jAut_transpose_mulVec_period hδ hτ (Pi.single s 1)
    rw [hp]
    refine Eq.trans ?_ h1.symm
    simp only [Matrix.mulVec_single_one]
    rfl
  have hl : ∀ z, φ z = (jAut δ τ)ᵀ *ᵥ z := by
    have : φ = Matrix.mulVecLin (jAut δ τ)ᵀ := (Pi.basisFun ℂ (Fin g)).ext fun k => by
      have h1 := per (Sum.inr k)
      have e1 : ofIntVec (m' (Sum.inr k)) = Pi.single k 1 := by
        funext i; simp [m', ofIntVec, Pi.single_apply]
      have e2 : ofIntVec (n' (Sum.inr k)) = 0 := by
        funext i; simp [n', ofIntVec]
      simp only [p, e1, e2, mulVec_zero, add_zero] at h1
      simpa using h1
    intro z
    rw [this]
    rfl
  refine ⟨δ, hδ, ?_, hl⟩
  have hinj : Function.Injective (jAut δ τ)ᵀ.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact jAut_isUnit hδ hτ
  ext i k
  have h1 := per (Sum.inl k)
  rw [hl] at h1
  have h2 := hinj h1
  have e1 : ofIntVec (n' (Sum.inl k)) = Pi.single k 1 := by
    funext i; simp [n', ofIntVec, Pi.single_apply]
  simp only [p, e1, add_right_inj] at h2
  simpa using congrFun h2 i

theorem pow_eight_eq (hI : InversionStatement) {τ τ' : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (hτ' : τ' ∈ SiegelH (Fin g)) (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hφ : ∀ m' n' : Fin g → ℤ, ∃ m n : Fin g → ℤ,
      φ ((fun i => (m' i : ℂ)) + τ' *ᵥ (fun i => (n' i : ℂ))) = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))
    {a b a' b' : Fin g → ℂ} (hab : charHalf g a b) (hab' : charHalf g a' b') {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    {e : (Fin g → ℂ) → ℂ} (he : Differentiable ℂ e) (he0 : ∀ z, e z ≠ 0) (he1 : e 0 = 1)
    (h : ∀ z, c' * thetaChar τ' a' b' z = e z * (c * thetaChar τ a b (φ z))) :
    ∃ j : Matrix (Fin g) (Fin g) ℂ, (∀ z, φ z = jᵀ *ᵥ z) ∧ c ^ 8 = c' ^ 8 * j.det ^ 4 := by
  have half : ∀ {a : Fin g → ℂ}, (∀ i, a i = 0 ∨ a i = 1 / 2) → ∃ n : Fin g → ℤ, a = fun i => (n i : ℂ) / 2 :=
    fun ha => by
      obtain ⟨p, -, rfl⟩ := ThetaCompare.exists_eq_half ha
      exact ⟨p, funext fun i => by simp⟩
  have half' : ∀ {k : Fin g → ℤ}, (∀ i, k i = 0 ∨ k i = 1) → ∀ i, (k i : ℂ) / 2 = 0 ∨ (k i : ℂ) / 2 = 1 / 2 :=
    fun hk i => (hk i).imp (fun h => by simp [h]) fun h => by simp [h]
  obtain ⟨n, rfl⟩ := half hab.1
  obtain ⟨m, rfl⟩ := half hab.2
  obtain ⟨n', rfl⟩ := half hab'.1
  obtain ⟨m', rfl⟩ := half hab'.2
  obtain ⟨δ, hδ, rfl, hj⟩ := exists_symplectic hτ hτ' φ hφ (a := halfVec n) (b := halfVec m) (a' := halfVec n')
    (b' := halfVec m') (e := fun z => c / c' * e z) (he.const_mul _)
    (fun z => mul_ne_zero (div_ne_zero hc hc') (he0 z)) (fun z => by
      have := h z
      rw [SpMove.thetaChar_half, SpMove.thetaChar_half] at this
      field_simp
      linear_combination this)
  refine ⟨_, hj, ?_⟩
  obtain ⟨k, k', hk, hk', hlaw⟩ := (chiAt_iff_thetaLaw g δ).1 (chi_of hI spGen g δ hδ) n m
  obtain ⟨r, hr, H⟩ := SpMove.exists_theta_law hδ hlaw hτ
  have hu := jAut_isUnit hδ hτ
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact pow_ne_zero 4 hu.ne_zero (by rw [← hr]; simp)
  let ρ : (Fin g → ℂ) → ℂ := fun z =>
    c / (c' * r) * e z * Complex.exp (-(Real.pi * Complex.I * expArg δ τ ((jAut δ τ)ᵀ *ᵥ z)))
  have hρ : Differentiable ℂ ρ := by
    simp only [ρ, expArg, dotProduct, mulVec]
    fun_prop
  have hρ0 : ρ 0 = c / (c' * r) := by simp [ρ, he1, expArg]
  have hth : ∀ z, thetaChar (spAct δ τ) (fun i => (n' i : ℂ) / 2) (fun i => (m' i : ℂ) / 2) z =
      ρ z * thetaChar (spAct δ τ) (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) z := fun z => by
    have h1 := H ((jAut δ τ)ᵀ *ᵥ z)
    have h2 : zAct δ τ ((jAut δ τ)ᵀ *ᵥ z) = z := by
      rw [zAct, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one,
        Matrix.one_mulVec]
    have h3 := h z
    rw [h2] at h1
    rw [hj, SpMove.thetaChar_half τ] at h3
    rw [SpMove.thetaChar_half _ k, h1]
    simp only [ρ, Complex.exp_neg]
    have := Complex.exp_ne_zero (Real.pi * Complex.I * expArg δ τ ((jAut δ τ)ᵀ *ᵥ z))
    field_simp
    linear_combination h3
  obtain ⟨e1, e2⟩ := ThetaCompare.char_eq_of_thetaChar_eq_mul hτ' hab'.1 hab'.2 (half' hk) (half' hk') hρ
    (by rw [hρ0]; exact div_ne_zero hc (mul_ne_zero hc' hr0)) hth
  rw [e1, e2] at hth
  simp only [SpMove.thetaChar_half] at hth
  rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero (fun z => ρ z - 1) _ (hρ.sub_const 1)
    (differentiable_theta hτ' (halfVec n') (halfVec m')) (fun z => by linear_combination -hth z) with h0 | h0
  · have h1 := h0 0
    rw [hρ0, sub_eq_zero, div_eq_one_iff_eq (mul_ne_zero hc' hr0)] at h1
    rw [h1, mul_pow, hr]
  · exact absurd (funext h0) (theta_ne_zero hτ' _ _)

end

theorem exists_frame_ratio {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {g : ℕ} (u u' : HolUnif A L g)
    (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hφ : ∀ z, u.ex (φ z) = u'.ex z) :
    ∃ e : (Fin g → ℂ) → ℂ, Differentiable ℂ e ∧ (∀ z, e z ≠ 0) ∧
      (∀ rig, u.IsRig rig → u'.IsRig rig → e 0 = 1) ∧
      ∀ s θ θ', u.IsFn s θ → u'.IsFn s θ' → ∀ z, θ' z = e z * θ (φ z) := by
  have cover : ∀ z, ∃ j, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U j := fun z => by
    obtain ⟨j, hj⟩ := exists_chart hL ((u'.ex z).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using cover
  have tr : ∀ j z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U j → ⊤ ≤ (u.ex (φ z)).left ⁻¹ᵁ L.U j :=
    fun j z h => by rw [hφ]; exact h
  have key : ∀ j z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U j →
      u.fr j (φ z) = u.fr (J z) (φ z) / u'.fr (J z) z * u'.fr j z := fun j z h => by
    have h1 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U j ⊓ L.U (J z)) := (top_le_preimage_inf _ _ _).2 ⟨h, hJ z⟩
    have e1 := u'.fr_compat j (J z) z h1
    have e2 := u.fr_compat j (J z) (φ z) (by rw [hφ]; exact h1)
    rw [hφ] at e2
    have := u'.fr_ne _ _ (hJ z)
    rw [e1, e2]
    field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ j z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U j →
      u.fr j (φ z) = ρ z * u'.fr j z := ⟨_, key⟩
  refine ⟨ρ, fun z => ?_, fun z h => u.fr_ne _ _ (tr _ _ (hJ z)) (by rw [hρ _ _ (hJ z), h, zero_mul]),
    fun rig h h' => ?_, fun s θ θ' h h' z => ?_⟩
  · have hz := (u'.hol (L.U (J z)) 0).1.mem_nhds (hJ z)
    have dl : Differentiable ℂ φ := (LinearMap.toContinuousLinearMap φ).differentiable
    have d2 : DifferentiableOn ℂ (fun z' => u.fr (J z) (φ z')) {z' | ⊤ ≤ (u'.ex z').left ⁻¹ᵁ L.U (J z)} :=
      (u.fr_hol (J z)).comp dl.differentiableOn (fun z' h => tr _ _ h)
    have d3 := (d2.mul ((u'.fr_hol (J z)).inv (fun z' h => u'.fr_ne _ _ h))).congr (f₁ := ρ) (fun z' h => by
      have := u'.fr_ne _ _ h
      show ρ z' = u.fr (J z) (φ z') * (u'.fr (J z) z')⁻¹
      rw [hρ _ _ h]; field_simp)
    exact d3.differentiableAt hz
  · have h0 : (u'.ex 0).left = eSec A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[A]).left = η[A].left
      rw [toUnit_unit, Category.id_comp]
    have hj : ⊤ ≤ (L.pull (eSec A)).U (fun _ => J 0) := fun y hy => by
      rw [mem_pull, ← h0]
      exact hJ 0 hy
    have e := hρ _ _ (hJ 0)
    rw [map_zero, (h _ hj).trans (h' _ hj).symm] at e
    exact (mul_eq_right₀ (u'.fr_ne _ _ (hJ 0))).1 e.symm
  · have e1 := h (J z) (φ z) (tr _ _ (hJ z))
    rw [hφ, h' (J z) z (hJ z), hρ _ _ (hJ z)] at e1
    apply mul_right_cancel₀ (u'.fr_ne _ _ (hJ z))
    rw [e1]
    ring

theorem thetaFrame_value_unique : ThetaUnifAV → Key.Chi.InversionStatement → ∀ (x : KeyIn ℂ) (t t' : ℂ), (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t = t' := by
  rintro hU hI x t t' ⟨τ, M, a, b, c, hab, hc, ⟨u, hs, hp, hΛ, hrig, hfn, hv⟩, rfl⟩
    ⟨τ', M', a', b', c', hab', hc', ⟨u', hs', hp', hΛ', hrig', hfn', hv'⟩, rfl⟩
  obtain ⟨h1, h2, -⟩ := AnyUnif.tangent_and_unimodular hU x.P u
  obtain ⟨φ, hφ, hl, hd, -⟩ := HomLinear.exists_linear_of_isMonHom x.P.A x.P.A x.P.isAb x.P.isAb x.P.L x.P.L
    x.P.g x.P.g u' u h1 h2 (𝟙 x.P.A) inferInstance
  simp only [Category.comp_id] at hφ hd
  obtain ⟨e, he, he0, he1, hθ⟩ := exists_frame_ratio x.P.isLB u u' φ hφ
  obtain ⟨j, hj, hcc⟩ := pow_eight_eq hI ⟨hs, hp⟩ ⟨hs', hp'⟩ φ
    (fun m n => (hΛ _).1 (hl _ ((hΛ' _).2 ⟨m, n, rfl⟩))) hab hab' hc hc' he he0 (he1 _ hrig hrig')
    (hθ _ _ _ hfn hfn')
  have hM : M = M' * j := by
    ext i k
    have e1 := (h1 _ (x.basis.1 i)).unique (hv i) (hd _ _ (x.basis.1 i) (hv' i)).2
    rw [map_smul, hj, Matrix.mulVec_transpose] at e1
    exact congrFun (smul_right_injective _ (inv_ne_zero Complex.two_pi_I_ne_zero) e1) k
  have hj0 : j.det ≠ 0 := fun h => pow_ne_zero 8 hc (by rw [hcc, h]; simp)
  rw [hM, Matrix.det_mul, hcc]
  field_simp

end GlobalTheory.NormalUnique
