import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.KeyNormalForm

section Normal

open Complex Matrix GlobalTheory.SiegelNormalForm

theorem exists_coordinates {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      ∀ z w, hermForm Hm (φ z) (φ w) = hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z w := by
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  have halt : Ef.IsAlt := fun l => by
    have h1 := congrArg Complex.im (form_conj hH (l : Fin g → ℂ) l)
    have h2 := hE l l
    simp only [Complex.star_def, Complex.conj_im] at h1
    have : (Ef l l : ℝ) = 0 := by linarith
    exact_mod_cast this
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm hbij) hrank
  set e : Fin g → Λ := fun i => bs (Sum.inl i) with he
  set f : Fin g → Λ := fun i => bs (Sum.inr i) with hf
  have hee : ∀ i j, ((e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (e j : Fin g → ℂ)).im = 0 := fun i j => by
    have := hbs.left_left i j
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    rw [← hE, this]; simp
  have hff : ∀ i j, ((f i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (f j : Fin g → ℂ)).im = 0 := fun i j => by
    have := hbs.right_right i j
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    rw [← hE, this]; simp
  have hef : ∀ i j, ((e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (f j : Fin g → ℂ)).im =
      if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [← hE, this]; split_ifs <;> simp
  let P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => (e i : Fin g → ℂ) k
  have hP : ∀ i, P *ᵥ Pi.single i 1 = e i := fun i => by
    ext k; simp [P]
  let Y : Matrix (Fin g) (Fin g) ℝ := (Pᵀ * Hm * P.map star).map Complex.re
  have hYe : ∀ i j, (Pᵀ * Hm * P.map star) i j =
      (e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (e j : Fin g → ℂ) := fun i j => by
    rw [← form_single (Pᵀ * Hm * P.map star), ← form_pull, hP, hP]
  have hY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · rw [hYe, hee]; simp
  have hPu : IsUnit P := isUnit_of_lagrangian P Hm (fun j => f j) hpos Y hY
    (fun i j => by rw [hP, hef])
  have hPi : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hPu
  have hPs : Function.Surjective P.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hPu
  let φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective P.mulVecLin ⟨hPi, hPs⟩
  have hφ : ∀ z, φ z = P *ᵥ z := fun z => rfl
  let τ : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => φ.symm (f j) k
  have hτ : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = f j := fun j => by
    rw [← hφ, ← LinearEquiv.eq_symm_apply]
    ext k; simp [τ]
  have hform : ∀ z w, (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w :=
    fun z w => by rw [form_pull, hY]
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (form_conj hH (e i : Fin g → ℂ) (e j))
    simp only [Complex.star_def, Complex.conj_re] at this
    simp only [Y, Matrix.transpose_apply, Matrix.map_apply, hYe, this]
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : P *ᵥ (fun i => (a i : ℂ)) ≠ 0 := by
      intro h0
      have := hPi (h0.trans (Matrix.mulVec_zero P).symm)
      exact ha (funext fun i => by simpa using congrFun this i)
    have := hpos _ hne
    rw [hform] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨hτs, hτp, hYτ⟩ := siegel_of_relations Y hYp τ
    (fun i j => by rw [← hform, hP, hτ, hef]) (fun i j => by rw [← hform, hτ, hτ, hff])
  have hcomb : ∀ m n : Fin g → ℤ, φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) =
      ((∑ i, m i • e i + ∑ i, n i • f i : Λ) : Fin g → ℂ) := fun m n => by
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [h1 m, h1 n, hφ]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    simp
  refine ⟨φ, τ, hτs, hτp, fun z => ⟨fun hz => ?_, ?_⟩, fun z w => ?_⟩
  · refine ⟨fun i => bs.repr ⟨_, hz⟩ (Sum.inl i), fun i => bs.repr ⟨_, hz⟩ (Sum.inr i),
      φ.injective ?_⟩
    rw [hcomb]
    have := bs.sum_repr ⟨_, hz⟩
    rw [Fintype.sum_sum_type] at this
    rw [this]
  · rintro ⟨m, n, rfl⟩
    rw [hcomb]
    exact Subtype.coe_prop _
  · rw [Matrix.inv_eq_left_inv hYτ]
    exact hform z w

end Normal

section Change

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  (φ : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (Q : (Fin g → ℂ) → ℂ) (hQ : Differentiable ℂ Q)

def change : HolUnif A L g where
  ex z := u.ex (φ z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto := u.ex_onto.comp φ.surjective
  Λ := u.Λ.comap (φ.toLinearEquiv.toLinearMap.restrictScalars ℤ)
  ker z := u.ker _
  discrete := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (β := u.Λ)
      (f := fun l => ⟨φ l, l.2⟩) ((φ.continuous.comp continuous_subtype_val).subtype_mk _) ?_
    intro a b h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  full := by
    have h : ((u.Λ.comap (φ.toLinearEquiv.toLinearMap.restrictScalars ℤ) : Submodule ℤ _) : Set (Fin g → ℂ)) =
        (φ.symm.toLinearEquiv.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨fun hz => ⟨φ z, hz, φ.symm_apply_apply z⟩, by
        rintro ⟨w, hw, rfl⟩
        change φ (φ.symm w) ∈ u.Λ
        rwa [φ.apply_symm_apply]⟩
    rw [h, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.symm.surjective
  hol U f := ⟨(u.hol U f).1.preimage φ.continuous,
    (u.hol U f).2.comp φ.differentiable.differentiableOn fun _ hz => hz⟩
  fr i z := Complex.exp (Q z) * u.fr i (φ z)
  fr_hol i := hQ.cexp.differentiableOn.mul
    ((u.fr_hol i).comp φ.differentiable.differentiableOn fun _ hz => hz)
  fr_ne i z hz := mul_ne_zero (Complex.exp_ne_zero _) (u.fr_ne i _ hz)
  fr_compat i j z hz := by rw [u.fr_compat i j _ hz]; ring

theorem mem_change (z : Fin g → ℂ) : z ∈ (change u φ Q hQ).Λ ↔ φ z ∈ u.Λ := Iff.rfl

theorem isRig_change (h0 : Q 0 = 0) {rig : LB.Gen (L.pull (eSec A))} (h : u.IsRig rig) :
    (change u φ Q hQ).IsRig rig := fun j hj => by
  rw [← h j hj]
  simp [change, h0]

theorem isFn_change {s : L.Sec} {θ θ' : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    (hθ : ∀ z, θ (φ z) = θ' z * Complex.exp (Q z)) : (change u φ Q hQ).IsFn s θ' := fun i z hz => by
  refine (h i (φ z) hz).trans ?_
  rw [hθ, _root_.mul_assoc]
  rfl

theorem isDiff_change {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (h : u.IsDiff (φ w) v) :
    (change u φ Q hQ).IsDiff w v := fun U hU f => by
  refine (h U hU f).trans ?_
  have := φ.comp_right_fderiv (f := fun z => valAt' (u.ex z).left U f) (x := 0)
  rw [map_zero] at this
  exact (congrArg (fun k => k w) this).symm

end Change

section Constants

open Complex Matrix

variable {g : ℕ}

theorem weight_eq {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (p q : Fin g → ℝ) (c t : ℂ)
    {z : Fin g → ℂ} (hz : z = (fun i => (p i : ℂ)) + τ.mulVec (fun i => (q i : ℂ))) :
    ‖c * (cexp (Real.pi / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z)) * t)‖ ^ 2 *
        Real.exp (-Real.pi * (hermForm (CanTh.imInv τ) z z).re) =
      ‖c‖ ^ 2 * (‖t‖ ^ 2 * Real.exp (-2 * Real.pi * (q ⬝ᵥ (τ.map Complex.im).mulVec q))) := by
  have h1 := CanTh.dot_imInv_eq_hermForm_add hp q p z
  rw [← hz] at h1
  have h2 : (z ⬝ᵥ fun i => (q i : ℂ)).im = q ⬝ᵥ (τ.map Complex.im).mulVec q := by
    rw [hz]
    simp [dotProduct, mulVec, mul_comm]
  have h3 : ((Real.pi : ℂ) / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z)).re =
      Real.pi / 2 * ((hermForm (CanTh.imInv τ) z z).re - 2 * (q ⬝ᵥ (τ.map Complex.im).mulVec q)) := by
    rw [h1, ← h2, show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    simp [sub_eq_add_neg]
  rw [norm_mul, norm_mul, Complex.norm_exp, h3, mul_pow, mul_pow, ← Real.exp_nat_mul, _root_.mul_assoc,
    mul_right_comm (Real.exp _), ← Real.exp_add, mul_comm (Real.exp _)]
  congr 3
  push_cast
  ring

theorem weight_periodic {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) {k t : ℂ} (hk : ‖k‖ = 1)
    (z l : Fin g → ℂ) :
    ‖(k * cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ 1 * t‖ ^ 2 *
        Real.exp (-Real.pi * (hermForm Hm (z + l) (z + l)).re) =
      ‖t‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := by
  have h3 : ((Real.pi : ℂ) * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l).re =
      Real.pi * (hermForm Hm z l).re + Real.pi / 2 * (hermForm Hm l l).re := by
    rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.add_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  rw [pow_one, norm_mul, norm_mul, hk, _root_.one_mul, Complex.norm_exp, h3,
    AppellHumbertTrivial.re_hermForm_add_self hH, mul_pow, ← Real.exp_nat_mul,
    mul_right_comm (Real.exp _), ← Real.exp_add, mul_comm (Real.exp _)]
  congr 2
  push_cast
  ring

theorem det_rows (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : ℂ) (M W : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i, W i = φ (s • M i)) : W.det = s ^ g * M.det * LinearMap.det φ := by
  have : W = (s • M) * (LinearMap.toMatrix' φ)ᵀ := by
    ext i j
    rw [h, ← LinearMap.toMatrix'_mulVec]
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_smul, Matrix.det_transpose, LinearMap.det_toMatrix', Fintype.card_fin]

theorem constant_eq (g : ℕ) {m c d y : ℝ} (hm : 0 < m) (hc : 0 < c) (hd : 0 < d) (hy : 0 < y) :
    m ^ 4 / c ^ 8 * (c ^ 2 * (Real.sqrt (2 ^ g * y))⁻¹) ^ 4 *
      (d ^ 2 * y / (Real.pi ^ g * (((2 * Real.pi)⁻¹) ^ g * m * d) ^ 2)) ^ 2 = (2 * Real.pi) ^ (2 * g) := by
  have h1 : Real.sqrt (2 ^ g * y) ^ 4 = (2 ^ g * y) ^ 2 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  have h2 := Real.pi_pos
  rw [mul_pow (c ^ 2), inv_pow, h1, inv_pow, mul_comm 2 g, pow_mul, mul_pow 2 Real.pi g]
  generalize_proofs
  have h3 : (0 : ℝ) < 2 ^ g := by positivity
  have h4 : (0 : ℝ) < Real.pi ^ g := by positivity
  generalize (2 : ℝ) ^ g = s at *
  generalize Real.pi ^ g = t at *
  field_simp

end Constants

theorem det_ne_zero_of_basis
    (hlin : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w)
    (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) : W.det ≠ 0 := by
  have hs : Function.Surjective W.vecMul := fun w => by
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
    obtain ⟨c, hc, -⟩ := x.basis.2 v hv
    refine ⟨c, (h₁ v hv).unique ?_ hd⟩
    have := hlin x.P.A x.P.isAb x.P.L _ _ u x.v W c v x.basis.1 hW hc
    rwa [← Matrix.vecMul_eq_sum] at this
  exact ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 hs)).ne_zero

theorem normal_form_of_parts
    (hcmp : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∀ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    (∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v))
    (hlin : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w)
    (hsec : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0)
    (hline : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (α : (Fin g → ℤ) → (Fin g → ℤ) → ℂ) (f : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → (∀ m n, α m n ^ 2 = 1) → Differentiable ℂ f → f ≠ 0 →
    (∀ (m n : Fin g → ℤ) (l z : Fin g → ℂ), l = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      f (z + l) = α m n * Complex.exp (Real.pi * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z l +
        Real.pi / 2 * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) l l) * f z) →
    ∃ (a b : Fin g → ℝ) (c : ℂ), (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ c ≠ 0 ∧
      ∀ z, f z = c * (Complex.exp (Real.pi / 2 * (z ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)).mulVec z)) *
        thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) z))
    (hvol : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    (volume Fd).toReal = ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det)
    (havg : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    ∀ F : (Fin g → ℂ) → ℝ, (∀ (l : Λ) z, F (z + l) = F z) →
    ∫ z in Fd, F z = (volume Fd).toReal * ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
      F (φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ))))) :
    ThetaUnifAV → ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ∃ (u' : HolUnif x.P.A x.P.L x.P.g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
        τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
        (∀ z, z ∈ u'.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
        u'.IsRig x.rig ∧ c ≠ 0 ∧ u'.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ M.det ≠ 0 ∧
        (∀ i, u'.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v i)) ∧
        ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g) := by
  intro hT x u Hm W χ θ Fd nth nη hAH hrig hfn hW hFd hnth hnη
  obtain ⟨⟨Ef, hE, hbij⟩, h₁, h₂⟩ := hcmp hT x.P x.rig x.rig_gen u Hm χ hAH
  have hWdet := det_ne_zero_of_basis hlin x u W hW h₁ h₂
  obtain ⟨⟨hθd, hθl⟩, hθ0⟩ := hsec x u Hm χ θ hAH hfn
  have := u.discrete
  obtain ⟨φ, τ, hs, hp, hΛ, hH⟩ := exists_coordinates u.Λ u.full Hm Ef hAH.1 hAH.2.1 hE hbij
  let ψ := φ.toContinuousLinearEquiv
  obtain ⟨a, b, c, ha, hb, hc, hθ⟩ := hline x.P.g τ
    (fun m n => χ ⟨φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))), (hΛ _).2 ⟨m, n, rfl⟩⟩)
    (fun z => θ (φ z)) hs hp (fun m n => semicharacter_sq_eq_one_of_symmetric x.P u Hm χ hAH _)
    (hθd.comp ψ.differentiable)
    (fun h => hθ0 (funext fun z => by simpa using congrFun h (φ.symm z)))
    (fun m n l z hl => by
      subst hl
      have := hθl ⟨_, (hΛ _).2 ⟨m, n, rfl⟩⟩ (φ z)
      rw [pow_one, hH, hH, ← map_add] at this
      exact this)
  have hQ : Differentiable ℂ fun z : Fin x.P.g → ℂ =>
      (Real.pi : ℂ) / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • φ.symm (W i)
  have hM : ∀ i, W i = φ ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M i) := fun i => by
    change _ = φ ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • φ.symm (W i))
    rw [inv_smul_smul₀ hπ, φ.apply_symm_apply]
  have hdet := det_rows φ.toLinearMap _ M W hM
  have hMdet : M.det ≠ 0 := fun h => hWdet (by rw [hdet, h]; simp)
  have hφdet : LinearMap.det φ.toLinearMap ≠ 0 := fun h => hWdet (by rw [hdet, h]; simp)
  refine ⟨change u ψ _ hQ, τ, M, fun i => a i, fun i => b i, c, hs, hp,
    fun i => (ha i).imp (fun h => by simp [h]) (fun h => by simp [h]),
    fun i => (hb i).imp (fun h => by simp [h]) (fun h => by simp [h]), hΛ,
    isRig_change u ψ _ hQ (by simp) hrig, hc,
    isFn_change u ψ _ hQ hfn fun z => (hθ z).trans (by rw [_root_.mul_assoc, mul_comm (Complex.exp _)]; rfl),
    hMdet, fun i => isDiff_change u ψ _ hQ (by have := hW i; rwa [hM] at this), ?_⟩
  have hv := hvol _ u.Λ φ τ hp hΛ Fd hFd
  have hv0 : (volume Fd).toReal ≠ 0 := by
    rw [hv]
    exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hφdet)) hp.det_pos.ne'
  have hI := havg _ u.Λ φ τ hp hΛ Fd hFd (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re))
    (fun l z => by rw [hθl]; exact weight_periodic hAH.1 (hAH.2.2.1 l) z l)
  have hn : nth = ‖c‖ ^ 2 * (Real.sqrt (2 ^ x.P.g * (τ.map Complex.im).det))⁻¹ := by
    rw [hnth, div_eq_iff hv0, mul_comm _ (volume Fd).toReal]
    refine hI.trans ?_
    rw [← ThetaNorm.integral_norm_sq_thetaChar _ τ a b hs hp, ← integral_const_mul (‖c‖ ^ 2)]
    congr 2
    funext p
    rw [hH, hθ]
    exact weight_eq hp _ _ c _ rfl
  have hWn : ‖W.det‖ = ((2 * Real.pi)⁻¹) ^ x.P.g * ‖M.det‖ * ‖LinearMap.det φ.toLinearMap‖ := by
    rw [hdet, norm_mul, norm_mul, norm_pow, norm_inv]
    rw [show ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi by simp [abs_of_pos Real.pi_pos]]
  rw [hn, hnη, hv, hWn, norm_div, norm_pow, norm_pow]
  exact constant_eq _ (norm_pos_iff.2 hMdet) (norm_pos_iff.2 hc) (norm_pos_iff.2 hφdet) hp.det_pos

end GlobalTheory.KeyNormalForm
