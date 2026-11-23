import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqZeroOfAffine
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.PolarisedTorusAlgebraicOfParts

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj

namespace GlobalTheory.TorusTransfer

section Tangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem fderiv_eq_zero_at (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0)
    (z₀ : Fin g → ℂ) (U : A.left.Opens) (f : Γ(A.left, U)) (h : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U f) z₀ w = 0 := by
  let T : A ⟶ A := (toUnit A ≫ u.ex z₀) * 𝟙 A
  have hT : ∀ z, (u.ex z).left ≫ T.left = (u.ex (z₀ + z)).left := fun z => by
    rw [← Over.comp_left, u.ex_add]
    congr 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _),
      Category.id_comp]
  have h1 := hw (T.left ⁻¹ᵁ U) ((T.left.app U).hom f)
    (by rw [← top_le_preimage_comp, hT, add_zero]; exact h)
  simp only [valAt'_comp, hT] at h1
  rw [fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), add_zero] at h1
  exact h1

theorem eq_zero_of_fderiv_eq_zero (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) : w = 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, h0, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((u.ex 0).left (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 h0
  have hc : Continuous fun t : ℂ => t • w := by fun_prop
  have hO : IsOpen {t : ℂ | ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U} := (u.hol U 0).1.preimage hc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 (by simpa using h0')
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • w ∈ u.Λ := by
    intro t ht
    rw [← u.ker, ← TangentOrigin.ex_zero u]
    have hval : ∀ f : Γ(A.left, U), valAt' (u.ex (t • w)).left U f = valAt' (u.ex 0).left U f := by
      intro f
      have hd : ∀ s ∈ Metric.ball (0 : ℂ) r,
          HasDerivAt (fun s : ℂ => valAt' (u.ex (s • w)).left U f) 0 s := by
        intro s hs
        have h1 : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) (s • w) :=
          (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hball hs))
        have h2 : HasDerivAt (fun s : ℂ => s • w) w s := by
          simpa using (hasDerivAt_id s).smul_const w
        have h3 := h1.hasFDerivAt.comp_hasDerivAt s h2
        rw [fderiv_eq_zero_at u w hw _ U f (hball hs)] at h3
        exact h3
      have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
        (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) (fun s hs => (hd s hs).deriv)
        ht (Metric.mem_ball_self hr)
      simpa using this
    exact (existsUnique_point_of_ringHom A U hU (valAtHom _ U h0')
      (fun a => by
        rw [← valAt'_eq_valAtHom]
        exact valAt'_constFn _ _ (Over.w (u.ex 0)) U a h0')).unique
      ⟨hball ht, fun f => by rw [hval, valAt'_eq_valAtHom]⟩
      ⟨h0', fun f => valAt'_eq_valAtHom _ h0' f⟩
  have := u.discrete
  obtain ⟨V, hV, hV'⟩ := (isOpen_induced_iff (f := ((↑) : u.Λ → Fin g → ℂ))).1 (isOpen_discrete ({0} : Set u.Λ))
  have hV0 : (0 : Fin g → ℂ) ∈ V := by
    have : (0 : u.Λ) ∈ ((↑) : u.Λ → Fin g → ℂ) ⁻¹' V := by rw [hV']; rfl
    exact this
  have hev : ∀ᶠ t : ℂ in 𝓝[≠] 0, t • w ∈ V ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (Filter.inter_mem ((hV.preimage hc).mem_nhds (by simpa using hV0)) (Metric.ball_mem_nhds _ hr))
  obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (hev.and self_mem_nhdsWithin).exists
  have h4 : (⟨t • w, hmem t h2⟩ : u.Λ) ∈ ((↑) : u.Λ → Fin g → ℂ) ⁻¹' V := h1
  rw [hV'] at h4
  exact (smul_eq_zero.1 (congrArg Subtype.val h4)).resolve_left h3

theorem tangent_bijective (hs : SmoothOfRelativeDimension g A.hom) :
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :=
  TangentOrigin.tangent_bijection_of_values valAt'_rules A L g u
    (exists_coord_adapted (HolChart.exists_holomorphic_chart valAt'_rules existsUnique_point_of_ringHom
      exists_holomorphic_section_of_etale) A L g u hs (eq_zero_of_fderiv_eq_zero u))

end Tangent

section Reparam

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def reparam (ψ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (q : (Fin g → ℂ) → ℂ) (hq : Differentiable ℂ q)
    (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ) (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hΛ : ∀ z, ψ z ∈ u.Λ ↔ z ∈ Λ) : HolUnif A L g where
  ex z := u.ex (ψ z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto := u.ex_onto.comp ψ.surjective
  Λ := Λ
  ker z := (u.ker _).trans (hΛ z)
  discrete := hd
  full := hf
  hol U f := ⟨(u.hol U f).1.preimage ψ.toContinuousLinearEquiv.continuous,
    (u.hol U f).2.comp ψ.toContinuousLinearEquiv.differentiable.differentiableOn fun _ hz => hz⟩
  fr i z := u.fr i (ψ z) * cexp (q (ψ z))
  fr_hol i := ((u.fr_hol i).mul hq.cexp.differentiableOn).comp
    ψ.toContinuousLinearEquiv.differentiable.differentiableOn fun _ hz => hz
  fr_ne i z hz := mul_ne_zero (u.fr_ne i _ hz) (Complex.exp_ne_zero _)
  fr_compat i j z hz := by rw [u.fr_compat i j _ hz, _root_.mul_assoc]

theorem frame_law (th : L.Sec) (θ a : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (ha : Continuous a)
    (hth : u.IsFn th θ) (l : Fin g → ℂ) (hl : l ∈ u.Λ) (hlaw : ∀ z, θ (z + l) = a z * θ z) (i : L.ι) (z : Fin g → ℂ)
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) : u.fr i z = a z * u.fr i (z + l) := by
  have he : ∀ z, u.ex (z + l) = u.ex z := fun z => by rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  have hO := (u.hol (L.U i) 0).1
  have hc : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ContinuousAt (u.fr i) z := fun z hz =>
    (u.fr_hol i).continuousOn.continuousAt (hO.mem_nhds hz)
  have hd := ThetaSeparation.dense_ne_zero hθ (Function.ne_iff.1 h0)
  have h1 : ContinuousAt (fun z => a z * u.fr i (z + l)) z :=
    ha.continuousAt.mul (ContinuousAt.comp (f := fun z => z + l) (hc _ (by rw [he]; exact hz)) (by fun_prop))
  refine tendsto_nhds_unique_of_frequently_eq (hc z hz) h1 ?_
  refine ((mem_closure_iff_frequently.1 (hd z)).and_eventually (hO.mem_nhds hz)).mono fun y hy => ?_
  have h2 := hth i y hy.2
  have h3 := hth i (y + l) (by rw [he]; exact hy.2)
  rw [he, h2, hlaw] at h3
  apply mul_left_cancel₀ hy.1
  rw [h3]; ring

end Reparam

section NormalForm

open SiegelNormalForm

variable {g : ℕ}

theorem exists_siegel_coordinates (Λ : Submodule ℤ (Fin g → ℂ)) (hdisc : DiscreteTopology Λ)
    (hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℝ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      (Y.map (↑) : Matrix _ _ ℂ).IsSymm ∧ Y * τ.map Complex.im = 1 ∧
      ∀ z w, φ z ⬝ᵥ Hm *ᵥ star (φ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w := by
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
  have hYs' : (Y.map (↑) : Matrix _ _ ℂ).IsSymm := by
    ext i j
    simpa using congrFun (congrFun hYs i) j
  have hcomb : ∀ m n : Fin g → ℤ, φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) =
      ((∑ i, m i • e i + ∑ i, n i • f i : Λ) : Fin g → ℂ) := fun m n => by
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [h1 m, h1 n, hφ]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    simp
  refine ⟨φ, τ, Y, hτs, hτp, fun z => ⟨fun hz => ?_, ?_⟩, hYs', hYτ, hform⟩
  · refine ⟨fun i => bs.repr ⟨_, hz⟩ (Sum.inl i), fun i => bs.repr ⟨_, hz⟩ (Sum.inr i),
      φ.injective ?_⟩
    rw [hcomb]
    have := bs.sum_repr ⟨_, hz⟩
    rw [Fintype.sum_sum_type] at this
    rw [this]
  · rintro ⟨m, n, rfl⟩
    rw [hcomb]
    exact Subtype.coe_prop _

theorem mulVec_star_period {Y : Matrix (Fin g) (Fin g) ℝ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : Y * τ.map Complex.im = 1) (n m : Fin g → ℤ) :
    (Y.map (↑) : Matrix _ _ ℂ) *ᵥ star (τ *ᵥ ofIntVec n + ofIntVec m) =
      Y.map (↑) *ᵥ (τ *ᵥ ofIntVec n + ofIntVec m) - (2 * I) • ofIntVec n := by
  have h1 : star (τ *ᵥ ofIntVec n + ofIntVec m) = (τ *ᵥ ofIntVec n + ofIntVec m) -
      (2 * I) • (((τ.map Complex.im).map ((↑) : ℝ → ℂ)) *ᵥ ofIntVec n) := by
    ext i
    apply Complex.ext
    · simp [Matrix.mulVec, dotProduct, ofIntVec]
    · simp [Matrix.mulVec, dotProduct, ofIntVec]
      ring
  have h2 : (Y.map ((↑) : ℝ → ℂ)) * (τ.map Complex.im).map ((↑) : ℝ → ℂ) = 1 := by
    have := congrArg (fun M : Matrix (Fin g) (Fin g) ℝ => M.map Complex.ofRealHom) h
    simp only [Matrix.map_mul] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  rw [h1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

theorem autFactor_mul_exp {Y : Matrix (Fin g) (Fin g) ℝ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hY : (Y.map (↑) : Matrix _ _ ℂ).IsSymm) (h : Y * τ.map Complex.im = 1) (n m : Fin g → ℤ) (z l : Fin g → ℂ)
    (hl : l = τ *ᵥ ofIntVec n + ofIntVec m) :
    autFactor 0 0 τ n m z * cexp (-quad (Y.map (↑)) 0 z) =
      cexp (((Real.pi * ((n ⬝ᵥ m : ℤ) : ℝ) : ℝ) : ℂ) * I) *
        cexp (Real.pi * (z ⬝ᵥ Y.map (↑) *ᵥ star l) + Real.pi / 2 * (l ⬝ᵥ Y.map (↑) *ᵥ star l)) *
        cexp (-quad (Y.map (↑)) 0 (z + l)) := by
  have h1 := mulVec_star_period h n m
  rw [← hl] at h1
  have h2 := quad_add_sub hY 0 z l
  have h3 : l ⬝ᵥ ofIntVec n = ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) + ((n ⬝ᵥ m : ℤ) : ℂ) := by
    rw [hl, dotProduct_comm, dotProduct_add]
    simp [dotProduct, ofIntVec]
  have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  rw [autFactor, eC, eC, h0, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h1,
    eq_add_of_sub_eq h2]
  congr 1
  simp only [dotProduct_sub, dotProduct_smul, h3, smul_eq_mul, zero_dotProduct, quad, dotProduct_comm z (ofIntVec n)]
  push_cast
  ring

end NormalForm

theorem torus_algebraic_of_siegel :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (th : P.L.Sec), P.g = g ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsFn th (thetaChar τ a b) ∧ ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f) →
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (χ : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro H g Λ Hm Ef hd hf hH hpos hE hbij
  obtain ⟨φ, τ, Y, hs, hp, hΛ, hY, hYτ, hform⟩ := exists_siegel_coordinates Λ hd hf Hm Ef hH hpos hE hbij
  have h0 : ∀ i : Fin g, ofRealVec (0 : Fin g → ℝ) i = 0 ∨ ofRealVec (0 : Fin g → ℝ) i = 1 / 2 :=
    fun i => Or.inl (by simp [ofRealVec])
  obtain ⟨P, u, th, hg, hu, hth, -⟩ := H g τ _ _ hs hp h0 h0
  rw [thetaChar_ofRealVec_eq_theta] at hth
  have hψ : ∀ z, φ.symm z ∈ u.Λ ↔ z ∈ Λ := fun z => by
    rw [hu, ← hΛ, LinearEquiv.apply_symm_apply]
  have hmn : ∀ l : Λ, ∃ m n : Fin g → ℤ, φ.symm l = τ *ᵥ ofIntVec n + ofIntVec m := fun l => by
    obtain ⟨m, n, h⟩ := (hu _).1 ((hψ _).2 l.2)
    exact ⟨m, n, h.trans (add_comm _ _)⟩
  choose m n hmn using hmn
  have hform' : ∀ z w, z ⬝ᵥ Hm *ᵥ star w = φ.symm z ⬝ᵥ Y.map (↑) *ᵥ star (φ.symm w) := fun z w => by
    rw [← hform, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  refine ⟨P, reparam u φ.symm (fun z => -SiegelNormalForm.quad (Y.map (↑)) 0 z)
    (SiegelNormalForm.quad_differentiable _ _).neg Λ hd hf hψ,
    fun l => cexp (((Real.pi * ((n l ⬝ᵥ m l : ℤ) : ℝ) : ℝ) : ℂ) * I), hg, rfl,
    ⟨hH, hpos, fun l => Complex.norm_exp_ofReal_mul_I _, fun l i z hz => ?_⟩, tangent_bijective _ hsm⟩
  have h1 := frame_law u th _ (autFactor 0 0 τ (n l) (m l)) (differentiable_theta ⟨hs, hp⟩ 0 0)
    (theta_ne_zero ⟨hs, hp⟩ 0 0) (by unfold autFactor eC; simp only [dotProduct]; fun_prop) hth (φ.symm l)
    ((hψ _).2 l.2) (fun z => by rw [hmn l, ← add_assoc]; exact thetaQuasiPeriod_holds _ _ _ _ _ _ _ hs) i
    (φ.symm z) hz
  have h2 := autFactor_mul_exp hY hYτ (n l) (m l) (φ.symm z) (φ.symm l) (hmn l)
  change u.fr i (φ.symm z) * cexp (-SiegelNormalForm.quad (Y.map (↑)) 0 (φ.symm z)) =
    _ * (u.fr i (φ.symm (z + l)) * cexp (-SiegelNormalForm.quad (Y.map (↑)) 0 (φ.symm (z + l))))
  rw [hform', hform', map_add, h1]
  linear_combination u.fr i (φ.symm z + φ.symm l) * h2

end GlobalTheory.TorusTransfer
