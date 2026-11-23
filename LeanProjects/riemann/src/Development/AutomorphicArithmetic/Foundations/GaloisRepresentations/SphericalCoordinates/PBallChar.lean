import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem ringHom_eq_of_eq_on_ringOfIntegers {F : Type} [Field F] [NumberField F] (τ₁ τ₂ : F →+* ℂ)
    (h : ∀ c : 𝓞 F, τ₁ c = τ₂ c) : τ₁ = τ₂ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun c => h c)

private theorem det_one_sub_smul_eq_prod_of_diagonal {d : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (T : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) (e : (Fin d → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (w : κ → ℂ)
    (h : ∀ b j, e (T b) j = w j * e b j) (y : ℂ) :
    LinearMap.det (1 - y • T) = ∏ j, (1 - y * w j) := by
  rw [← LinearMap.det_conj (1 - y • T) e]
  have hc : (e : (Fin d → ℂ) →ₗ[ℂ] (κ → ℂ)) ∘ₗ (1 - y • T) ∘ₗ (e.symm : (κ → ℂ) →ₗ[ℂ] (Fin d → ℂ)) =
      Matrix.toLin' (Matrix.diagonal fun j => 1 - y * w j) := by
    apply LinearMap.ext
    intro v
    funext j
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, h]
    ring
  rw [hc, LinearMap.det_toLin', Matrix.det_diagonal]

private theorem transpose_rho_mul_herm_eq_herm_mul_bar {O : Type} [Ring O] {bar : O → O} {g : ℕ} (D : PLat O bar)
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ Fin g → ℂ) (M₀ : Matrix (Fin g) (Fin g) ℂ)
    (hP : PELU.IsPeriod D ρ P₀) (hM : IsHermOf D P₀ M₀) (x : O) :
    (ρ x)ᵀ * M₀ = M₀ * (ρ (bar x)).map star := by
  have hL : ∀ (R : Matrix (Fin g) (Fin g) ℂ) (u w : Fin g → ℂ),
      hermForm M₀ (R *ᵥ u) w = u ⬝ᵥ (Rᵀ * M₀) *ᵥ star w := by
    intro R u w
    unfold hermForm
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Rᵀ, Matrix.vecMul_transpose]
  have hR : ∀ (R : Matrix (Fin g) (Fin g) ℂ) (u w : Fin g → ℂ),
      hermForm M₀ u (R *ᵥ w) = u ⬝ᵥ (M₀ * R.map star) *ᵥ star w := by
    intro R u w
    unfold hermForm
    rw [← Matrix.mulVec_mulVec]
    congr 2
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, Pi.star_apply]
  set A := (ρ x)ᵀ * M₀ - M₀ * (ρ (bar x)).map star with hA
  have key : ∀ p q : D.La, (P₀ p ⬝ᵥ A *ᵥ star (P₀ q)).im = 0 := by
    intro p q
    have h1 := hM.2.2 (x • p) q
    have h2 := hM.2.2 p (bar x • q)
    rw [D.adj x p q] at h1
    rw [hP.1 x p, hL] at h1
    rw [hP.1 (bar x) q, hR] at h2
    rw [hA, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h1, h2, sub_self]
  have hspan := hP.2.2.2.1
  have step1 : ∀ p : D.La, ∀ v : Fin g → ℂ, (P₀ p ⬝ᵥ A *ᵥ star v).im = 0 := by
    intro p v
    have hv : v ∈ Submodule.span ℝ (Set.range P₀) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      exact key p q
    | zero => simp
    | add y z _ _ hy hz =>
      rw [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, hy, hz, add_zero]
    | smul r y _ hy =>
      rw [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, hy, smul_zero]
  have step2 : ∀ u v : Fin g → ℂ, (u ⬝ᵥ A *ᵥ star v).im = 0 := by
    intro u v
    have hu : u ∈ Submodule.span ℝ (Set.range P₀) := by rw [hspan]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      exact step1 p v
    | zero => simp
    | add y z _ _ hy hz =>
      rw [add_dotProduct, Complex.add_im, hy, hz, add_zero]
    | smul r y _ hy =>
      rw [smul_dotProduct, Complex.smul_im, hy, smul_zero]
  have hA0 : A = 0 := by
    ext k l
    have e1 := step2 (Pi.single k 1) (Pi.single l 1)
    have e2 := step2 (Pi.single k Complex.I) (Pi.single l 1)
    simp [Matrix.mulVec_single] at e1 e2
    exact Complex.ext e2 e1
  rw [hA, sub_eq_zero] at hA0
  exact hA0

theorem UpperTheory.Gal.W2.ballChar_of :
    UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.TspDiag → UpperTheory.Gal.W2.BallChar := by
  intro hTC hTD
  unfold UpperTheory.Gal.W2.BallChar
  intro F _ _ O _ bar g ρ a n t₀ ε hS D P₀ M₀ hP hM H hH Sb ty ev hD mu hmu d co hco T hT
  classical
  have hD' : Sb.det ≠ 0 ∧ (∀ c : 𝓞 F, ρ (a c) * Sb = Sb * Matrix.diagonal fun i => ty i c) ∧
      H * Sb = Sb * Matrix.diagonal ev := hD
  obtain ⟨hSb, hρ, hHS⟩ := hD'
  have hcnt := hTC F O bar g ρ a n t₀ ε hS H Sb ty ev hD
  have hcard : ∀ τ : F →+* ℂ, (Finset.univ.filter fun i => ty i = τ).card = typeMult n t₀ ε τ := by
    intro τ
    have := (hcnt τ).1
    rw [evAt, Multiset.card_map] at this
    exact this
  have ht0 : typeMult n t₀ ε t₀ = 1 := by simp [typeMult]
  obtain ⟨i₀, hi₀s⟩ := Finset.card_eq_one.1 ((hcard t₀).trans ht0)
  have hi₀ : ∀ i, ty i = t₀ ↔ i = i₀ := by
    intro i
    have := congrArg (i ∈ ·) hi₀s
    simpa using this
  have hmu0 : ev i₀ = mu := by
    have h1 : evAt ty ev t₀ = {ev i₀} := by
      simp only [evAt]
      rw [show ({i | ty i = t₀} : Finset (Fin g)) = {i₀} from by simpa using hi₀s]
      simp
    rw [h1] at hmu
    exact Multiset.singleton_inj.1 hmu
  have hcc : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  have hpair : ∀ i j, ty j = ComplexEmbedding.conjugate (ty i) → i = i₀ ∨ j = i₀ := by
    intro i j hij
    by_cases h1 : ty i = t₀
    · exact Or.inl ((hi₀ i).1 h1)
    by_cases h2 : ty i = ComplexEmbedding.conjugate t₀
    · right
      apply (hi₀ j).1
      rw [hij, h2, hcc]
    exfalso
    have e1 := hS.eps (ty i) h1 h2
    have c1 : 1 ≤ typeMult n t₀ ε (ty i) := by
      rw [← hcard]
      exact Finset.card_pos.2 ⟨i, by simp⟩
    have c2 : 1 ≤ typeMult n t₀ ε (ComplexEmbedding.conjugate (ty i)) := by
      rw [← hcard]
      exact Finset.card_pos.2 ⟨j, by simp [hij]⟩
    have n1 : ComplexEmbedding.conjugate (ty i) ≠ t₀ := fun h => h2 (by rw [← h, hcc])
    have n2 : ComplexEmbedding.conjugate (ty i) ≠ ComplexEmbedding.conjugate t₀ := fun h =>
      h1 (by have := congrArg ComplexEmbedding.conjugate h; rwa [hcc, hcc] at this)
    simp only [typeMult, h1, h2, n1, n2, if_false] at c1 c2
    have a1 : ε (ty i) ≠ 0 := by
      intro h
      rw [h, mul_zero] at c1
      omega
    have a2 : ε (ComplexEmbedding.conjugate (ty i)) ≠ 0 := by
      intro h
      rw [h, mul_zero] at c2
      omega
    omega
  let W : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) :=
    { carrier := {S | Sᵀ = S ∧ ∀ (c : 𝓞 F) (i j : Fin g),
        S i j * ty j c = starRingEnd ℂ (ty i c) * S i j}
      add_mem' := by
        rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
        refine ⟨by rw [Matrix.transpose_add, hA1, hB1], fun c i j => ?_⟩
        simp only [Matrix.add_apply, add_mul, mul_add, hA2 c i j, hB2 c i j]
      zero_mem' := by
        refine ⟨Matrix.transpose_zero, fun c i j => ?_⟩
        simp
      smul_mem' := by
        rintro r A ⟨hA1, hA2⟩
        refine ⟨by rw [Matrix.transpose_smul, hA1], fun c i j => ?_⟩
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [_root_.mul_assoc, hA2 c i j]
        ring }
  have hbij := hTD F g ty t₀ i₀ (hS.cx t₀) hi₀ hpair W (fun S => Iff.rfl)
  have hmapmul : ∀ A B : Matrix (Fin g) (Fin g) ℂ, (A * B).map star = A.map star * B.map star := by
    intro A B
    ext i j
    simp [Matrix.mul_apply]
  have hdiagmap : ∀ v : Fin g → ℂ, (Matrix.diagonal v).map star =
      Matrix.diagonal fun i => starRingEnd ℂ (v i) := by
    intro v
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  set P := Sb.map star with hPdef
  have hPdet : P.det ≠ 0 := by
    have : P.det = starRingEnd ℂ Sb.det := by
      rw [RingHom.map_det]
      rfl
    rw [this]
    simpa using hSb
  have hSbu : IsUnit Sb.det := isUnit_iff_ne_zero.2 hSb
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hPdet
  have hPtu : IsUnit Pᵀ.det := by rw [Matrix.det_transpose]; exact hPu
  have hDc : ∀ c : 𝓞 F, (ρ (bar (a c))).map star * P = P * Matrix.diagonal fun i => ty i c := by
    intro c
    obtain ⟨c', hc'1, hc'2⟩ := hS.conj c
    have h1 := hρ c'
    rw [hc'1]
    have e : (fun i => ty i c') = fun i => starRingEnd ℂ (ty i c) := funext fun i => hc'2 (ty i)
    rw [e] at h1
    have h2 := congrArg (fun M : Matrix (Fin g) (Fin g) ℂ => M.map star) h1
    simp only [hmapmul, hdiagmap] at h2
    rw [h2, hPdef]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply]
  have hPt : ∀ c : 𝓞 F, Pᵀ * (ρ (a c))ᴴ = (Matrix.diagonal fun i => ty i c)ᴴ * Pᵀ := by
    intro c
    have hP' : Pᵀ = Sbᴴ := by
      ext i j
      simp [hPdef, Matrix.conjTranspose_apply]
    rw [hP', ← Matrix.conjTranspose_mul, hρ c, Matrix.conjTranspose_mul]
  haveI : Invertible P := P.invertibleOfIsUnitDet hPu
  have hcan : ∀ X Y : Matrix (Fin g) (Fin g) ℂ, Pᵀ * X * P = Pᵀ * Y * P → X = Y := by
    intro X Y h
    exact Matrix.mul_right_injective_of_invertible Pᵀ (Matrix.mul_left_injective_of_invertible P h)
  have hent : ∀ (Q : Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F),
      (∀ i j, Q i j * ty j c = starRingEnd ℂ (ty i c) * Q i j) ↔
        Q * Matrix.diagonal (fun i => ty i c) = (Matrix.diagonal fun i => ty i c)ᴴ * Q := by
    intro Q c
    constructor
    · intro h
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, h i j]
      rfl
    · intro h i j
      have := congrFun (congrFun h i) j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul] at this
      exact this
  have hQD : ∀ (S : Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F), Pᵀ * S * P * Matrix.diagonal (fun i => ty i c) =
      Pᵀ * (S * (ρ (bar (a c))).map star) * P := by
    intro S c
    rw [Matrix.mul_assoc (Pᵀ * S), ← hDc c]
    simp only [Matrix.mul_assoc]
  have hDQ : ∀ (S : Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F), (Matrix.diagonal fun i => ty i c)ᴴ * (Pᵀ * S * P) =
      Pᵀ * ((ρ (a c))ᴴ * S) * P := by
    intro S c
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hPt c]
    simp only [Matrix.mul_assoc]
  have hTW : ∀ S : Matrix (Fin g) (Fin g) ℂ, S ∈ PerCoordU.Tsp bar ρ ↔ Pᵀ * S * P ∈ W := by
    intro S
    show (Sᵀ = S ∧ ∀ x, S * (ρ (bar x)).map star = (ρ x)ᴴ * S) ↔
      ((Pᵀ * S * P)ᵀ = Pᵀ * S * P ∧ ∀ (c : 𝓞 F) (i j : Fin g),
        (Pᵀ * S * P) i j * ty j c = starRingEnd ℂ (ty i c) * (Pᵀ * S * P) i j)
    have htr : (Pᵀ * S * P)ᵀ = Pᵀ * Sᵀ * P := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [htr, h1], fun c => (hent _ c).2 ?_⟩
      rw [hQD, hDQ, h2]
    · rintro ⟨h1, h2⟩
      refine ⟨hcan _ _ (by rw [← htr, h1]), fun x => ?_⟩
      obtain ⟨c, rfl⟩ := hS.onto x
      apply hcan
      rw [← hQD, ← hDQ]
      exact (hent _ c).1 (h2 c)
  have hM0 : M₀.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 := hM.2.1 (star v) (by simpa using hv)
    simp [hermForm, hv0] at h1
  have hRos := transpose_rho_mul_herm_eq_herm_mul_bar D ρ P₀ M₀ hP hM
  set N := Sbᵀ * M₀ * P with hNdef
  have hNc : ∀ c : 𝓞 F, N * Matrix.diagonal (fun i => ty i c) = Matrix.diagonal (fun i => ty i c) * N := by
    intro c
    calc N * Matrix.diagonal (fun i => ty i c) = Sbᵀ * (M₀ * (ρ (bar (a c))).map star) * P := by
          rw [hNdef, Matrix.mul_assoc (Sbᵀ * M₀) P, ← hDc c]
          simp only [Matrix.mul_assoc]
      _ = (ρ (a c) * Sb)ᵀ * M₀ * P := by
          rw [← hRos, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => ty i c) * N := by
          rw [hρ c, Matrix.transpose_mul, Matrix.diagonal_transpose, hNdef]
          simp only [Matrix.mul_assoc]
  have hNcol : ∀ m, m ≠ i₀ → N m i₀ = 0 := by
    intro m hm
    by_contra hne
    have e : ty m = ty i₀ := ringHom_eq_of_eq_on_ringOfIntegers _ _ (fun c => by
      have e := congrFun (congrFun (hNc c) m) i₀
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
      exact (mul_left_cancel₀ hne (e.trans (mul_comm _ _))).symm)
    exact hm ((hi₀ m).1 (e.trans ((hi₀ i₀).2 rfl)))
  have hN0 : N i₀ i₀ ≠ 0 := by
    have hv : (fun k => Sb k i₀) ≠ 0 := by
      intro h
      apply hSb
      rw [← Matrix.det_transpose]
      exact Matrix.det_eq_zero_of_row_eq_zero i₀ (fun k => by simpa using congrFun h k)
    have hNh : N i₀ i₀ = hermForm M₀ (fun k => Sb k i₀) (fun k => Sb k i₀) := by
      simp only [hNdef, hPdef, hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
        Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
      rw [Finset.sum_comm]
      simp only [_root_.mul_assoc]
    intro h0
    have h1 := hM.2.1 _ hv
    rw [← hNh, h0] at h1
    simp at h1
  have hev : ∀ j, ev j ≠ 0 := by
    have h1 := congrArg Matrix.det hHS
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h1
    have h2 : H.det = ∏ i, ev i := mul_left_cancel₀ hSb h1
    intro j hj
    apply hH
    rw [h2]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  haveI : Invertible Sb := Sb.invertibleOfIsUnitDet hSbu
  haveI : Invertible M₀ := M₀.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hM0)
  have hCsp : ∀ b, (co b)ᵀ * M₀ ∈ PerCoordU.Tsp bar ρ := by
    intro b
    have : co b ∈ Csp bar ρ M₀ := hco.2 ▸ LinearMap.mem_range_self co b
    exact this
  have hin : ∀ b, Pᵀ * ((co b)ᵀ * M₀) * P ∈ W := fun b => (hTW _).1 (hCsp b)
  have hS'rel : ∀ b, Pᵀ * ((co b)ᵀ * M₀) * P = (Sb⁻¹ * co b * P)ᵀ * N := by
    intro b
    rw [hNdef]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.transpose_nonsing_inv]
  have hrow : ∀ b j, (Pᵀ * ((co b)ᵀ * M₀) * P) i₀ j = (Sb⁻¹ * co b * P) i₀ j * N i₀ i₀ := by
    intro b j
    have hw : (Pᵀ * ((co b)ᵀ * M₀) * P)ᵀ = Pᵀ * ((co b)ᵀ * M₀) * P ∧ _ := hin b
    have h1 := congrFun (congrFun hw.1 j) i₀
    rw [Matrix.transpose_apply] at h1
    rw [h1, hS'rel, Matrix.mul_apply, Finset.sum_eq_single i₀]
    · rfl
    · intro m _ hm
      rw [hNcol m hm, mul_zero]
    · simp
  have hEb : ∀ j, starRingEnd ℂ (ev j) ≠ 0 := fun j => by simpa using hev j
  set Eb := Matrix.diagonal fun j => starRingEnd ℂ (ev j) with hEbdef
  have hEbu : IsUnit Eb.det := by
    rw [hEbdef, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => hEb j)
  haveI : Invertible Eb := Eb.invertibleOfIsUnitDet hEbu
  have hEinv : Eb⁻¹ = Matrix.diagonal fun j => (starRingEnd ℂ (ev j))⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hEbdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (hEb j)
  have hHbu : IsUnit (H.map star).det := by
    have : (H.map star).det = starRingEnd ℂ H.det := by
      rw [RingHom.map_det]
      rfl
    rw [this]
    exact isUnit_iff_ne_zero.2 (by simpa using hH)
  haveI : Invertible (H.map star) := (H.map star).invertibleOfIsUnitDet hHbu
  have h1 : Sb⁻¹ * H = Matrix.diagonal ev * Sb⁻¹ := by
    calc Sb⁻¹ * H = Sb⁻¹ * (H * Sb) * Sb⁻¹ := by simp [Matrix.mul_assoc]
      _ = Matrix.diagonal ev * Sb⁻¹ := by rw [hHS]; simp [Matrix.mul_assoc]
  have h2 : H.map star * P = P * Eb := by
    have := congrArg (fun M : Matrix (Fin g) (Fin g) ℂ => M.map star) hHS
    simp only [hmapmul, hdiagmap] at this
    rw [hPdef, hEbdef]
    exact this
  have h3 : (H.map star)⁻¹ * P = P * Eb⁻¹ := by
    calc (H.map star)⁻¹ * P = (H.map star)⁻¹ * (P * Eb) * Eb⁻¹ := by simp [Matrix.mul_assoc]
      _ = P * Eb⁻¹ := by rw [← h2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHbu, Matrix.one_mul]
  have hTrel : ∀ b j, (Sb⁻¹ * co (T b) * P) i₀ j = mu / starRingEnd ℂ (ev j) * (Sb⁻¹ * co b * P) i₀ j := by
    intro b j
    rw [hT b]
    have e : Sb⁻¹ * (H * co b * (H.map star)⁻¹) * P = Matrix.diagonal ev * (Sb⁻¹ * co b * P) * Eb⁻¹ := by
      calc Sb⁻¹ * (H * co b * (H.map star)⁻¹) * P = (Sb⁻¹ * H) * co b * ((H.map star)⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h3]; simp only [Matrix.mul_assoc]
    rw [e, hEinv, Matrix.mul_diagonal, Matrix.diagonal_mul, hmu0]
    ring
  let ψ : (Fin d → ℂ) →ₗ[ℂ] ({j // ty j = ComplexEmbedding.conjugate t₀} → ℂ) :=
    { toFun := fun b j => (Sb⁻¹ * co b * P) i₀ j.val
      map_add' := by
        intro b b'
        funext j
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro r b
        funext j
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h0 : (⟨_, hin b⟩ : W) = 0 := hbij.1 (by
      funext j
      have hj := congrFun hb j
      change (Sb⁻¹ * co b * P) i₀ j.val = 0 at hj
      change (Pᵀ * ((co b)ᵀ * M₀) * P) i₀ j.val = (0 : Matrix (Fin g) (Fin g) ℂ) i₀ j.val
      rw [hrow, hj, zero_mul]
      rfl)
    have hQ : Pᵀ * ((co b)ᵀ * M₀) * P = 0 := congrArg Subtype.val h0
    have hQ2 : (co b)ᵀ * M₀ = 0 := hcan _ _ (by rw [hQ]; simp)
    have hQ3 : (co b)ᵀ = 0 := Matrix.mul_left_injective_of_invertible M₀ (by simpa using hQ2)
    have hQ4 : co b = 0 := by simpa using congrArg Matrix.transpose hQ3
    exact hco.1 (by rw [hQ4, map_zero])
  have hsurj : Function.Surjective ψ := by
    intro t
    obtain ⟨S', hS'⟩ := hbij.2 (fun j => N i₀ i₀ * t j)
    set S := (Pᵀ)⁻¹ * S'.val * P⁻¹ with hSdef
    have hSP : Pᵀ * S * P = S'.val := by simp [hSdef, Matrix.mul_assoc]
    have hSt : S ∈ PerCoordU.Tsp bar ρ := (hTW S).2 (by rw [hSP]; exact S'.2)
    set C := (S * M₀⁻¹)ᵀ with hCdef
    have hC : Cᵀ * M₀ = S := by simp [hCdef, Matrix.mul_assoc]
    have hCm : C ∈ Csp bar ρ M₀ := by
      show Cᵀ * M₀ ∈ PerCoordU.Tsp bar ρ
      rw [hC]
      exact hSt
    rw [← hco.2] at hCm
    obtain ⟨b, hb⟩ := hCm
    refine ⟨b, funext fun j => ?_⟩
    have h1 := hrow b j.val
    have hQb : Pᵀ * ((co b)ᵀ * M₀) * P = S'.val := by rw [hb, hC, hSP]
    rw [hQb] at h1
    have h2 := congrFun hS' j
    change S'.val i₀ j.val = N i₀ i₀ * t j at h2
    rw [h2] at h1
    change (Sb⁻¹ * co b * P) i₀ j.val = t j
    have h3 : N i₀ i₀ * (Sb⁻¹ * co b * P) i₀ j.val = N i₀ i₀ * t j := by
      rw [mul_comm]
      exact h1.symm
    exact mul_left_cancel₀ hN0 h3
  let e := LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hdet := det_one_sub_smul_eq_prod_of_diagonal T e (fun j => mu / starRingEnd ℂ (ev j.val)) (fun b j => hTrel b j.val)
  have hd : d = Fintype.card {j // ty j = ComplexEmbedding.conjugate t₀} := by
    have := LinearEquiv.finrank_eq e
    simpa using this
  have hJ : Fintype.card {j // ty j = ComplexEmbedding.conjugate t₀} = n - 1 := by
    rw [Fintype.card_subtype, hcard]
    simp [typeMult, hS.cx t₀]
  refine ⟨hd.trans hJ, fun y => ?_⟩
  rw [hdet y, evAt, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rw [Finset.prod_subtype (p := fun x => ty x = ComplexEmbedding.conjugate t₀) (Finset.univ.filter fun x => ty x = ComplexEmbedding.conjugate t₀)
    (fun x => by simp)]
  rfl
