import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem integral_add_left_haar {G : Type} [MeasurableSpace G] [TopologicalSpace G] [AddGroup G] (μ : Measure G)
    [μ.IsAddHaarMeasure] (g : G) (f : G → ℂ) : ∫ x, f (g + x) ∂μ = ∫ x, f x ∂μ := by
  have hne : μ ≠ 0 := by
    intro h0
    have := IsOpen.measure_ne_zero μ isOpen_univ Set.univ_nonempty
    simp [h0] at this
  have aem : ∀ g' : G, AEMeasurable (fun x => g' + x) μ := by
    intro g'
    by_contra hc
    have := Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) g'
    rw [Measure.map_of_not_aemeasurable hc] at this
    exact hne this.symm
  have hmap : Measure.map (fun x => g + x) μ = μ := Measure.IsAddLeftInvariant.map_add_left_eq_self g
  by_cases hf : AEStronglyMeasurable f μ
  · conv_rhs => rw [← hmap]
    rw [integral_map (aem g) (by rwa [hmap])]
  · have hf' : ¬ AEStronglyMeasurable (fun x => f (g + x)) μ := by
      intro h
      apply hf
      have h2 : AEStronglyMeasurable (fun x => f (g + x)) (Measure.map (fun x => -g + x) μ) := by
        rwa [Measure.IsAddLeftInvariant.map_add_left_eq_self]
      have := h2.comp_aemeasurable (aem (-g))
      simpa [Function.comp_def, add_neg_cancel_left] using this
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hf']

theorem holValueAt_const_mul {h : ℂ → ℂ} {s v : ℂ} (c : ℂ) (hh : HolValueAt h s v) :
    HolValueAt (fun z => c * h z) s (c * v) := by
  obtain ⟨H, ⟨U, hsU, hU, hmer, σ', heq⟩, han, rfl⟩ := hh
  refine ⟨fun z => c * H z, ⟨U, hsU, hU, fun z hz => (MeromorphicAt.const c z).mul (hmer z hz), σ', ?_⟩,
    analyticAt_const.mul han, rfl⟩
  intro z hz
  simp only [heq hz]

theorem incM_mul_inv (d : SD σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_inv_mul (d : SD σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.inv_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inFrame_mul (d : SD σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have h1 := incM_mul_inv d
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem matrix_eq_frame_conjugate (d : SD σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  simp only [inFrame, ← Matrix.mul_assoc, incM_mul_inv d, Matrix.one_mul]
  rw [Matrix.mul_assoc, incM_mul_inv d, Matrix.mul_one]

theorem inFrame_injective (d : SD σ) : Function.Injective (inFrame (σ := σ) (Y := d.Y) d.b) := by
  intro x y h
  have : mat2 x = mat2 y := by rw [matrix_eq_frame_conjugate d x, matrix_eq_frame_conjugate d y, h]
  exact Subtype.ext (Units.ext this)

theorem om_mem_sch (d : SD σ) (g : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om g Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres g Φ h

theorem section_mul_weil_action (d : SD σ) (Φ : d.Fn) (g k : d.G) : d.sec0 Φ (g * k) = d.sec0 (d.om k Φ) g := by
  simp [SD.sec0, map_mul, Module.End.mul_apply]

theorem a_mul_K (d : SD σ) (g k : d.G) (hk : k ∈ d.K) : d.a (g * k) = d.a g := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := d.ok.hgt.iwa g
  rw [mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']

theorem kfin_om (d : SD σ) {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) : d.KFin (d.om k Φ) := by
  refine ⟨om_mem_sch d k hΦ.1, ?_⟩
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩
  simp [map_mul, Module.End.mul_apply]

section Forms

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem form_conj_in (c : R →+* R) {X Y M J : Matrix ι ι R} (hXY : X * Y = 1) (hM : Mᵀ * J * M.map c = J) :
    (Y * M * X)ᵀ * (Xᵀ * J * X.map c) * (Y * M * X).map c = Xᵀ * J * X.map c := by
  have h1 : Yᵀ * Xᵀ = 1 := by rw [← Matrix.transpose_mul, hXY, Matrix.transpose_one]
  have h2 : X.map c * Y.map c = 1 := by rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero c) (map_one c)]
  simp only [Matrix.transpose_mul, Matrix.map_mul]
  calc _ = Xᵀ * (Mᵀ * ((Yᵀ * Xᵀ) * J * (X.map c * Y.map c)) * M.map c) * X.map c := by
        simp only [Matrix.mul_assoc]
    _ = Xᵀ * J * X.map c := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hM]

theorem form_conj_out (c : R →+* R) {X Y N J : Matrix ι ι R} (hXY : X * Y = 1)
    (hN : Nᵀ * (Xᵀ * J * X.map c) * N.map c = Xᵀ * J * X.map c) :
    (X * N * Y)ᵀ * J * (X * N * Y).map c = J := by
  have h1 : Yᵀ * Xᵀ = 1 := by rw [← Matrix.transpose_mul, hXY, Matrix.transpose_one]
  have h2 : X.map c * Y.map c = 1 := by rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero c) (map_one c)]
  simp only [Matrix.transpose_mul, Matrix.map_mul]
  calc _ = Yᵀ * (Nᵀ * (Xᵀ * J * X.map c) * N.map c) * Y.map c := by simp only [Matrix.mul_assoc]
    _ = (Yᵀ * Xᵀ) * J * (X.map c * Y.map c) := by rw [hN]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem block_diag_form (c : R →+* R) {κ : Type} [Fintype κ] [DecidableEq κ] (A B D C' : Matrix κ κ R)
    (h : (Matrix.fromBlocks A B 0 D)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (Matrix.fromBlocks A B 0 D).map c =
      Matrix.fromBlocks 0 1 C' 0) :
    (Matrix.fromBlocks A 0 0 D)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (Matrix.fromBlocks A 0 0 D).map c =
      Matrix.fromBlocks 0 1 C' 0 := by
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero c), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, trivial⟩

end Forms

local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y

omit [NumberField E] in
theorem incM_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    incM F (X ⬝ Y) = incM F X ⬝ incM F Y := Matrix.map_mul

theorem frame_form (d : SD σ) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  simp [incM, Matrix.fromBlocks_map]

theorem parabolic_lower_block_zero (d : SD σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    (inFrame d.b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1 := htb
  have hp' : mat2 p ⬝ DC = DC ⬝ t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M ⬝ E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 ⬝ E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1) = DC ⬝ incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 ⬝ E1 = DC ⬝ incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 ⬝ incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 ⬝ incM F d.b.1 = 1 := incM_inv_mul d
  have hdc : DC = incM F d.b.1 ⬝ E1 ⬝ incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p ⬝ E1 = E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 ⬝ mat2 p ⬝ incM F d.b.1 := rfl
    calc inFrame d.b p ⬝ E1 = incM F (d.b⁻¹).1 ⬝ (mat2 p ⬝ (incM F d.b.1 ⬝ E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((mat2 p ⬝ DC) ⬝ incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((DC ⬝ t.1) ⬝ incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 ⬝ incM F d.b.1) ⬝ E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inr i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type] using this

theorem par_decomp (d : SD σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ (n0 m0 : d.G) (β₀ : Mx F E d.n d.n), inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1 ∧ IsLevi d m0 ∧ p = n0 * m0 := by
  have h21 := parabolic_lower_block_zero d p t hp
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_mul_inv d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_inv_mul d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := frame_form d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := form_conj_in (cA σ).toRingHom (incM_mul_inv d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := form_conj_out (cA σ).toRingHom (incM_mul_inv d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, incM_inv_mul d, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩
  · have e := inFrame_mul d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]

theorem gram_mat_inv (d : SD σ) (g : UA σ d.A.J) (X : Mx F E d.m d.n) :
    d.gram (mat g⁻¹ * X) (mat g⁻¹ * X) = d.gram X X := by
  have hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J := (g⁻¹).2
  have hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  simp only [SD.gram, Matrix.transpose_mul, hm]
  calc Xᵀ * (mat g⁻¹)ᵀ * incM F d.A.J * ((mat g⁻¹).map (cA σ) * X.map (cA σ))
      = Xᵀ * ((mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ)) * X.map (cA σ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg]

theorem phase (d : SD σ) (T β₀ : Mx F E d.n d.n) :
    -(⅟(2 : AF F) * d.tt (β₀ * ((-2 : ℤ) • T))) = d.tt (T * β₀) := by
  have h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀) := by
    simp only [SD.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]

theorem orb_n (hT : TAll) (d : SD σ) (T : nF σ d.Y d.b) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) (n0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) :
    d.orb T (d.om n0 Ψ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T Ψ := by
  have hP := (hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn
  have hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E),
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 →
      d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X) := by
    intro g X hX
    rw [hP, gram_mat_inv, hX, phase]
  have hs : ∀ g : UA σ d.A.J,
      (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T Ψ (mat g⁻¹ * incM F X.1) := by
    intro g
    rw [← tsum_mul_left]
    exact tsum_congr fun X => hpt g X.1 X.2
  simp only [SD.orb]
  simp_rw [hs]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _

theorem int_n (d : SD σ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b))
    (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (w n0 m0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) (f : d.G → ℂ) :
    ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
      d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, f (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
  have := hcd.2.1
  have hβ₀ : β₀ ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨n0, hn⟩
  let b₀ : nA σ d.Y d.b := ⟨β₀, hβ₀⟩
  have hnb : ∀ β, nb β * n0 = nb (b₀ + β) := by
    intro β
    apply inFrame_injective d
    rw [inFrame_mul, hcd.1 β, hn, hcd.1 (b₀ + β)]
    simp [Matrix.fromBlocks_multiply, add_comm, b₀]
  have htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1) := by
    intro β
    simp [SD.tt, Matrix.mul_add, Matrix.trace_add, map_add, b₀]
  calc ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
      = ∫ β, (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) *
          d.B.ψ (d.tt (T.1.1 * β₀)))) (b₀ + β) ∂lam := by
        congr 1
        funext β
        dsimp only
        rw [← hnb β, htt β, ← AddChar.map_add_eq_mul,
          show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]
        simp only [mul_assoc]
    _ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam :=
        integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) *
          (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))
    _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext β
        ring

theorem iwaRed : IwaRed := by
  intro hT hL F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hcd ε w hw T hTnd x
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp d p t hp
  have key := hL F E σ d hnm hE (d.om k Φ) (kfin_om d hΦ hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    simp only [flat]
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc], a_mul_K d _ k hk,
      section_mul_weil_action]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ hΦ.1)) n0 β₀ hn
  rw [e1, e2]
  exact holValueAt_const_mul _ key

end PositivityTheory.SiegelWeilFormula.KWhit

end
