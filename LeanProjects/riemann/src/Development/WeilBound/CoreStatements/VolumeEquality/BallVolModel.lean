import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

theorem qconj_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (x : E) :
    GroundTheory.Automorphic.conj (maximalRealSubfield E) E x = IsCMField.complexConj E x :=
  HermTrace.quadConj_eq_complexConj x

theorem sesq_eq_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (h : GroundTheory.Automorphic.HermitianForm (maximalRealSubfield E) E (Fin N → E)) (r : E) (x y : Fin N → E) :
    herm (r • (GroundTheory.Automorphic.gram h.toSesq (Pi.basisFun E (Fin N)))ᵀ) x y = r * h.toSesq y x := by
  rw [GroundTheory.Automorphic.sesq_eq_sum h.toSesq (Pi.basisFun E (Fin N)), herm, Finset.sum_comm]
  simp only [Finset.mul_sum, qconj_eq, Pi.basisFun_repr, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, cc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sgI_sq (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem stdModel_of (h : StdZ) : StdModel := by
  intro E _ _ _ Ψ _ _ j j' n g Λ _ _ H F ξ c₀ hc₀ hξ
  obtain ⟨C⟩ := GlobalTheory.T.exists_lattice_embedding E Ψ j j' n g Λ H F
  obtain ⟨A, hA, Z, hbij, hmeas, hZ⟩ := h E Ψ j j' n g Λ F C
  obtain ⟨τ₀⟩ := ‹Nonempty Ψ›
  have hc := C.c_pos
  have hc₀' : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀.ne'
  have hξ0 : ξ ≠ 0 := fun h0 => by
    have := hξ τ₀
    rw [h0, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero hc₀' this.symm
  set r : E := C.xi / ξ with hr
  have hsr : ∀ τ, embOf (F.σ τ) r = ((C.c / c₀ * C.eps τ : ℝ) : ℂ) := fun τ => by
    rw [hr, map_div₀, C.xi_eq, hξ]
    push_cast
    field_simp
  have heps : ∀ τ, C.eps τ ≠ 0 := fun τ h0 => by
    have := C.eps_sq τ
    rw [h0] at this
    norm_num at this
  have hsr0 : ∀ τ, embOf (F.σ τ) r ≠ 0 := fun τ => by
    rw [hsr]
    exact_mod_cast mul_ne_zero (div_pos hc hc₀).ne' (heps τ)
  have hr0 : r ≠ 0 := fun h0 => hsr0 τ₀ (by rw [h0, map_zero])
  have hcr : cc r = r := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, hsr, Complex.conj_ofReal])
  set g₀ := GroundTheory.Automorphic.gram C.h.toSesq (Pi.basisFun E (Fin (j + j'))) with hg₀
  have hGs : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = embOf (F.σ τ) r • C.gr τ := fun τ => by
    ext a b
    simp [LatEmb.gr, hg₀]
  have hGs' : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = ((C.c / c₀ : ℝ) : ℂ) • C.sgr τ := fun τ => by
    rw [hGs, hsr, LatEmb.sgr, smul_smul, Complex.ofReal_mul]
  let e : Λ →ₗ[𝓞 E] (Fin (j + j') → E) :=
    { toFun := C.e, map_add' := C.e.map_add, map_smul' := fun a x => C.e_smul a x }
  let k : ℝ := Real.sqrt (c₀ / C.c)
  have hk : 0 < k := Real.sqrt_pos.2 (div_pos hc₀ hc)
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkk : (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) * k = 1 := by
    have : k * (C.c / c₀) * k = 1 := by
      have h1 : k * k = c₀ / C.c := Real.mul_self_sqrt (div_pos hc₀ hc).le
      rw [mul_right_comm, h1]
      field_simp
    exact_mod_cast this
  have hl : ∀ τ, C.cinv (A τ) τ * A τ = 1 := fun τ => by
    rw [LatEmb.cinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A τ)ᴴ, hA, sgI_sq]
  have hrr : ∀ τ, A τ * C.cinv (A τ) τ = 1 := fun τ =>
    (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (hl τ)
  have hform : ∀ x y, ((F.form x y : ℤ) : ℚ) = EFf (-ξ) (r • g₀ᵀ) (e x) (e y) := fun x y => by
    rw [C.form_eq, EFf, hg₀, sesq_eq_herm, neg_neg, ← mul_assoc, hr, mul_div_cancel₀ _ hξ0]
    rfl
  refine ⟨r • g₀ᵀ, e, fun τ => (k : ℂ) • A τ, fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ, Z, fun a b => ?_, ?_, C.e_inj, ⟨?_, ?_⟩,
    hform, fun τ => ⟨?_, ?_, ?_⟩, hbij, hmeas, fun γ hγ δ hδ t ht t' ht' => ?_⟩
  · have h1 : cc (g₀ b a) = g₀ a b := by
      rw [cc, ← qconj_eq]
      exact C.h.isSymm.eq _ _
    show cc (r * g₀ b a) = r * g₀ a b
    rw [← h1]
    conv_rhs => rw [← hcr]
    exact map_mul (IsCMField.complexConj E) _ _
  · rw [det_smul, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr0) (GroundTheory.Automorphic.isUnit_det_gram C.h _).ne_zero
  · have := (F.R 0).fin
    have : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ _ _
    exact Module.Finite.iff_fg.1 inferInstance
  · exact C.integral.isLattice.span_eq_top
  · rw [hGs', conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      hA, smul_smul, smul_smul]
    have : star (k : ℂ) * (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_ofReal, mul_right_comm, hkk]
    rw [this, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ hk', one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, mul_inv_cancel₀ hk', one_smul]
  · have hγ' : (γ : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * (r • g₀ᵀ) *
        (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = r • g₀ᵀ := hγ
    have hrho : rho (fun τ => embOf (F.σ τ)) (fun τ => (k : ℂ) • A τ) (fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ) γ =
        rho (fun τ => embOf (F.σ τ)) A (fun τ => C.cinv (A τ) τ) γ := by
      funext τ
      simp only [rho]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul]
    rw [hrho]
    refine hZ γ δ hδ (fun x y => ?_) (fun τ => ?_) t ht t' ht'
    · have h1 := hform (δ x) (δ y)
      rw [hδ, hδ, EFf, herm_mulVec', hγ', ← EFf, ← hform] at h1
      exact_mod_cast h1
    · have h1 := congrArg (fun M => (M.map (embOf (F.σ τ)))ᵀ) hγ'
      have h2 : (((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E)).map (embOf (F.σ τ)))ᵀ =
          ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)))ᴴ := by
        ext a b
        exact IsCMField.complexEmbedding_complexConj E (embOf (F.σ τ)) ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E) b a)
      simp only [Matrix.map_mul, transpose_mul] at h1
      rw [hGs, h2, ← Matrix.transpose_map, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul] at h1
      rw [Matrix.mul_assoc]
      exact smul_right_injective _ (hsr0 τ) h1

end SheetDecomposition
