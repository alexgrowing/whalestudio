import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CardZBasisEqMulFinrank
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspDataOfFamily
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin
open scoped Kronecker ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem ip_act_act (R : RiemLat E g Λ) (ω ω' : 𝓞 E) (x y : Fin g → ℂ) :
    R.ip (R.B ω x) (R.B ω' y) = ∑ s : E →+* ℂ, star (s (algebraMap (𝓞 E) E ω)) *
      R.ip (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x) (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) y) *
      s (algebraMap (𝓞 E) E ω') := by
  classical
  obtain ⟨-, -, h3, h4, h5⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have ex : ∀ (a : 𝓞 E) (x : Fin g → ℂ), R.B a x = ∑ s : E →+* ℂ,
      (s.comp (algebraMap (𝓞 E) E)) a • eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x := fun a x => by
    conv_lhs => rw [← h4 (R.B a x)]
    exact Finset.sum_congr rfl fun s _ => (h3 _).2.2.2 a x
  rw [ex ω x, ex ω' y, ip_sum_left]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ip_sum_right, Finset.sum_eq_single s]
  · rw [ip_smul_left, ip_smul_right]
    simp only [RingHom.comp_apply, Complex.star_def]
    ring
  · intro s' _ hs
    rw [ip_smul_left, ip_smul_right, h5 _ _ (comp_ne hs.symm) _ ((h3 _).1 x) _ ((h3 _).1 y)]
    simp
  · simp

theorem ip_im_eq_zero (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) {x y : Λ}
    (hx : x ∈ I) (hy : y ∈ I) : (R.ip (R.P x) (R.P y)).im = 0 := by
  have h := R.im y x
  rw [hI y hy x hx] at h
  simpa [RiemLat.ip] using h

theorem gram_tower (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) {ρ : ℕ} {v : Fin ρ → Λ}
    (hv : ∀ a, v a ∈ I) (hli : LinearIndependent (𝓞 E) v) [DecidableEq (E →+* ℂ)] :
    Complex.ofRealHom.mapMatrix (Matrix.of fun p q =>
        (R.ip (R.P (towerZBasis hli p : Λ)) (R.P (towerZBasis hli q : Λ))).re) =
      ((1 : Matrix (Fin ρ) (Fin ρ) ℂ) ⊗ₖ (basisMatrix E)ᵀ)ᴴ *
        blockDiagonal (fun s : E →+* ℂ => R.gram fun a => eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P (v a))) *
        ((1 : Matrix (Fin ρ) (Fin ρ) ℂ) ⊗ₖ (basisMatrix E)ᵀ) := by
  have hJI : Submodule.span (𝓞 E) (Set.range v) ≤ I :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hv a)
  ext ⟨a, τ⟩ ⟨b, τ'⟩
  have hre : ((R.ip (R.P (towerZBasis hli (a, τ) : Λ)) (R.P (towerZBasis hli (b, τ') : Λ))).re : ℂ) =
      R.ip (R.P (towerZBasis hli (a, τ) : Λ)) (R.P (towerZBasis hli (b, τ') : Λ)) := by
    apply Complex.ext
    · simp
    · simpa using (ip_im_eq_zero R hI (hJI (towerZBasis hli (a, τ)).2) (hJI (towerZBasis hli (b, τ')).2)).symm
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Complex.ofRealHom_eq_coe, hre]
  simp only [towerZBasis_apply, R.act]
  rw [ip_act_act]
  simp only [mul_apply, conjTranspose_apply, kroneckerMap_apply, one_apply, transpose_apply,
    blockDiagonal_apply, Fintype.sum_prod_type, basisMatrix_apply']
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, star_zero, apply_ite star,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.sum_eq_single b fun x hx ↦ by simp [hx]]
  simp only [if_true]
  rfl

section CM

variable {Ψ : Type} [Fintype Ψ]

omit [IsCMField E] in
theorem emb_ext {s s' : E →+* ℂ} (h : s.comp (algebraMap (𝓞 E) E) = s'.comp (algebraMap (𝓞 E) E)) : s = s' := by
  by_contra hs
  exact comp_ne hs h

omit [IsCMField E] in
theorem conj_extEmb_comp (t : 𝓞 E →+* ℂ) :
    ((starRingEnd ℂ).comp (extEmb t)).comp (algebraMap (𝓞 E) E) = (starRingEnd ℂ).comp t := by
  rw [RingHom.comp_assoc, extEmb_comp]

def cmSum (σ : Ψ → (𝓞 E →+* ℂ)) : Ψ ⊕ Ψ → (E →+* ℂ) :=
  Sum.elim (fun τ => extEmb (σ τ)) fun τ => (starRingEnd ℂ).comp (extEmb (σ τ))

theorem cmSum_bijective {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) : Function.Bijective (cmSum σ) := by
  have cross : ∀ a b, (extEmb (σ a) : E →+* ℂ) ≠ (starRingEnd ℂ).comp (extEmb (σ b)) := by
    intro a b h
    have h1 := congrArg (fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)) h
    simp only [extEmb_comp, conj_extEmb_comp] at h1
    exact (hσ.2 (σ b)).1 ⟨b, rfl⟩ ⟨a, h1⟩
  constructor
  · rintro (a | a) (b | b) h
    · have h1 := congrArg (fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)) h
      simp only [cmSum, Sum.elim_inl, extEmb_comp] at h1
      exact congrArg Sum.inl (hσ.1 h1)
    · exact absurd h (cross a b)
    · exact absurd h.symm (cross b a)
    · have h1 : σ a = σ b := RingHom.ext fun x => by
        have h2 := congrArg (fun φ : E →+* ℂ => starRingEnd ℂ (φ (algebraMap (𝓞 E) E x))) h
        simpa [cmSum, extEmb_apply] using h2
      exact congrArg Sum.inr (hσ.1 h1)
  · intro s
    by_cases h : ∃ τ, σ τ = s.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := h
      exact ⟨Sum.inl τ, emb_ext (by simp only [cmSum, Sum.elim_inl, extEmb_comp, hτ])⟩
    · have h' : ∃ τ, σ τ = (starRingEnd ℂ).comp (s.comp (algebraMap (𝓞 E) E)) := by
        by_contra h''
        exact h ((hσ.2 _).2 h'')
      obtain ⟨τ, hτ⟩ := h'
      refine ⟨Sum.inr τ, emb_ext ?_⟩
      simp only [cmSum, Sum.elim_inr, conj_extEmb_comp, hτ]
      ext x
      simp

theorem finrank_eq_two_card {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) :
    Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  classical
  rw [← NumberField.Embeddings.card E ℂ, ← Fintype.card_of_bijective (cmSum_bijective hσ), Fintype.card_sum]
  ring

theorem prod_det_gram (R : RiemLat E g Λ) {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) {I : Submodule (𝓞 E) Λ}
    (hI : IsIsoSub R.form I) {ρ : ℕ} {v : Fin ρ → Λ} (hv : ∀ a, v a ∈ I) :
    ∏ s : E →+* ℂ, (R.gram fun a => eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P (v a))).det =
      ((∏ τ, ((R.gram fun a => eigComp R.B (σ τ) (R.P (v a))).det.re) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← (Equiv.ofBijective _ (cmSum_bijective hσ)).prod_comp, Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib]
  push_cast
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [Equiv.ofBijective_apply, cmSum, Sum.elim_inl, Sum.elim_inr, extEmb_comp, conj_extEmb_comp]
  set G := R.gram fun a => eigComp R.B (σ τ) (R.P (v a)) with hGdef
  have hconj : (R.gram fun a => eigComp R.B ((starRingEnd ℂ).comp (σ τ)) (R.P (v a))) = G.map (starRingEnd ℂ) := by
    ext a b
    exact (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Ψ R I hI (σ τ)).1 _ (hv a) _ (hv b)
  have htr : G.map (starRingEnd ℂ) = Gᵀ := by
    ext a b
    exact ip_conj R _ _
  have hdet : starRingEnd ℂ G.det = G.det := by
    have h1 := RingHom.map_det (starRingEnd ℂ) G
    rw [RingHom.mapMatrix_apply, htr, det_transpose] at h1
    exact h1
  have hre : (G.det.re : ℂ) = G.det := Complex.conj_eq_iff_re.1 hdet
  rw [hconj, htr, det_transpose, hre]
  ring

end CM

section Tower

variable {Ψ : Type} [Fintype Ψ]

open Classical in

theorem det_gram_tower (R : RiemLat E g Λ) {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) {I : Submodule (𝓞 E) Λ}
    (hI : IsIsoSub R.form I) {ρ : ℕ} {v : Fin ρ → Λ} (hv : ∀ a, v a ∈ I) (hli : LinearIndependent (𝓞 E) v) :
    (Matrix.of fun p q => (R.ip (R.P (towerZBasis hli p : Λ)) (R.P (towerZBasis hli q : Λ))).re).det =
      |(discr E : ℝ)| ^ ρ * ∏ τ, ((R.gram fun a => eigComp R.B (σ τ) (R.P (v a))).det.re) ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hG := congrArg Matrix.det (gram_tower R hI hv hli)
  rw [← RingHom.map_det, Complex.ofRealHom_eq_coe] at hG
  rw [hG, det_mul, det_mul, det_conjTranspose, det_kronecker, det_one, one_pow, one_mul,
    det_transpose, det_blockDiagonal]
  have hB : star (basisMatrix E).det * (basisMatrix E).det = ((|(discr E : ℝ)| : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow, det_basisMatrix_sq]
    simp
  rw [prod_det_gram R hσ hI hv, Fintype.card_fin, star_pow]
  have key : star (basisMatrix E).det ^ ρ * (basisMatrix E).det ^ ρ =
      ((|(discr E : ℝ)| : ℝ) : ℂ) ^ ρ := by
    rw [← mul_pow, hB]
  push_cast at key ⊢
  linear_combination
    (∏ τ, ((R.gram fun a => eigComp R.B (σ τ) (R.P (v a))).det.re : ℂ) ^ 2) * key

omit [IsCMField E] in

theorem card_basis_eq (htf : ∀ (n : ℕ) (x : Λ), n ≠ 0 → n • x = 0 → x = 0) {I : Submodule (𝓞 E) Λ} {ρ : ℕ}
    {v : Fin ρ → Λ} (hv : IsNzFamily I ρ v) {m : ℕ} (b : Module.Basis (Fin m) ℤ I) :
    m = ρ * Module.finrank ℚ E := by
  obtain ⟨-, hvI, hli, hidx⟩ := hv
  set J := Submodule.span (𝓞 E) (Set.range v) with hJdef
  have hJI : J ≤ I := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hvI a)
  let B := towerZBasis hli
  haveI : Module.Finite ℤ J := Module.Finite.of_basis B
  haveI : Module.Finite ℤ I := Module.Finite.of_basis b
  have hJ : Module.finrank ℤ J = ρ * Module.finrank ℚ E := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_prod, Fintype.card_fin, NumberField.Embeddings.card]
  have hIr : Module.finrank ℤ I = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let i1 : J →+ I :=
    { toFun := fun x => ⟨x, hJI x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let i2 : I →+ J :=
    { toFun := fun x => ⟨J.toAddSubgroup.relIndex I.toAddSubgroup • (x : Λ),
        AddSubgroup.nsmul_relIndex_mem J.toAddSubgroup (K := I.toAddSubgroup) x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have h1 : Function.Injective i1.toIntLinearMap := fun x y h =>
    Subtype.ext (congrArg (fun z : I => (z : Λ)) h)
  have h2 : Function.Injective i2.toIntLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : J.toAddSubgroup.relIndex I.toAddSubgroup • (x : Λ) = 0 := congrArg (fun z : J => (z : Λ)) hx
    exact Subtype.ext (htf _ _ hidx hx')
  have l1 := LinearMap.finrank_le_finrank_of_injective h1
  have l2 := LinearMap.finrank_le_finrank_of_injective h2
  omega

omit [IsCMField E] in
open Classical in

theorem det_gram_index (f : Λ →+ Λ →+ ℝ) {I : Submodule (𝓞 E) Λ} {ρ : ℕ} {v : Fin ρ → Λ}
    (hv : IsNzFamily I ρ v) {m : ℕ} (b : Module.Basis (Fin m) ℤ I) (hm : m = ρ * Module.finrank ℚ E) :
    (Matrix.of fun p q => f (towerZBasis hv.2.2.1 p : Λ) (towerZBasis hv.2.2.1 q : Λ)).det =
      ((Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) ^ 2 *
        (Matrix.of fun k l => f (b k : Λ) (b l : Λ)).det := by
  have hli := hv.2.2.1
  set J := Submodule.span (𝓞 E) (Set.range v)
  have hJI : J.toAddSubgroup ≤ I.toAddSubgroup :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hv.2.1 a)
  have hc : Fintype.card (Fin m) = Fintype.card (Fin ρ × (E →+* ℂ)) := by
    rw [Fintype.card_fin, hm, Fintype.card_prod, Fintype.card_fin, NumberField.Embeddings.card]
  let e : Fin m ≃ Fin ρ × (E →+* ℂ) := Fintype.equivOfCardEq hc
  let eI : I ≃+ I.toAddSubgroup.toIntSubmodule :=
    { toFun := fun x => ⟨x, x.2⟩, invFun := fun x => ⟨x, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  let B₂ : Module.Basis (Fin ρ × (E →+* ℂ)) ℤ I.toAddSubgroup.toIntSubmodule :=
    (b.map eI.toIntLinearEquiv).reindex e
  have hB₂ : ∀ k, (B₂ k : Λ) = b (e.symm k) := by
    intro k
    simp only [B₂, Module.Basis.reindex_apply, Module.Basis.map_apply]
    rfl
  let eJ : J ≃+ J.toAddSubgroup.toIntSubmodule :=
    { toFun := fun x => ⟨x, x.2⟩, invFun := fun x => ⟨x, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  let B₁ : Module.Basis (Fin ρ × (E →+* ℂ)) ℤ J.toAddSubgroup.toIntSubmodule :=
    (towerZBasis hli).map eJ.toIntLinearEquiv
  have hidx := AddSubgroup.relIndex_eq_natAbs_det J.toAddSubgroup I.toAddSubgroup hJI B₁ B₂
  rw [Module.Basis.det_apply] at hidx
  set M := B₂.toMatrix fun i => (⟨B₁ i, hJI (SetLike.coe_mem _)⟩ : I.toAddSubgroup.toIntSubmodule)
  have hexp : ∀ p, (towerZBasis hli p : Λ) = ∑ k, M k p • (b (e.symm k) : Λ) := by
    intro p
    have h := congrArg Subtype.val (B₂.sum_repr ⟨B₁ p, hJI (SetLike.coe_mem _)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hB₂] at h
    have hB₁ : (B₁ p : Λ) = towerZBasis hli p := rfl
    rw [← hB₁, ← h]
    rfl
  have hgram : (Matrix.of fun p q => f (towerZBasis hli p : Λ) (towerZBasis hli q : Λ)) =
      (M.map (Int.cast : ℤ → ℝ))ᵀ * (Matrix.of fun k l => f (b k : Λ) (b l : Λ)).submatrix e.symm e.symm *
        M.map (Int.cast : ℤ → ℝ) := by
    ext p q
    rw [Matrix.of_apply, hexp p, hexp q]
    simp only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.coe_smul, Pi.smul_apply]
    simp only [zsmul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hc' : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det M
    simpa using this.symm
  rw [hgram, det_mul, det_mul, det_transpose, det_submatrix_equiv_self, hidx, Nat.cast_natAbs,
    Int.cast_abs, sq_abs, hc']
  ring

end Tower

def reForm (R : RiemLat E g Λ) : Λ →+ Λ →+ ℝ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => (R.ip (R.P x) (R.P y)).re)
    (fun a b => by simp [map_add, ip_add_right])) (fun a b => by ext y; simp [map_add, ip_add_left])

theorem reForm_apply (R : RiemLat E g Λ) (x y : Λ) : reForm R x y = (R.ip (R.P x) (R.P y)).re := rfl

theorem rd_sq {f : ℕ} (hn : Module.finrank ℚ E = 2 * f) (ρ : ℕ) :
    ((|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) ^ (f * ρ)) ^ 2 = |(discr E : ℝ)| ^ ρ := by
  have hpos : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  have h := Real.rpow_inv_natCast_pow (abs_nonneg (discr E : ℝ)) hpos
  rw [one_div, ← pow_mul, show f * ρ * 2 = Module.finrank ℚ E * ρ by rw [hn]; ring, pow_mul, h]

theorem det_re_gram_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ),
    IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → ∀ (m : ℕ) (b : Module.Basis (Fin m) ℤ I),
    m = 2 * Fintype.card Ψ * Module.finrank (𝓞 E) I ∧
    (Matrix.of fun i j => (R.ip (R.P (b i : Λ)) (R.P (b j : Λ))).re).det =
      (R.nz σ I * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) ^
        (Fintype.card Ψ * Module.finrank (𝓞 E) I)) ^ 2 := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I hσ hI hne m b
  obtain ⟨⟨r, v, hv⟩, hall⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ R σ I hσ hI hne
  obtain ⟨hnz, -, hr⟩ := hall r v hv
  have hf := finrank_eq_two_card hσ
  have htf : ∀ (n : ℕ) (x : Λ), n ≠ 0 → n • x = 0 → x = 0 := by
    intro n x hn hx
    obtain ⟨hinj, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
    apply hinj
    have h1 : n • R.P x = 0 := by rw [← map_nsmul, hx, map_zero]
    rw [map_zero]
    exact (smul_eq_zero.1 (by rw [← Nat.cast_smul_eq_nsmul ℂ] at h1; exact h1)).resolve_left (by exact_mod_cast hn)
  have hm := card_basis_eq htf hv b
  refine ⟨by rw [hm, hf, ← hr]; ring, ?_⟩
  have h1 := det_gram_index (reForm R) hv b hm
  simp only [reForm_apply] at h1
  rw [det_gram_tower R hσ hI hv.2.1 hv.2.2.1] at h1
  have hidx : ((Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hv.2.2.2
  rw [hnz, ← hr, mul_pow, rd_sq hf, RiemLat.nzOf, div_pow, ← Finset.prod_pow]
  field_simp
  linarith [h1]

end GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol
