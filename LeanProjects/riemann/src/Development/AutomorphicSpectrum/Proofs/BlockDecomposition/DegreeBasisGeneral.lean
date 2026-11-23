import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegBasisGen

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem exists_left_inv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ K) (hP : LinearIndependent K Pᵀ) : ∃ Y : Matrix κ ι K, Y * P = 1 := by
  have inj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := hv
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum] at h0
    simp only [op_smul_eq_smul] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 hP v h0 i
  obtain ⟨f, hf⟩ := P.mulVecLin.exists_leftInverse_of_injective inj
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h := congrArg LinearMap.toMatrix' hf
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] at h

theorem degG_reindex (hF : WedgeF) (hI : WedgeI) {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ' ≃ κ) (x : GA E n) (M : Matrix (Fin n) κ E) :
    degG x (M.submatrix id e) = degG x M := by
  have hfr : (x⁻¹ : GA E n).val * (M.submatrix id e).map (algebraMap E (Ad E)) =
      ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hv : ∀ v, nI ((A.submatrix id e).map (cV v)) = nI (A.map (cV v)) := fun v => by
    rw [← Matrix.submatrix_map]
    exact (hI (Fin n)).reindex κ κ' e (A.map (cV v))
  have hw : ∀ w, nF ((A.submatrix id e).map (cW w)) = nF (A.map (cW w)) := fun w => by
    haveI := ultra w
    rw [← Matrix.submatrix_map]
    exact (hF (w.adicCompletion E) (Fin n)).reindex κ κ' e (A.map (cW w))
  simp only [degG, hfr, ← hA, hv, hw]

theorem degG_mul (mF : MulF) (mI : MulI) (lg : LogAbsBasic) (fs : FinSupp) {κ : Type} [Fintype κ] [DecidableEq κ]
    (x : GA E n) (P : Matrix (Fin n) κ E) (hP : LinearIndependent E Pᵀ) (s : Matrix κ κ E) (hs : s.det ≠ 0) :
    degG x (P * s) = degG x P := by
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hfr : (x⁻¹ : GA E n).val * (P * s).map (algebraMap E (Ad E)) = A * s.map (algebraMap E (Ad E)) := by
    rw [hA, Matrix.map_mul, Matrix.mul_assoc]
  obtain ⟨Y₀, hY₀⟩ := exists_left_inv P hP
  have hYA : (Y₀.map (algebraMap E (Ad E)) * x.val) * A = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hY₀, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2, h3⟩ := (lg E).1, (lg E).2.1, (lg E).2.2
  obtain ⟨f1, f2, f3⟩ := fs E (Fin n) κ A _ hYA
  have hu : IsUnit (algebraMap E (Ad E) s.det) := (IsUnit.mk0 _ hs).map _
  have hdet : ∀ {R : Type} [CommRing R] (f : Ad E →+* R),
      ((s.map (algebraMap E (Ad E))).map f).det = f (algebraMap E (Ad E) s.det) := fun f => by
    rw [RingHom.map_det, RingHom.map_det]
    rfl
  have hv : ∀ v, Real.log (nI ((A * s.map (algebraMap E (Ad E))).map (cV v))) =
      Real.log (nI (A.map (cV v))) + Real.log (‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2) := fun v => by
    have hne : ‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero)
    rw [Matrix.map_mul, (mI (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f1 v) hne]
  have hw : ∀ w, Real.log (nF ((A * s.map (algebraMap E (Ad E))).map (cW w))) =
      Real.log (nF (A.map (cW w))) + Real.log ‖cW w (algebraMap E (Ad E) s.det)‖ := fun w => by
    haveI := ultra w
    have hne : ‖cW w (algebraMap E (Ad E) s.det)‖ ≠ 0 := norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero
    rw [Matrix.map_mul, (mF _ (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f2 w) hne]
  have hsupp : (Function.support fun w => Real.log (nF (A.map (cW w)))).Finite :=
    f3.subset fun w hw' h => hw' (by simp [h])
  have hprod := h3 s.det hs
  simp only [degG, hfr, ← hA, hv, hw]
  rw [Finset.sum_add_distrib, finsum_add_distrib hsupp (h1 _ hu)]
  unfold logAbs at hprod
  linarith

theorem degBasisG_of : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  intro hF hI mF mI lg fs E _ _ _ n κ _ _ x M hM
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span E (Set.range Mᵀ) := ⟨_, rfl⟩
  rw [← hW]
  have hcard : Module.finrank E W = Fintype.card κ := by
    rw [hW]
    exact finrank_span_eq_card hM
  have hsub : ∀ k, (fun i => M i k) ∈ W := fun k => by
    rw [hW]
    exact Submodule.subset_span ⟨k, rfl⟩
  let e : Fin (Module.finrank E W) ≃ κ := (Fintype.equivFinOfCardEq hcard.symm).symm
  have hcol : ∀ j, (fun i => M i (e j)) ∈ W := fun j => hsub (e j)
  let b := Module.finBasis E W
  let s : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E :=
    Matrix.of fun i j => b.repr ⟨fun i' => M i' (e j), hcol j⟩ i
  have hfac : M.submatrix id e = basisMat W * s := by
    ext i j
    have h := congrArg (fun y : W => (y : Fin n → E) i) (b.sum_repr ⟨fun i' => M i' (e j), hcol j⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simp only [Matrix.mul_apply, basisMat, Matrix.of_apply, Matrix.submatrix_apply, id, s]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hlin : LinearIndependent E (M.submatrix id e)ᵀ := hM.comp e e.injective
  have hs : s.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M.submatrix id e *ᵥ v = 0 := by
      rw [hfac, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.mulVec_eq_sum] at h1
    simp only [op_smul_eq_smul] at h1
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.1 hlin v h1 i)
  have hP : LinearIndependent E (basisMat W)ᵀ :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  calc degG x M = degG x (M.submatrix id e) := (degG_reindex hF hI e x M).symm
    _ = degG x (basisMat W * s) := by rw [hfac]
    _ = degG x (basisMat W) := degG_mul mF mI lg fs x _ hP s hs
    _ = deg x W := rfl

end GlobalTheory.CompanionTheory.DegBasisGen

end
