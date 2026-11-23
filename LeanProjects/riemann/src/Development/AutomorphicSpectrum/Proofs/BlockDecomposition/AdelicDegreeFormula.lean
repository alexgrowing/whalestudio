import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegAdelicProof

theorem exists_leftInv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ L : Matrix (Fin k) (Fin n) K, L * M = 1 := by
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' M) = 1 := by
    rw [Matrix.toLin'_apply', hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ}

theorem frame_mul (x t : GA E n) (s : GA E k) (M : Matrix (Fin n) (Fin k) E)
    (h : t.val * M.map (algebraMap E (Ad E)) = M.map (algebraMap E (Ad E)) * s.val) :
    frame (t * x) M = frame x M * (s⁻¹ : GA E k).val := by
  have h' : (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) =
      M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
    calc (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))
        = (t⁻¹ : GA E n).val * (M.map (algebraMap E (Ad E)) * (s.val * (s⁻¹ : GA E k).val)) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (t⁻¹ : GA E n).val * (t.val * M.map (algebraMap E (Ad E))) * (s⁻¹ : GA E k).val := by
          rw [h, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, h', Matrix.mul_assoc]

theorem lognInf_mul (hI : MulI) (v : InfinitePlace E) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nI (A.map (cV v)) ≠ 0) (hS : IsUnit S.det) :
    lognInf v (A * S) = lognInf v A + Real.log (‖cV v S.det‖ ^ 2) := by
  have hd : (S.map (cV v)).det = cV v S.det := (RingHom.map_det (cV v) S).symm
  have h0 : cV v S.det ≠ 0 := (hS.map (cV v)).ne_zero
  change Real.log (nI ((A * S).map (cV v))) = Real.log (nI (A.map (cV v))) + _
  rw [Matrix.map_mul, (hI (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (pow_ne_zero 2 (norm_ne_zero_iff.2 h0))]

theorem lognFin_mul (hF : MulF) (w : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nF (A.map (cW w)) ≠ 0) (hS : IsUnit S.det) :
    lognFin w (A * S) = lognFin w A + Real.log ‖cW w S.det‖ := by
  have hd : (S.map (cW w)).det = cW w S.det := (RingHom.map_det (cW w) S).symm
  have h0 : cW w S.det ≠ 0 := (hS.map (cW w)).ne_zero
  change Real.log (nF ((A * S).map (cW w))) = Real.log (nF (A.map (cW w))) + _
  rw [Matrix.map_mul, (hF _ (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (norm_ne_zero_iff.2 h0)]

theorem logAbs_inv (hL : LogAbsBasic) (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') (h : u * u' = 1) :
    logAbs u = -logAbs u' := by
  have h1 := (hL E).2.1 u u' hu hu'
  have h2 := (hL E).2.2 1 one_ne_zero
  rw [map_one] at h2
  rw [h, h2] at h1
  linarith

theorem frame_leftInv (x : GA E n) (M : Matrix (Fin n) (Fin k) E) (L : Matrix (Fin k) (Fin n) E)
    (hLM : L * M = 1) :
    (L.map (algebraMap E (Ad E)) * x.val) * frame x M = 1 := by
  unfold frame
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul,
    ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem degAdelic_of (hF : MulF) (hI : MulI) (hL : LogAbsBasic) (hS : FinSupp) : DegAdelic := by
  intro E _ _ _ n k x t s M hM h
  obtain ⟨L, hLM⟩ := exists_leftInv M hM
  obtain ⟨h1, h2, h3⟩ := hS E (Fin n) (Fin k) (frame x M) _ (frame_leftInv x M L hLM)
  have hδ : IsUnit (s⁻¹ : GA E k).val.det := Matrix.isUnits_det_units _
  have hs : IsUnit s.val.det := Matrix.isUnits_det_units _
  have hmul : (s⁻¹ : GA E k).val.det * s.val.det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hinv := logAbs_inv hL _ _ hδ hs hmul
  have hfin₁ : (Function.support fun w => lognFin w (frame x M)).Finite := by
    refine h3.subset fun w hw hw1 => hw ?_
    change Real.log (nF ((frame x M).map (cW w))) = 0
    rw [show nF ((frame x M).map (cW w)) = 1 from hw1, Real.log_one]
  have hfin₂ := (hL E).1 _ hδ
  rw [degM, degM, frame_mul x t s M h]
  have e₁ : ∀ v, lognInf v (frame x M * (s⁻¹ : GA E k).val) =
      lognInf v (frame x M) + Real.log (‖cV v (s⁻¹ : GA E k).val.det‖ ^ 2) :=
    fun v => lognInf_mul hI v _ _ (h1 v) hδ
  have e₂ : ∀ w, lognFin w (frame x M * (s⁻¹ : GA E k).val) =
      lognFin w (frame x M) + Real.log ‖cW w (s⁻¹ : GA E k).val.det‖ :=
    fun w => lognFin_mul hF w _ _ (h2 w) hδ
  simp_rw [e₁, e₂]
  rw [Finset.sum_add_distrib, finsum_add_distrib hfin₁ hfin₂]
  unfold logAbs at hinv ⊢
  linarith

end GlobalTheory.CompanionTheory.DegAdelicProof

end
