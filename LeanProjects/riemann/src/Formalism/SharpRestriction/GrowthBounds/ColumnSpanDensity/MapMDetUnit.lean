import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MemColSpanIff

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Tr

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

theorem mapM_det_unit (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) :
    IsUnit (mapM (Qq := R.Qq) V).det := by
  show IsUnit ((algebraMap R.W R.Qq).mapMatrix V).det
  rw [← RingHom.map_det]
  exact hV.map _

theorem colSpan_mapM (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) :
    colSpan R.W (mapM (Qq := R.Qq) V) = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) := by
  have h := colSpan_unimod (1 : Matrix (Fin k) (Fin k) R.Qq) V hV
  rwa [one_mul] at h

private theorem colSpan_map_mulVecLin_eq_colSpan_mul (M g : Matrix (Fin k) (Fin k) R.Qq) :
    (colSpan R.W g).map ((Matrix.mulVecLin M).restrictScalars R.W) = colSpan R.W (M * g) := by
  rw [colSpan, colSpan, Submodule.map_span, ← Set.range_comp]
  congr 1

private theorem isEdge_map_mulVecLin_of_isUnit_det (M : Matrix (Fin k) (Fin k) R.Qq) (hM : IsUnit M.det) (e : Edge R.W R.Qq k)
    (he : IsEdge p n' 1 e) :
    IsEdge p n' 1 (⟨e.src.map ((Matrix.mulVecLin M).restrictScalars R.W),
      e.tgt.map ((Matrix.mulVecLin M).restrictScalars R.W)⟩ : Edge R.W R.Qq k) := by
  obtain ⟨⟨g1, hg1, hs⟩, ⟨g2, hg2, ht⟩, hle, hpm, hcard⟩ := he
  set f := (Matrix.mulVecLin M).restrictScalars R.W with hfdef
  have hfinj : Function.Injective f := by
    have h := (Matrix.mulVec_injective_iff_isUnit (A := M)).2 ((Matrix.isUnit_iff_isUnit_det M).2 hM)
    exact h
  refine ⟨⟨M * g1, by rw [Matrix.det_mul]; exact hM.mul hg1, by rw [hs]; exact colSpan_map_mulVecLin_eq_colSpan_mul R M g1⟩,
    ⟨M * g2, by rw [Matrix.det_mul]; exact hM.mul hg2, by rw [ht]; exact colSpan_map_mulVecLin_eq_colSpan_mul R M g2⟩,
    Submodule.map_mono hle, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(p : R.W) • y, hpm y hy, map_smul f _ y⟩
  · rw [← hcard]
    let e0 := Submodule.equivMapOfInjective f hfinj e.tgt
    have hPQ : (Submodule.comap e.tgt.subtype e.src).map (e0 : e.tgt →ₗ[R.W] _) =
        Submodule.comap (e.tgt.map f).subtype (e.src.map f) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.1, hy, rfl⟩
      · intro hz
        obtain ⟨y, hys, hyz⟩ := hz
        refine ⟨⟨y, hle hys⟩, hys, Subtype.ext ?_⟩
        exact hyz
    exact (Nat.card_congr (Submodule.Quotient.equiv _ _ e0 hPQ).toEquiv).symm

private theorem natCast_p_ne_zero_Qq (j : Fin k) : (p : R.Qq) ≠ 0 := by
  intro h0
  obtain ⟨g, hg, hgeq⟩ := (baseEdge R j).1
  have hker : colSpan R.W (dj j (p : R.Qq)) ≤
      LinearMap.ker ((LinearMap.proj j : (Fin k → R.Qq) →ₗ[R.Qq] R.Qq).restrictScalars R.W) := by
    rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    simp [dj, Matrix.diagonal_apply, h0]
  obtain ⟨c, hc⟩ : ∃ c, g j c ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hg.ne_zero (Matrix.det_eq_zero_of_row_eq_zero j hall)
  have hmem : (fun i => g i c) ∈ colSpan R.W (dj j (p : R.Qq)) := by
    have hgeq' : colSpan R.W (dj j (p : R.Qq)) = colSpan R.W g := hgeq
    rw [hgeq']
    exact Submodule.subset_span ⟨c, rfl⟩
  have h1 := hker hmem
  simp at h1
  exact hc h1

theorem edgeT (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (mapM V * dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  have h := isEdge_map_mulVecLin_of_isUnit_det R (mapM V) (mapM_det_unit R V hV) _ (baseEdge R j)
  simp only [colSpan_map_mulVecLin_eq_colSpan_mul, mul_one, colSpan_mapM R V hV] at h
  exact h

theorem edgeS (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq), colSpan R.W (mapM V * dj j (p : R.Qq)⁻¹)⟩ :
      Edge R.W R.Qq k) := by
  have hp := natCast_p_ne_zero_Qq R j
  have hdet : IsUnit (mapM V * dj j (p : R.Qq)⁻¹).det := by
    rw [Matrix.det_mul, dj_det]
    exact (mapM_det_unit R V hV).mul (isUnit_iff_ne_zero.2 (inv_ne_zero hp))
  have h := isEdge_map_mulVecLin_of_isUnit_det R _ hdet _ (baseEdge R j)
  simp only [colSpan_map_mulVecLin_eq_colSpan_mul, mul_one, mul_assoc, dj_mul, inv_mul_cancel₀ hp, dj_one,
    colSpan_mapM R V hV] at h
  exact h

theorem transport (L : Submodule R.W (Fin k → R.Qq)) (hL : IsLattice R.W L) {Ne : ℕ}
    (es : Fin Ne → Edge R.W R.Qq k) (hinj : Function.Injective es) (hes : ∀ i, IsEdge p n' 1 (es i)) :
    ∃ es' : Fin Ne → Edge R.W R.Qq k, Function.Injective es' ∧ (∀ i, IsEdge p n' 1 (es' i)) ∧
      (∀ i, (es i).tgt = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) → (es' i).tgt = L) ∧
      (∀ i, (es i).src = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) → (es' i).src = L) := by
  obtain ⟨g, hg, rfl⟩ := hL
  set f := (Matrix.mulVecLin g).restrictScalars R.W with hfdef
  have hfinj : Function.Injective f :=
    (Matrix.mulVec_injective_iff_isUnit (A := g)).2 ((Matrix.isUnit_iff_isUnit_det g).2 hg)
  refine ⟨fun i => ⟨(es i).src.map f, (es i).tgt.map f⟩, ?_, fun i => isEdge_map_mulVecLin_of_isUnit_det R g hg _ (hes i), ?_, ?_⟩
  · intro i i' h
    apply hinj
    have h1 : (es i).src.map f = (es i').src.map f := congrArg Edge.src h
    have h2 : (es i).tgt.map f = (es i').tgt.map f := congrArg Edge.tgt h
    have e1 := Submodule.map_injective_of_injective hfinj h1
    have e2 := Submodule.map_injective_of_injective hfinj h2
    cases hi : es i
    cases hi' : es i'
    rw [hi, hi'] at e1 e2
    simp only at e1 e2
    rw [e1, e2]
  · intro i hi
    show (es i).tgt.map f = _
    rw [hi, colSpan_map_mulVecLin_eq_colSpan_mul, mul_one]
  · intro i hi
    show (es i).src.map f = _
    rw [hi, colSpan_map_mulVecLin_eq_colSpan_mul, mul_one]

end Tr

end Formalism.MainNotions.flipOneThree.Pf

end
