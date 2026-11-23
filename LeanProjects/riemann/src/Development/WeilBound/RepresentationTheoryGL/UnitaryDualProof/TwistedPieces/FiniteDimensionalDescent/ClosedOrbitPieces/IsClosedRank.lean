import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop

noncomputable section

open Matrix Polynomial Topology

set_option linter.unusedSectionVars false

namespace PositivityTheory.RgUd.TP.Desc.Piece.PTop

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem rank_eq_near {e0 : Matrix (Fin N) (Fin N) k} (h0 : IsIdempotentElem e0) :
    ∃ U ∈ 𝓝 e0, ∀ e ∈ U, IsIdempotentElem e → e.rank = e0.rank := by
  refine ⟨{e | (e * e0 + (1 - e) * (1 - e0)).det ≠ 0}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact isOpen_ne_fun (Continuous.matrix_det ((continuous_id.mul continuous_const).add
        ((continuous_const.sub continuous_id).mul continuous_const))) continuous_const
    · show (e0 * e0 + (1 - e0) * (1 - e0)).det ≠ 0
      have h1 : (1 - e0) * (1 - e0) = 1 - e0 := h0.one_sub.eq
      rw [h0.eq, h1, add_sub_cancel, det_one]
      exact one_ne_zero
  · intro e he hide
    have hu : IsUnit (e * e0 + (1 - e) * (1 - e0)).det := isUnit_iff_ne_zero.2 he
    have key : e * (e * e0 + (1 - e) * (1 - e0)) = (e * e0 + (1 - e) * (1 - e0)) * e0 := by
      have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hide.eq, sub_self]
      have h2 : (1 - e0) * e0 = 0 := by rw [sub_mul, one_mul, h0.eq, sub_self]
      rw [mul_add, ← mul_assoc, ← mul_assoc, hide.eq, h1, zero_mul, add_zero, add_mul,
        mul_assoc (1 - e), h2, mul_zero, add_zero, mul_assoc, h0.eq]
    rw [← Matrix.rank_mul_eq_left_of_isUnit_det _ e hu, key, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]

theorem isClosed_rank {X : Type} [TopologicalSpace X] {F : Set X} (hF : IsClosed F)
    {f : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hi : ∀ x ∈ F, IsIdempotentElem (f x)) (r : ℕ) :
    IsClosed {x | x ∈ F ∧ (f x).rank = r} := by
  apply isClosed_of_closure_subset
  intro x hx
  have hxF : x ∈ F := hF.closure_subset (closure_mono (fun y hy => hy.1) hx)
  obtain ⟨U, hU, hUe⟩ := rank_eq_near (hi x hxF)
  obtain ⟨y, hyU, hyF, hyr⟩ := mem_closure_iff_nhds.1 hx _ (hf.continuousAt.preimage_mem_nhds hU)
  exact ⟨hxF, (hUe _ hyU (hi y hyF)).symm.trans hyr⟩

theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) : IsClosed (Bz Z) := by
  have h : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin N) (Fin N) k | a * x = x * a} := by
    ext x
    simp [Bz]
  rw [h]
  exact isClosed_biInter (fun a _ => isClosed_eq (continuous_const.mul continuous_id)
    (continuous_id.mul continuous_const))

theorem continuous_pe {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k) : Continuous (pe c) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_pow _)

theorem pe_conj {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k)
    (hc : ∀ l, c l ∈ Z) {g : GL (Fin N) k} (hg : g ∈ Gz Z) (x : Matrix (Fin N) (Fin N) k) :
    pe c (g.val * x * g⁻¹.val) = g.val * pe c x * g⁻¹.val := by
  unfold pe
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Units.conj_pow]
  simp only [mul_assoc]
  rw [← mul_assoc (c l), hg _ (hc l), mul_assoc]

theorem aeval_conj (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (χ : k[X]) :
    aeval (g.val * x * g⁻¹.val) χ = g.val * aeval x χ * g⁻¹.val := by
  induction χ using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, hp, hr, mul_add, add_mul]
  | monomial n a =>
    simp only [aeval_monomial, Units.conj_pow, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

theorem rank_conj (g : GL (Fin N) k) (e : Matrix (Fin N) (Fin N) k) : (g.val * e * g⁻¹.val).rank = e.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (g⁻¹).isUnit),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]

variable (k) in
theorem pieceTop : PieceTop k := by
  intro N q Z hZ χ D τ
  have hF : IsClosed {x : Matrix (Fin N) (Fin N) k | x ∈ Bz Z ∧ aeval x χ = 0} :=
    (isClosed_Bz Z).inter (isClosed_eq (Polynomial.continuous_aeval χ) continuous_const)
  have hft : ∀ t : Fin D.m, Continuous fun x : Matrix (Fin N) (Fin N) k =>
      ∑ j : Fin D.r, D.κ t j • pe (D.a j) x :=
    fun t => continuous_finset_sum _
      (fun j _ => (continuous_const_smul (D.κ t j)).comp (continuous_pe (D.a j)))
  have hidem : ∀ t : Fin D.m, ∀ x ∈ {x : Matrix (Fin N) (Fin N) k | x ∈ Bz Z ∧ aeval x χ = 0},
      IsIdempotentElem (∑ j : Fin D.r, D.κ t j • pe (D.a j) x) :=
    fun t x hx => (D.spec x hx.1 hx.2).2.2.2.2.2.2.2.2.1 t
  refine ⟨?_, ?_, ?_⟩
  · have h : piece D τ = {x | x ∈ Bz Z ∧ aeval x χ = 0} ∩ ⋂ t, {x | x ∈ {x : Matrix (Fin N) (Fin N) k |
        x ∈ Bz Z ∧ aeval x χ = 0} ∧ (∑ j : Fin D.r, D.κ t j • pe (D.a j) x).rank = τ t} := by
      ext x
      simp only [piece, typ, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, funext_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun t => ⟨⟨h1, h2⟩, h3 t⟩⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, fun t => (h3 t).2⟩
    rw [h]
    exact hF.inter (isClosed_iInter fun t => isClosed_rank hF (hft t) (hidem t) (τ t))
  · rintro g hg x ⟨hxB, hxa, hxt⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have hga : a * g.val = g.val * a := hg a ha
      have hgi : a * (g⁻¹).val = (g⁻¹).val * a := by
        calc a * (g⁻¹).val = (g⁻¹).val * (g.val * a) * (g⁻¹).val := by rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = (g⁻¹).val * (a * g.val) * (g⁻¹).val := by rw [hga]
          _ = (g⁻¹).val * a := by rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      calc a * (g.val * x * (g⁻¹).val) = g.val * (a * x) * (g⁻¹).val := by simp only [← mul_assoc, hga]
        _ = g.val * (x * a) * (g⁻¹).val := by rw [hxB a ha]
        _ = g.val * x * (g⁻¹).val * a := by simp only [mul_assoc, hgi]
    · rw [aeval_conj, hxa, mul_zero, zero_mul]
    · rw [← hxt]
      funext t
      simp only [typ]
      have h : ∑ j, D.κ t j • pe (D.a j) (g.val * x * (g⁻¹).val) = g.val * (∑ j, D.κ t j • pe (D.a j) x) * (g⁻¹).val := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [pe_conj (D.a j) (D.ha j) hg, mul_smul_comm, smul_mul_assoc]
      rw [h, rank_conj]
  · intro x hx
    obtain ⟨hxB, hxa, -⟩ := hx
    have sp := D.spec x hxB hxa
    simp only at sp
    obtain ⟨hmul, hone, hcomm, -, -, hred, -⟩ := sp
    have hspan_mul : ∀ a b, a ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) →
        b ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) →
        a * b ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) := by
      intro a b ha hb
      have h1 := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨j', rfl⟩, rfl⟩
      show pe (D.a j) x * pe (D.a j') x ∈ _
      rw [hmul j j']
      exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩))
    have h1mem : (1 : Matrix (Fin N) (Fin N) k) ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) := by
      rw [← hone]
      exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    have hle : Sx D x ≤ (Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x)).toSubalgebra
        h1mem hspan_mul := by
      apply Algebra.adjoin_le
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
    refine ⟨?_, ⟨fun y hy => ?_⟩⟩
    · intro a ha b hb
      have ha' : a ∈ Algebra.adjoin k (Set.range fun j : Fin D.r => pe (D.a j) x) := ha
      have hb' : b ∈ Algebra.adjoin k (Set.range fun j : Fin D.r => pe (D.a j) x) := hb
      have hgen : ∀ u ∈ Set.range (fun j : Fin D.r => pe (D.a j) x), Commute u b := by
        intro u hu
        refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb' ?_
        rintro _ ⟨j', rfl⟩
        obtain ⟨j, rfl⟩ := hu
        exact hcomm j j'
      exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha' (fun u hu => (hgen u hu).symm)).symm.eq
    · apply Subtype.ext
      exact hred _ (hle y.2) (hy.map (Sx D x).val)

end PositivityTheory.RgUd.TP.Desc.Piece.PTop
