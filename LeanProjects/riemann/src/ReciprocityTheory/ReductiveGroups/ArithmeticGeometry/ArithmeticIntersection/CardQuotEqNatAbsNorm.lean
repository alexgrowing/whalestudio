import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.IndexSt

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

theorem card_quot_eq_natAbs_norm {S : Type*} [CommRing S] [IsDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (f : S) (hf : f ≠ 0) :
    Nat.card (S ⧸ Ideal.span {f}) = (Algebra.norm ℤ f).natAbs := by
  classical
  let N : Submodule ℤ S := (Ideal.span {f}).restrictScalars ℤ
  have hmem : ∀ x : S, f * x ∈ N := fun x => Ideal.mul_mem_right x _ (Ideal.subset_span rfl)
  let g : S →+ N :=
    { toFun := fun x => ⟨f * x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hbij : Function.Bijective g := by
    constructor
    · intro x y hxy
      have h1 : f * x = f * y := congrArg Subtype.val hxy
      exact mul_left_cancel₀ hf h1
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨a, by ext; simp [g, mul_comm]⟩
  let e : S ≃+ N := AddEquiv.ofBijective g hbij
  have h := Submodule.natAbs_det_equiv N e
  have hlin : N.subtype ∘ₗ (e : S →+ N).toIntLinearMap = Algebra.lmul ℤ S f := by
    ext x
    rfl
  rw [hlin, ← Algebra.norm_apply] at h
  rw [h]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {f})).toEquiv.symm

theorem norm_int_eq_norm_rat {K : Type*} [Field K] [NumberField K] (O : Subring K)
    [Module.Free ℤ O] [Module.Finite ℤ O] (h : Module.finrank ℤ O = Module.finrank ℚ K)
    (f : O) : ((Algebra.norm ℤ f : ℤ) : ℚ) = Algebra.norm ℚ (f : K) := by
  classical
  let b := Module.Free.chooseBasis ℤ O
  have hli : LinearIndependent ℚ (fun i => ((b i : O) : K)) := by
    have h1 : LinearIndependent ℤ (fun i => ((b i : O) : K)) :=
      b.linearIndependent.map' (O.subtype.toIntAlgHom.toLinearMap)
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℚ K := by
    rw [← h, Module.finrank_eq_card_chooseBasisIndex]
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ O) := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact Module.finrank_pos
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb' : ∀ i, b' i = ((b i : O) : K) := fun i => by
    simp only [b', coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [Algebra.norm_eq_matrix_det b f, Algebra.norm_eq_matrix_det b' (f : K)]
  have hm := RingHom.map_det (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f)
  rw [show ((Algebra.leftMulMatrix b f).det : ℚ) = (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f).det from rfl, hm]
  congr 1
  ext i j
  have hx : (f : K) * b' j = ∑ k, ((b.repr (f * b j) k : ℤ) : ℚ) • b' k := by
    have e1 := congrArg (O.subtype.toIntAlgHom.toLinearMap) (b.sum_repr (f * b j))
    rw [map_sum] at e1
    simp only [map_zsmul] at e1
    simp only [hb', Int.cast_smul_eq_zsmul]
    exact e1.symm
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, eq_intCast]
  rw [hx, b'.repr_sum_self]

theorem abs_norm_eq_prod {K : Type*} [Field K] [NumberField K] (x : K) :
    |(Algebra.norm ℚ x : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast, Complex.norm_ratCast] at h2
  exact h2.trans (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)).symm

theorem index_thm : IndexStatement := by
  intro K _ _ O hfree hfin hrank f hf
  haveI := hfree
  haveI := hfin
  have hc := card_quot_eq_natAbs_norm f hf
  have hn := norm_int_eq_norm_rat O hrank f
  have hprod := abs_norm_eq_prod (f : K)
  have h1 : (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| := by
    rw [hc, ← hn]
    simp [Nat.cast_natAbs, Int.cast_abs, Rat.cast_intCast]
  refine ⟨h1, ?_⟩
  rw [h1, hprod, Real.log_prod (fun σ _ => ?_)]
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (fun h0 => hf (Subtype.ext h0)))

end ReciprocityTheory.ChartRestriction.G.AI
