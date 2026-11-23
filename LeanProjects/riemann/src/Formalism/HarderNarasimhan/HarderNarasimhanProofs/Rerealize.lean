import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean

open Module NumberField

noncomputable section

namespace Formalism.HN

namespace Rerealization

section Lat

variable {G E F : Type*} [AddCommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem eq_of_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) {x y : G}
    (h : α x = α y) : β x = β y := by
  have h0 : ‖β (x - y)‖ = 0 := by rw [hn, map_sub, h, sub_self, norm_zero]
  rw [norm_eq_zero, map_sub, sub_eq_zero] at h0
  exact h0

theorem inner_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (x y : G) :
    inner ℝ (β x) (β y) = inner ℝ (α x) (α y) := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, ← map_add, hn, hn, hn]

private theorem det_gram_basis_eq' {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ F)
    (C C' : Module.Basis ι ℤ L) :
    (Matrix.gram ℝ (fun i => ((C' i : L) : F))).det = (Matrix.gram ℝ (fun i => ((C i : L) : F))).det := by
  set P : Matrix ι ι ℝ := (C.toMatrix C').map (Int.cast : ℤ → ℝ) with hP
  have hC' : ∀ i, ((C' i : L) : F) = ∑ k, P k i • ((C k : L) : F) := by
    intro i
    have e := congrArg (fun w : L => (w : F)) (C.sum_repr (C' i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, Matrix.map_apply, Module.Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ (fun i => ((C' i : L) : F)) =
      P.transpose * Matrix.gram ℝ (fun i => ((C i : L) : F)) * P := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hC', sum_inner,
      inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_;
          rw [real_inner_comm]; ring)
  have hdet : (C.toMatrix C').det * (C'.toMatrix C).det = 1 := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hPd : P.det = ((C.toMatrix C').det : ℝ) := by
    rw [hP]
    first
      | exact (Int.cast_det _).symm
      | exact ((Int.castRingHom ℝ).map_det _).symm
  have hsq : P.det ^ 2 = 1 := by
    rw [hPd]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;> simp [h]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show ∀ a b : ℝ, a * b * a = a ^ 2 * b from fun a b => by ring, hsq, one_mul]

private theorem covol_eq_of_inner_preserving_equiv (L1 : Submodule ℤ E) (L2 : Submodule ℤ F) [DiscreteTopology L1]
    [DiscreteTopology L2] (τ : L1 ≃ₗ[ℤ] L2)
    (hτ : ∀ x y : L1, inner ℝ ((τ x : L2) : F) ((τ y : L2) : F) = inner ℝ (x : E) (y : E)) :
    Formalism.F.covol L1 = Formalism.F.covol L2 := by
  have hr : Module.finrank ℤ L1 = Module.finrank ℤ L2 := τ.finrank_eq
  unfold Formalism.F.covol
  rw [dif_pos ‹DiscreteTopology L1›, dif_pos ‹DiscreteTopology L2›]
  congr 1
  let B : Module.Basis (Fin (Module.finrank ℤ L2)) ℤ L2 :=
    ((Module.finBasis ℤ L1).map τ).reindex (finCongr hr)
  have h1 : Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L1 i : L1) : E)) =
      (Matrix.gram ℝ (fun i => ((B i : L2) : F))).submatrix (finCongr hr) (finCongr hr) := by
    ext i j
    simp [B, Matrix.gram, hτ]
  rw [h1, Matrix.det_submatrix_equiv_self, det_gram_basis_eq' L2 (Module.finBasis ℤ L2) B]

theorem covol_rk_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G)
    (hα : DiscreteTopology (H.map α).toIntSubmodule)
    (hβ : DiscreteTopology (H.map β).toIntSubmodule) :
    Formalism.F.covol (H.map β).toIntSubmodule = Formalism.F.covol (H.map α).toIntSubmodule ∧
      Formalism.F.rk (H.map β).toIntSubmodule = Formalism.F.rk (H.map α).toIntSubmodule := by
  haveI := hα
  haveI := hβ
  have ex : ∀ y : (H.map α).toIntSubmodule, ∃ g ∈ H, α g = (y : E) := fun y =>
    AddSubgroup.mem_map.mp y.2
  let τf : (H.map α).toIntSubmodule →+ (H.map β).toIntSubmodule :=
    { toFun := fun y => ⟨β (ex y).choose, AddSubgroup.mem_map.mpr ⟨_, (ex y).choose_spec.1, rfl⟩⟩
      map_zero' := by
        apply Subtype.ext
        show β (ex 0).choose = 0
        rw [← map_zero β]
        exact eq_of_eq α β hn (by simp [(ex 0).choose_spec.2])
      map_add' := fun y z => by
        apply Subtype.ext
        show β (ex (y + z)).choose = β (ex y).choose + β (ex z).choose
        rw [← map_add]
        exact eq_of_eq α β hn
          (by simp [(ex (y + z)).choose_spec.2, (ex y).choose_spec.2, (ex z).choose_spec.2]) }
  have hval : ∀ (y : (H.map α).toIntSubmodule) (g : G), α g = (y : E) → ((τf y : (H.map β).toIntSubmodule) : F) = β g := fun y g hg =>
    eq_of_eq α β hn (((ex y).choose_spec.2).trans hg.symm)
  have hnorm : ∀ y, ‖((τf y : (H.map β).toIntSubmodule) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [hval y _ (ex y).choose_spec.2, hn, (ex y).choose_spec.2]
  have hinj : Function.Injective τf := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have : ‖(y : E)‖ = 0 := by rw [← hnorm, hy]; simp
    exact Subtype.ext (norm_eq_zero.mp this)
  have hsurj : Function.Surjective τf := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨⟨α g, AddSubgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩, Subtype.ext (hval _ g rfl)⟩
  let τ : (H.map α).toIntSubmodule ≃ₗ[ℤ] (H.map β).toIntSubmodule :=
    (AddEquiv.ofBijective τf ⟨hinj, hsurj⟩).toIntLinearEquiv
  have hτ : ∀ x y : (H.map α).toIntSubmodule, inner ℝ ((τ x : (H.map β).toIntSubmodule) : F)
      ((τ y : (H.map β).toIntSubmodule) : F) = inner ℝ (x : E) (y : E) := by
    intro x y
    exact inner_eq ((H.map α).toIntSubmodule.subtype.toAddMonoidHom)
      (((H.map β).toIntSubmodule.subtype.toAddMonoidHom).comp τf) hnorm x y
  exact ⟨(covol_eq_of_inner_preserving_equiv _ _ τ hτ).symm, τ.finrank_eq.symm⟩

end Lat

section Abs

variable {R V E E₂ : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

theorem covol_eq_exp {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] (L : Submodule ℤ E') (h : DiscreteTopology L) :
    Formalism.F.covol L = Real.exp (- Formalism.F.deg L) := by
  haveI := h
  rw [Formalism.F.deg, neg_neg, Real.exp_log (Formalism.F.covol_pos L)]

theorem transfer (ρ : V →+ E) (ρ₂ : V →+ E₂) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (L : Submodule R V)
    (hL : IsLat ρ L) (hL₂ : IsLat ρ₂ L) :
    (∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N) ∧
    (∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N) ∧
    (∀ N : Submodule R V, IsSat ρ L N →
      Formalism.F.covol (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.covol (Formalism.F.quot (zl ρ L) (zl ρ N)) ∧
      Formalism.F.slope (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
        Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N))) := by
  obtain ⟨a1, -, -, -, -, -, -, a8⟩ := saturation_basic_properties R V E ρ L hL
  obtain ⟨b1, -, -, -, -, -, -, b8⟩ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have T1 : ∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N := by
    intro N hN
    obtain ⟨c1, c2⟩ := covol_rk_eq ρ ρ₂ hn N.toAddSubgroup (a1 N hN).2 (b1 N hN).2
    have h1 : Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) := c1
    have h2 : rk ρ₂ N = rk ρ N := c2
    have h3 : deg ρ₂ N = deg ρ N := by
      unfold deg Formalism.F.deg
      rw [h1]
    refine ⟨h1, h2, h3, ?_⟩
    unfold slope Formalism.F.slope
    exact congrArg₂ (· / ·) h3 (congrArg (fun n : ℕ => (n : ℝ)) h2)
  have T2 : ∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N := by
    intro N
    rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, h⟩
      refine ⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩
      rw [(T1 N' h2).2.1, (T1 N hNL).2.1, h3]
    · rintro ⟨hNL, h⟩
      refine ⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩
      rw [← (T1 N' h2).2.1, ← (T1 N hNL).2.1, h3]
  refine ⟨T1, T2, ?_⟩
  intro N hS
  have hS₂ := (T2 N).2 hS
  obtain ⟨q1, -, q3⟩ := a8 N hS
  obtain ⟨r1, -, r3⟩ := b8 N hS₂
  have hrk : Formalism.F.rk (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ N)) := by
    rw [q1, r1, (T1 L le_rfl).2.1, (T1 N hS.1).2.1]
  have hdeg : Formalism.F.deg (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ N)) := by
    rw [q3, r3, (T1 L le_rfl).2.2.1, (T1 N hS.1).2.2.1]
  refine ⟨?_, ?_⟩
  · rw [covol_eq_exp _ (Formalism.F.degQuot E₂ _ _ hL₂.2 hS₂.2).1,
      covol_eq_exp _ (Formalism.F.degQuot E _ _ hL.2 hS.2).1, hdeg]
  · unfold Formalism.F.slope
    rw [hdeg, hrk]

end Abs

end Rerealization

open Rerealization in
theorem lattice_rerealization : Rerealize := by
  intro K V ι V'' κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b'' X'' ψ hX hX'' hψ hnorm A hA
  have hψ' : Function.Injective (ψ.restrictScalars (𝓞 K)) := hψ
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : V →+ EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2),
      ρ₂ = (Formalism.HermitianLatticesTheory.realize b'' X'').comp ψ.toAddMonoidHom := ⟨_, rfl⟩
  have hρ₂x : ∀ x, ρ₂ x = Formalism.HermitianLatticesTheory.realize b'' X'' (ψ x) := fun x => by rw [hρ₂]; rfl
  have hn : ∀ x, ‖ρ₂ x‖ = ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
    intro x
    have h2 : ‖ρ₂ x‖ ^ 2 = ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 := by
      rw [hρ₂x, PlaceOperatorNorms.norm_sq_realize, PlaceOperatorNorms.norm_sq_realize]
      simp only [hnorm]
    have h3 := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3
  have hzl : ∀ N : Submodule (𝓞 K) V,
      zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) = zl ρ₂ N := by
    intro N
    ext y
    rw [satR_mem_zl, satR_mem_zl]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hρ₂x x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ψ x, ⟨x, hx, rfl⟩, (hρ₂x x).symm⟩
  have hmc : ∀ N'' : Submodule (𝓞 K) V'', N'' ≤ A.map (ψ.restrictScalars (𝓞 K)) →
      ∃ N : Submodule (𝓞 K) V, N ≤ A ∧ N.map (ψ.restrictScalars (𝓞 K)) = N'' := by
    intro N'' h
    refine ⟨N''.comap (ψ.restrictScalars (𝓞 K)), ?_, ?_⟩
    · intro x hx
      obtain ⟨x', hx', hxx'⟩ := h hx
      rw [← hψ' hxx']
      exact hx'
    · apply le_antisymm (Submodule.map_comap_le _ _)
      intro y hy
      obtain ⟨x, -, rfl⟩ := h hy
      exact ⟨x, hy, rfl⟩
  have hle : ∀ N : Submodule (𝓞 K) V,
      N.map (ψ.restrictScalars (𝓞 K)) ≤ A.map (ψ.restrictScalars (𝓞 K)) ↔ N ≤ A :=
    fun N => Submodule.map_le_map_iff_of_injective hψ' N A
  have hbot : ∀ N : Submodule (𝓞 K) V, N.map (ψ.restrictScalars (𝓞 K)) = ⊥ ↔ N = ⊥ := by
    intro N
    rw [← Submodule.map_bot (ψ.restrictScalars (𝓞 K))]
    exact (Submodule.map_injective_of_injective hψ').eq_iff
  have hneA : ∀ N : Submodule (𝓞 K) V,
      N.map (ψ.restrictScalars (𝓞 K)) = A.map (ψ.restrictScalars (𝓞 K)) ↔ N = A :=
    fun N => (Submodule.map_injective_of_injective hψ').eq_iff
  have hrkK : ∀ N : Submodule (𝓞 K) V, rkK (N.map (ψ.restrictScalars (𝓞 K))) = rkK N := by
    intro N
    unfold rkK
    have hs : Submodule.span K ((N.map (ψ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V'') : Set V'') =
        (Submodule.span K (N : Set V)).map ψ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective ψ hψ _).finrank_eq.symm
  have hlatA : IsLat (Formalism.HermitianLatticesTheory.realize b X) A := (place_lattice_structure K V ι b X hX A hA).1
  have hlatA'' : IsLat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) :=
    (place_lattice_structure K V'' κ b'' X'' hX'' _ (hA.map _)).1
  have hlatA₂ : IsLat ρ₂ A := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy h
      rw [hρ₂x, hρ₂x] at h
      exact hψ (hlatA''.1 (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hy) h)
    · rw [← hzl]
      exact hlatA''.2
  obtain ⟨T1, T2, T3⟩ := transfer (Formalism.HermitianLatticesTheory.realize b X) ρ₂ hn A hlatA hlatA₂
  have hht : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      ht b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = ht b X N := by
    intro N hN
    unfold ht
    rw [hrkK, hzl, (T1 N hN).1]
  have hsize : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      size b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = size b X N := by
    intro N hN
    unfold size
    rw [hht N hN, hrkK]
  have hslope : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      slope (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) =
        slope (Formalism.HermitianLatticesTheory.realize b X) N := by
    intro N hN
    rw [← (T1 N hN).2.2.2]
    unfold slope
    rw [hzl]
  have hsat : ∀ N : Submodule (𝓞 K) V,
      IsSat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K)))
        (N.map (ψ.restrictScalars (𝓞 K))) ↔ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N := by
    intro N
    rw [← T2 N]
    unfold IsSat
    rw [hzl, hzl, hle]
  have hqs : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N →
      Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))))
        (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))))) =
      Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) A) (zl (Formalism.HermitianLatticesTheory.realize b X) N)) := by
    intro N hN
    rw [hzl, hzl]
    exact (T3 N hN).2
  have hsizeQ : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N →
      sizeQ b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) (N.map (ψ.restrictScalars (𝓞 K))) =
        sizeQ b X A N := by
    intro N hN
    unfold sizeQ htQ
    rw [hrkK, hrkK, hzl, hzl, (T3 N hN).1]
  refine ⟨hht A le_rfl, hsize A le_rfl, hslope A le_rfl, ?_, ?_, ?_, ?_⟩
  · unfold muMax
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hN'', hne, rfl⟩
      obtain ⟨N, hN, rfl⟩ := hmc N'' hN''
      exact ⟨N, hN, fun h => hne ((hbot N).2 h), (hslope N hN).symm⟩
    · rintro ⟨N, hN, hne, rfl⟩
      exact ⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hslope N hN⟩
  · unfold muMin
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hs, hne, rfl⟩
      obtain ⟨N, -, rfl⟩ := hmc N'' hs.1
      have hs' := (hsat N).1 hs
      exact ⟨N, hs', fun h => hne ((hneA N).2 h), (hqs N hs').symm⟩
    · rintro ⟨N, hs, hne, rfl⟩
      exact ⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hqs N hs⟩
  · unfold leastSize
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hN'', hne, rfl⟩
      obtain ⟨N, hN, rfl⟩ := hmc N'' hN''
      exact ⟨N, hN, fun h => hne ((hbot N).2 h), (hsize N hN).symm⟩
    · rintro ⟨N, hN, hne, rfl⟩
      exact ⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hsize N hN⟩
  · unfold largestSize
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hs, hne, rfl⟩
      obtain ⟨N, -, rfl⟩ := hmc N'' hs.1
      have hs' := (hsat N).1 hs
      exact ⟨N, hs', fun h => hne ((hneA N).2 h), (hsizeQ N hs').symm⟩
    · rintro ⟨N, hs, hne, rfl⟩
      exact ⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hsizeQ N hs⟩

end Formalism.HN
