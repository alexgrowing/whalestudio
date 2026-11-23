import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuationStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MatrixIndex

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ b : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, b.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : F, a ∈ 𝒪[F] → algebraMap F E a ∈ L.O := fun a h =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 h
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'
    have ht : algebraMap F E t = 0 := by
      linear_combination e * h - e * h' - algebraMap F E t * hωe
    have hs : algebraMap F E s = 0 := by rw [ht] at h; simpa using h
    exact ⟨GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using hs),
      GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using ht)⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = ω := by simp [b]
  have hx : ∀ x, x = algebraMap F E (b.repr x 0) + algebraMap F E (b.repr x 1) * ω := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at this
    simpa [Algebra.smul_def] using this.symm
  refine ⟨b, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := hx x
    have h2 := congrArg L.cj h1
    simp only [map_add, map_mul, AlgEquiv.commutes] at h2
    have h3 : algebraMap F E (b.repr x 1) = (x - L.cj x) * e := by
      linear_combination -e * h1 + e * h2 - algebraMap F E (b.repr x 1) * hωe
    have h4 : algebraMap F E (b.repr x 1) ∈ L.O := by
      rw [h3]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have h5 : algebraMap F E (b.repr x 0) ∈ L.O := by
      have : algebraMap F E (b.repr x 0) = x - algebraMap F E (b.repr x 1) * ω := by
        linear_combination -h1
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem h4 hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h5
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h4
  · rw [hx x]
    exact L.O.add_mem (hint _ (h 0)) (L.O.mul_mem (hint _ (h 1)) hω)
  · rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one, map_sub, map_mul]
    have h1 := hx x
    have h2 := congrArg L.cj h1
    have h3 := hx (x * ω)
    have h4 := congrArg L.cj h3
    simp only [map_add, map_mul, AlgEquiv.commutes] at h2 h4
    generalize algebraMap F E (b.repr x 0) = a at *
    generalize algebraMap F E (b.repr x 1) = c at *
    generalize algebraMap F E (b.repr (x * ω) 0) = a' at *
    generalize algebraMap F E (b.repr (x * ω) 1) = c' at *
    have key : (ω - L.cj ω) * (a * c' - a' * c - x * L.cj x) = 0 := by
      linear_combination (-(L.cj x)) * h3 + x * h4 + (a' + c' * L.cj ω) * h1 - (a' + c' * ω) * h2
    linear_combination e * key - (a * c' - a' * c - x * L.cj x) * hωe

theorem span_eq_map (L : LocE F E) {n m : ℕ} (y : Fin m → Fin n → E) :
    (Submodule.span L.O (Set.range y)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup).map
        (Fintype.linearCombination E y).toAddMonoidHom := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
    AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left,
    LinearMap.toAddMonoidHom_coe, Fintype.linearCombination_apply, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩

theorem index_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ A : Matrix (Fin m) (Fin m) E, IsIntM L A → IsUnit A.det → 0 ≤ vE L ϖ (A.det * L.cj A.det) ∧ (Submodule.span L.O (Set.range (rmul y A))).toAddSubgroup.relIndex (Submodule.span L.O (Set.range y)).toAddSubgroup = resQ ϖ ^ (vE L ϖ (A.det * L.cj A.det)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m y hy A hA hu
  obtain ⟨b, hbO, hnorm⟩ := exists_basis L
  have := L.free
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨-, -, hv3, hv4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hdO : A.det ∈ L.O := by
    rw [Matrix.det_apply']
    exact L.O.sum_mem fun σ _ => L.O.mul_mem (intCast_mem _ _) (L.O.prod_mem fun i _ => hA _ _)
  have hN0 : Algebra.norm F A.det ≠ 0 := (hu.map (Algebra.norm F)).ne_zero
  have hNO : Algebra.norm F A.det ∈ 𝒪[F] := by
    rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hnorm]
    exact L.O.mul_mem hdO (GlobalTheory.UnramOrder.cj_mem L hdO)
  rw [← hnorm]
  have ha := (hv3 _ hN0).2 hNO
  obtain ⟨u, hu'⟩ := hv4 _ hN0
  refine ⟨ha, ?_⟩
  generalize vE L ϖ (algebraMap F E (Algebra.norm F A.det)) = a at *
  let φ : (Fin m → E) ≃ₗ[F] (Fin m → E) :=
    (Matrix.toLinearEquiv (Pi.basisFun E (Fin m)) A hu).restrictScalars F
  have hφ : ∀ v, φ v = A.mulVec v := fun v => by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  have hdet : LinearMap.det (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = Algebra.norm F A.det := by
    have : (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = (Matrix.toLin' A).restrictScalars F := by
      ext1 v; exact LinearMap.ext fun w => hφ _
    rw [this, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  set W0 := (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup) with hW0
  have hmem : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp [hW0, AddSubgroup.mem_pi]
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => b) φ a u (hdet.trans hu') W0
    (fun x => by
      simp only [hmem, hbO, Pi.basis_repr, Sigma.forall])
  have hle : W0.map φ.toAddEquiv.toAddMonoidHom ≤ W0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hmem]
    intro i
    change φ v i ∈ _
    rw [hφ, Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun j _ => L.O.mul_mem (hA _ _) ((hmem v).1 hv j)
  have hcomp : (Fintype.linearCombination E (rmul y A)).toAddMonoidHom =
      (Fintype.linearCombination E y).toAddMonoidHom.comp φ.toAddEquiv.toAddMonoidHom := by
    refine AddMonoidHom.ext fun v => ?_
    change Fintype.linearCombination E (rmul y A) v = Fintype.linearCombination E y (φ v)
    rw [hφ]
    simp only [Fintype.linearCombination_apply, rmul, Matrix.mulVec, dotProduct, Finset.smul_sum,
      Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hinj : Function.Injective (Fintype.linearCombination E y).toAddMonoidHom := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact funext (Fintype.linearIndependent_iff.1 hy v hv)
  rw [span_eq_map, span_eq_map, ← hW0, hcomp, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _
      hinj]
  rw [relVol, AddSubgroup.relIndex_eq_one.2 hle] at h3
  lift a to ℕ using ha
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_div, inv_inj] at h3
  rw [Int.toNat_natCast]
  exact_mod_cast h3

end GlobalTheory.MatrixIndex
