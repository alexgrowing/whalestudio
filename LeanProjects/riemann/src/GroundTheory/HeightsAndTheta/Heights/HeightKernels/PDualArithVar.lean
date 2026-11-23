import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualArithmeticVariety

variable {K : Type} [Field K]

def evalForm (m : ℕ) : (Fin m → K) →ₗ[K] ProjField K m :=
  Fintype.linearCombination K fun j => algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j)

theorem algebraicIndependent_gen (m : ℕ) :
    AlgebraicIndependent K fun j : Fin m =>
      algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) :=
  (MvPolynomial.algebraicIndependent_X (Fin m) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (ProjField K m))
    (IsFractionRing.injective _ _)

theorem evalForm_ne_zero {m : ℕ} {φ : Fin m → K} (hφ : φ ≠ 0) : evalForm m φ ≠ 0 := by
  intro h0
  apply hφ
  funext j
  exact Fintype.linearIndependent_iff.mp (algebraicIndependent_gen m).linearIndependent φ
    (by rw [← Fintype.linearCombination_apply]; exact h0) j

theorem mem_of_gen_mem {m : ℕ} (E : IntermediateField K (ProjField K m))
    (h : ∀ j, algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) ∈ E) (z : ProjField K m) :
    z ∈ E := by
  have hp : ∀ p : MvPolynomial (Fin m) K, algebraMap _ (ProjField K m) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp => rw [map_mul]; exact mul_mem hp (h j)
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin m) K) z
  exact div_mem (hp p) (hp q)

theorem isAlgebraic_of_adjoin {m : ℕ} (S : Set (ProjField K m))
    (h : ∀ z, z ∈ IntermediateField.adjoin K S) :
    Algebra.IsAlgebraic (Algebra.adjoin K S) (ProjField K m) := by
  rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
  exact ⟨fun z => isAlgebraic_algebraMap (⟨z, h z⟩ : IntermediateField.adjoin K S)⟩

theorem trdeg_eq (m : ℕ) : Cardinal.mk (Fin m) = Algebra.trdeg K (ProjField K m) :=
  ((algebraicIndependent_gen m).isTranscendenceBasis_iff_isAlgebraic.mpr
    (isAlgebraic_of_adjoin _ (mem_of_gen_mem _ fun j =>
      IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩))).cardinalMk_eq_trdeg

variable [NumberField K] {i : ℕ}

theorem span_dualLattice (F : HermLattice K i) :
    Submodule.span K (dualLattice F : Set (Fin i → K)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  have hmem : (N : K) • v ∈ dualLattice F := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      have hg' := hint _ (Finset.mem_image_of_mem _ hg)
      rw [smul_dotProduct, Int.cast_smul_eq_zsmul]
      exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [dotProduct_add, map_add, ha, hc]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [dotProduct_smul, map_mul, ha]
      rfl
  have hN' : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN
  have := Submodule.smul_mem (Submodule.span K (dualLattice F : Set (Fin i → K))) (N : K)⁻¹
    (Submodule.subset_span hmem)
  rwa [inv_smul_smul₀ hN'] at this

variable {F : HermLattice K i} {T : Type}

theorem span_basis [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) :
    Submodule.span K (Set.range fun t => (b t : Fin i → K)) = ⊤ := by
  refine eq_top_iff.mpr ((span_dualLattice F).symm.le.trans (Submodule.span_le.mpr fun φ hφ => ?_))
  have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  rw [← h]
  exact Submodule.sum_mem _ fun t _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self t)) _

theorem dualLatticeCoord_eq (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    dualLatticeCoord b ⟨(), t⟩ = evalForm i (b t : Fin i → K) := by
  rw [dualLatticeCoord, evalForm, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin i) K),
    MvPolynomial.algebraMap_eq]

end DualArithmeticVariety

open DualArithmeticVariety in

theorem DualArithVar.proof (h : CoordConeArithVar.Statement) : DualArithVar.Statement := by
  intro K _ _ i F T _ _ b hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K fun t => (b t : Fin (n + 1) → K)
  rw [span_basis b] at hsp
  let B : Module.Basis κ K (Fin (n + 1) → K) := Module.Basis.mk hli hsp.ge
  let e : Fin (n + 1) ≃ κ := (B.indexEquiv (Pi.basisFun K (Fin (n + 1)))).symm
  let u : Fin (n + 1) → T := a ∘ e
  let w : Fin (n + 1) → ProjField K (n + 1) := fun l => evalForm (n + 1) (b (u l) : Fin (n + 1) → K)
  let s : Fin n → ProjField K (n + 1) := fun l => w l.succ / w 0
  let v : Fin (n + 1) → ProjField K (n + 1) := Fin.cons (w 0) s
  have hy := dualLatticeCoord_eq b
  have hw0 : w 0 ≠ 0 := evalForm_ne_zero (hli.ne_zero (e 0))
  have hspw : ∀ ψ, evalForm (n + 1) ψ ∈ Submodule.span K (Set.range w) := by
    intro ψ
    have hψ : ψ ∈ Submodule.span K (Set.range (((fun t => (b t : Fin (n + 1) → K)) ∘ a) ∘ e)) := by
      rw [EquivLike.range_comp, hsp]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := evalForm (n + 1)) hψ
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hwE : ∀ l, w l ∈ IntermediateField.adjoin K (Set.range v) := by
    intro l
    have hv : ∀ l, v l ∈ IntermediateField.adjoin K (Set.range v) :=
      fun l => IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
    induction l using Fin.cases with
    | zero => exact hv 0
    | succ m =>
      have := mul_mem (hv m.succ) (hv 0)
      simpa [v, s, div_mul_cancel₀ _ hw0] using this
  have hall : ∀ z, z ∈ IntermediateField.adjoin K (Set.range v) := by
    refine mem_of_gen_mem _ fun j => ?_
    have hX : algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j) =
        evalForm (n + 1) (Pi.single j 1) := by
      rw [evalForm, Fintype.linearCombination_apply_single, one_smul]
    rw [hX]
    exact (Submodule.span_le (p := (IntermediateField.adjoin K (Set.range v)).toSubalgebra.toSubmodule)).mpr
      (by rintro _ ⟨l, rfl⟩; exact hwE l) (hspw _)
  have hv : AlgebraicIndependent K v := by
    have := isAlgebraic_of_adjoin _ hall
    exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K v (trdeg_eq (n + 1)).le).1
  have hs : AlgebraicIndependent ℚ s :=
    (hv.comp Fin.succ (Fin.succ_injective _)).restrictScalars (algebraMap ℚ K).injective
  have hint : ∀ z ∈ Submodule.span K (Set.range w),
      IsIntegral (IntermediateField.adjoin ℚ (Set.range s)) (z / w 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      induction l using Fin.cases with
      | zero => rw [div_self hw0]; exact isIntegral_one
      | succ m =>
        exact isIntegral_algebraMap (x := (⟨s m, IntermediateField.subset_adjoin _ _ ⟨m, rfl⟩⟩ :
          IntermediateField.adjoin ℚ (Set.range s)))
    | zero => rw [zero_div]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [add_div]; exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, mul_div_assoc]
      exact ((Algebra.IsIntegral.isIntegral (R := ℚ) c).map
        (IsScalarTower.toAlgHom ℚ K (ProjField K (n + 1)))).tower_top.mul hx
  refine h Unit (dualBlocks T) (ProjField K (n + 1)) (dualLatticeCoord b) (fun _ => u 0) n s ⟨()⟩
    (fun _ => by rw [hy]; exact hw0) hs (fun l => IntermediateField.subset_adjoin _ _ ⟨⟨(), u l.succ⟩, ?_⟩) ?_
  · show dualLatticeCoord b ⟨(), u l.succ⟩ / dualLatticeCoord b ⟨(), u 0⟩ = w l.succ / w 0
    rw [hy, hy]
  · rintro r ⟨⟨⟨⟩, t⟩, rfl⟩
    show IsAlgebraic _ (dualLatticeCoord b ⟨(), t⟩ / dualLatticeCoord b ⟨(), u 0⟩)
    rw [hy, hy]
    exact (hint _ (hspw _)).isAlgebraic

end

end GroundTheory.Heights₂.Heights
