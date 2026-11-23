import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

open NumberField Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.LKTrip

namespace LevelExists

theorem isCompact_intCompl (v : HeightOneSpectrum ℤ) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  haveI : CompleteSpace (v.adicCompletionIntegers ℚ) :=
    (Valued.isClosed_valuationSubring (v.adicCompletion ℚ)).completeSpace_coe
  haveI : Finite (ℤ ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv
  have hc : CompactSpace (Valued.integer (v.adicCompletion ℚ)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨inferInstanceAs (CompleteSpace (v.adicCompletionIntegers ℚ)),
        inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers ℚ)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))⟩
  exact isCompact_iff_compactSpace.mpr hc

def rp {p : ℕ} (x : AfP p) : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] := x

def intAfP (p : ℕ) : Subring (AfP p) where
  carrier := {x | ∀ v : AwayP p, (rp x).1 v ∈ v.1.adicCompletionIntegers ℚ}
  mul_mem' := by intro a b ha hb v; exact mul_mem (ha v) (hb v)
  one_mem' := by intro v; exact one_mem _
  add_mem' := by intro a b ha hb v; exact add_mem (ha v) (hb v)
  zero_mem' := by intro v; exact zero_mem _
  neg_mem' := by intro a ha v; exact neg_mem (ha v)

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p : Set (AfP p)) := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun w : AwayP p => w.1.adicCompletion ℚ)
    (A := fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ)))
    (fun w => Valued.isOpen_valuationSubring (w.1.adicCompletion ℚ))

theorem isCompact_intAfP (p : ℕ) : IsCompact (intAfP p : Set (AfP p)) := by
  haveI : ∀ w : AwayP p, CompactSpace (w.1.adicCompletionIntegers ℚ) :=
    fun w => isCompact_iff_compactSpace.mp (isCompact_intCompl w.1)
  let e := RestrictedProduct.homeoTop (R := fun w : AwayP p => w.1.adicCompletion ℚ)
    (A := fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ)))
  let f : (Π w : AwayP p, w.1.adicCompletionIntegers ℚ) → AfP p := fun g =>
    RestrictedProduct.inclusion (fun w : AwayP p => w.1.adicCompletion ℚ)
      (fun w => (w.1.adicCompletionIntegers ℚ : Set (w.1.adicCompletion ℚ))) le_top (e g)
  have hf : Continuous f :=
    (RestrictedProduct.continuous_inclusion le_top).comp e.continuous
  have hset : (intAfP p : Set (AfP p)) = Set.range f := by
    ext x
    constructor
    · intro hx
      exact ⟨fun w => ⟨(rp x).1 w, hx w⟩, rfl⟩
    · rintro ⟨g, rfl⟩ w
      exact (g w).2
  rw [hset]
  exact isCompact_range hf

end LevelExists

namespace LevelExists

section Tensor

variable (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
  (F : Type) [Field F] [NumberField F]

def tensorInt (O : Subring R) : Subring (R ⊗[ℚ] F) where
  carrier := {x | ∀ i j, Algebra.leftMulMatrix (Algebra.TensorProduct.basis R (Module.finBasis ℚ F)) x i j ∈ O}
  mul_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_mul, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (hx i k) (hy k j)
  one_mem' := by
    intro i j
    simp only [Set.mem_setOf_eq, map_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro x hx i j
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

def mulMatAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] :
    R ⊗[ℚ] A →ₐ[R] Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R :=
  (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R (Module.finBasis ℚ A))).toAlgHom.comp
    (Algebra.lmul R (R ⊗[ℚ] A))

def tensorIntAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (O : Subring R) : Subring (R ⊗[ℚ] A) where
  carrier := {x | ∀ i j, mulMatAlg R A x i j ∈ O}
  mul_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_mul, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (hx i k) (hy k j)
  one_mem' := by
    intro i j
    simp only [Set.mem_setOf_eq, map_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro x y hx hy i j
    simp only [Set.mem_setOf_eq, map_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro x hx i j
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

theorem isOpen_isCompact_tensorIntAlg (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (O : Subring R)
    (hOo : IsOpen (O : Set R)) (hOc : IsCompact (O : Set R)) :
    @IsOpen _ (moduleTopology R (R ⊗[ℚ] A)) (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) ∧
      @IsCompact _ (moduleTopology R (R ⊗[ℚ] A)) (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) := by
  letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
  haveI : IsModuleTopology R (R ⊗[ℚ] A) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] A)
  set bS := Algebra.TensorProduct.basis R (Module.finBasis ℚ A) with hbS
  set L := mulMatAlg R A with hL
  have hLc : Continuous L := IsModuleTopology.continuous_of_linearMap L.toLinearMap
  set box : Set (Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R) :=
    Set.univ.pi fun _ ↦ Set.univ.pi fun _ ↦ (O : Set R) with hbox
  have hset : (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) = L ⁻¹' box := by
    ext x
    constructor
    · intro h i _ j _; exact h i j
    · intro h i j; exact h i trivial j trivial
  have hopen : IsOpen (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) := by
    rw [hset]
    exact hLc.isOpen_preimage _ (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_set_pi Set.finite_univ fun _ _ ↦ hOo)
  refine ⟨hopen, ?_⟩
  have hboxc : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ hOc
  set w := bS.equivFun 1
  let ψ : Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A)) R → R ⊗[ℚ] A :=
    fun M ↦ bS.equivFun.symm (M *ᵥ w)
  have hψ : Continuous ψ :=
    (IsModuleTopology.continuous_of_linearMap bS.equivFun.symm.toLinearMap).comp
      (continuous_id.matrix_mulVec continuous_const)
  have e : ∀ f : Module.End R (R ⊗[ℚ] A), LinearMap.toMatrixAlgEquiv bS f = LinearMap.toMatrix bS bS f :=
    fun f ↦ by ext i j; simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hrec : ∀ x, ψ (L x) = x := by
    intro x
    show bS.equivFun.symm (LinearMap.toMatrixAlgEquiv bS (Algebra.lmul R (R ⊗[ℚ] A) x) *ᵥ bS.equivFun 1) = x
    rw [e, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, ← Module.Basis.equivFun_apply,
      LinearEquiv.symm_apply_apply]
    simp
  have hsub : (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) ⊆ ψ '' box := by
    intro x hx
    refine ⟨L x, by rw [hset] at hx; exact hx, hrec x⟩
  have hcl : IsClosed (tensorIntAlg R A O : Set (R ⊗[ℚ] A)) :=
    AddSubgroup.isClosed_of_isOpen (tensorIntAlg R A O).toAddSubgroup hopen
  exact (hboxc.image hψ).of_isClosed_subset hcl hsub

theorem t2Space_tensor_rat_finite_algebra_moduleTopology [T2Space R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] :
    @T2Space (R ⊗[ℚ] A) (moduleTopology R (R ⊗[ℚ] A)) := by
  letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
  haveI : IsModuleTopology R (R ⊗[ℚ] A) := ⟨rfl⟩
  set bS := Algebra.TensorProduct.basis R (Module.finBasis ℚ A)
  exact T2Space.of_injective_continuous bS.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap bS.equivFun.toLinearMap)

end Tensor

end LevelExists

namespace LevelExists

section Entries

variable {S : Type} [CommRing S] {n : ℕ}

def EntriesIn (n : ℕ) (P : Subring S) : Set (Matrix (Fin n) (Fin n) S) := {M | ∀ i j, M i j ∈ P}

end Entries

variable {p : ℕ} [Fact p.Prime]

def stdLevel (G : HTGroup p) (O : Subring (AfP p)) (P : Subring (AfP p ⊗[ℚ] G.C)) : Subgroup G.GAf where
  carrier := {x | ((((x.1.1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) ∈ P ∧
      (((x.1.1⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) ∈ P) ∧
      (((x.1.2 : (AfP p)ˣ) : AfP p) ∈ O ∧ (((x.1.2⁻¹ : (AfP p)ˣ)) : AfP p) ∈ O))}
  mul_mem' := by
    rintro x y ⟨⟨hx1, hx2⟩, hx3, hx4⟩ ⟨⟨hy1, hy2⟩, hy3, hy4⟩
    exact ⟨⟨mul_mem hx1 hy1, mul_mem hy2 hx2⟩, mul_mem hx3 hy3, mul_mem hy4 hx4⟩
  one_mem' := ⟨⟨P.one_mem, P.one_mem⟩, O.one_mem, O.one_mem⟩
  inv_mem' := by
    rintro x ⟨⟨hx1, hx2⟩, hx3, hx4⟩
    exact ⟨⟨hx2, hx1⟩, hx4, hx3⟩

theorem level_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Nonempty G.Level := by
  intro p _ G
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C
  obtain ⟨hPo, hPc⟩ := isOpen_isCompact_tensorIntAlg (AfP p) G.C (intAfP p) (isOpen_intAfP p) (isCompact_intAfP p)
  have hOo := isOpen_intAfP p
  have hOc := isCompact_intAfP p
  set P := tensorIntAlg (AfP p) G.C (intAfP p)
  set O := intAfP p
  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let g : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding g :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  let C := ((P : Set (AfP p ⊗[ℚ] G.C)) ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' (P : Set (AfP p ⊗[ℚ] G.C)))) ×ˢ
    ((O : Set (AfP p)) ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' (O : Set (AfP p))))
  have hKC : (stdLevel G O P : Set G.GAf) = g ⁻¹' C := rfl
  refine ⟨⟨⟨stdLevel G O P, ?_⟩, ?_⟩⟩
  · show IsOpen (stdLevel G O P : Set G.GAf)
    rw [hKC]
    exact hg.continuous.isOpen_preimage _ ((hPo.prod
      (MulOpposite.opHomeomorph.symm.isOpen_preimage.2 hPo)).prod
      (hOo.prod (MulOpposite.opHomeomorph.symm.isOpen_preimage.2 hOo)))
  · show IsCompact (stdLevel G O P : Set G.GAf)
    rw [hKC]
    exact hg.isCompact_preimage ((hPc.prod
      (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod
      (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))

end LevelExists

end GlobalTheory.LKTrip
