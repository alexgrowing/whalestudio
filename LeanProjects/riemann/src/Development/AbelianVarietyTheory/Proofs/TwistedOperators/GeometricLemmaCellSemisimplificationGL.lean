import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClassesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLeviStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorDoublyIndexedSwapBlocksEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultNormalisedInductionExactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorSmoothRepsExactEachFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveFamilyFunctionDeterminedConstituentsStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult
open scoped TensorProduct

namespace GlobalTheory.SmGL.CellSemis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def relIndEquiv {α β : Type} [Fintype α] [Fintype β] [LinearOrder β] {m : α → Type}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β → Type} [∀ i j, Fintype (c i j)]
    [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (∀ i, Levi k (c i)) V}
    {σ : Representation ℂ (∀ i, Levi k (c i)) W} (φ : ρ.Equiv σ) : (relInd f ρ).Equiv (relInd f σ) :=
  GlobalTheory.LocGL.equivOfBijective (smIndMap (compMap (twistMap φ.toIntertwiningMap _) _))
    (Function.bijective_iff_has_inverse.2
      ⟨smIndMap (compMap (twistMap φ.symm.toIntertwiningMap _) _),
        fun F => Subtype.ext (Subtype.ext (funext fun x => φ.symm_apply_apply (F.1.1 x))),
        fun F => Subtype.ext (Subtype.ext (funext fun x => φ.apply_symm_apply (F.1.1 x)))⟩)

theorem jhMult_relInd_of_subsingleton {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
    {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β → Type}
    [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) {V : Type}
    [AddCommGroup V] [Module ℂ V] [Subsingleton V] (ρ : Representation ℂ (∀ i, Levi k (c i)) V)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k m) Y}
    (hτ : τ.IsIrreducible) : jhMult τ (relInd f ρ) = 0 := by
  haveI : Subsingleton (smoothPart (ind (relParab k f) ((twist ρ (relDeltaHalf k c)).comp (relProj k f)))) :=
    ⟨fun a b => Subtype.ext (Subtype.ext (funext fun _ => Subsingleton.elim _ _))⟩
  exact jhMult_of_subsingleton hτ _

theorem subsingleton_piTensor {α : Type} [Fintype α] [DecidableEq α] {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (i : α) [Subsingleton (X i)] :
    Subsingleton (⨂[ℂ] a, X a) := by
  have h : ∀ z : ⨂[ℂ] a, X a, z = 0 := fun z => by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim _ _), smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩

end GlobalTheory.SmGL.CellSemis

open GlobalTheory.SmGL.CellSemis in
theorem GlobalTheory.SmGL.CellSemis.cellSemisimplification : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  intro hBZ k _ _ _ _ α β _ _ _ _ m _ _ m' _ _ c _ _ f g X _ _ ρ hρ hl
  classical
  let A : ∀ i, SmRep (Levi k (c i)) := fun i => ⟨_, jac (f i) (ρ i), isSmooth_jac (f i) (hρ i)⟩
  have hA : ∀ i, HasFiniteLength (A i).ρ := fun i =>
    (hBZ k).2.1 β (m i) (c i) (f i) (X i) (ρ i) (hρ i) (hl i)
  let Φ : IrrRep (Levi k m') → (∀ i, SmRep (Levi k (c i))) → ℕ∞ := fun τ B =>
    jhMult τ.ρ (relInd (c := fun j i => c i j) g ((piTensor fun i => (B i).ρ).comp (swapBlocks k c)))
  have hswap : Continuous (swapBlocks k c) := by
    show Continuous fun g : (∀ j, Levi k fun i => c i j) => fun i j => g j i
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)
  have hzero : ∀ τ (B : ∀ i, SmRep (Levi k (c i))) (i : α), Subsingleton (B i).V → Φ τ B = 0 := by
    intro τ B i hi
    haveI := subsingleton_piTensor (X := fun a => (B a).V) i
    exact jhMult_relInd_of_subsingleton _ _ τ.irr
  have hexact : ∀ τ (B : ∀ i, SmRep (Levi k (c i))) (i : α) (C C₁ C₂ : SmRep (Levi k (c i)))
      (ι : C₁.ρ.IntertwiningMap C.ρ) (p : C.ρ.IntertwiningMap C₂.ρ), Function.Injective ι →
      Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) →
      Φ τ (Function.update B i C) = Φ τ (Function.update B i C₁) + Φ τ (Function.update B i C₂) := by
    intro τ B i C C₁ C₂ ι p h1 h2 h3 h4
    obtain ⟨ι', p', h1', h2', h3', h4'⟩ := GlobalTheory.T.piTensor_smooth_reps_exact_each_factor α (fun i => Levi k (c i)) B i C C₁ C₂ ι p h1 h2 h3 h4
    exact GlobalTheory.T.jordanHolder_mult_normalised_induction_exact k β α m' (fun j i => c i j) g _ _ _ _ _ _ (compMap ι' _) (compMap p' _) h1' h2' h3' h4'
      (isSmooth_comp (isSmooth_piTensor fun a => (Function.update B i C a).smooth) _ hswap) _ τ.ρ τ.irr
  let T' : Finset (∀ i, IrrCl (Levi k (c i))) :=
    Fintype.piFinset fun i => (finite_constituents (hA i)).toFinset
  have hT' : ∀ t ∉ T', ∃ i, jhMult (t i).rep.ρ (A i).ρ = 0 := by
    intro t ht
    rw [Fintype.mem_piFinset] at ht
    push_neg at ht
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, by simpa using hi⟩
  let P : ∀ i, (∀ j, IrrCl (GL (c i j) k)) → IrrRep (Levi k (c i)) := fun i s =>
    ⟨_, piTensor fun j => (s j).rep.ρ, isSmooth_piTensor fun j => (s j).rep.smooth,
      GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k β (c i) fun j => (s j).rep⟩
  let Θ : (∀ i j, IrrCl (GL (c i j) k)) → ∀ i, IrrCl (Levi k (c i)) := fun s i => (P i (s i)).cl
  have hΘi : Function.Injective Θ := by
    intro s s' h
    funext i j
    have h2 := GlobalTheory.T.tensor_product_determines_factor_classes β (fun j => GL (c i j) k) (fun j => (s i j).rep) (fun j => (s' i j).rep)
      (IrrRep.cl_eq_iff.1 (congrFun h i)) j
    rwa [IrrCl.cl_rep, IrrCl.cl_rep] at h2
  have hΘs : Function.Surjective Θ := by
    intro t
    choose s hs using fun i => GlobalTheory.T.exists_equiv_piExteriorTensor_blockLevi hBZ k β (c i) (t i).rep
    refine ⟨fun i j => (s i j).cl, funext fun i => ?_⟩
    rw [← (t i).cl_rep]
    exact IrrRep.cl_eq_iff.2 ⟨(GlobalTheory.LocGL.piTensorEquiv fun j => (s i j).nonempty_equiv_rep.some).trans
      (hs i).some.symm⟩
  refine ⟨T'.preimage Θ hΘi.injOn, fun s hs => ?_, fun τ => ?_⟩
  · rw [Finset.mem_preimage] at hs
    obtain ⟨i, hi⟩ := hT' _ hs
    exact ⟨i, (jhMult_congr_left (P i (s i)).nonempty_equiv_rep.some.symm _).trans hi⟩
  · have hLHS : jhMult τ.ρ (cellFunctor f g (piTensor ρ)) = Φ τ A :=
      jhMult_congr_right _ (relIndEquiv g (GlobalTheory.LocGL.compEquiv (GlobalTheory.T.relative_jacquet_functor_piTensor_equiv k α β m c f X ρ).some (swapBlocks k c)))
    rw [hLHS, GlobalTheory.T.additive_family_function_determined_constituents α (fun i => Levi k (c i)) (Φ τ) (hzero τ) (hexact τ) A hA T' hT',
      ← Finset.sum_preimage Θ T' hΘi.injOn _ (fun t _ ht => absurd (hΘs t) ht)]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ =>
      jhMult_congr_left (P i (s i)).nonempty_equiv_rep.some _) (jhMult_congr_right _ ?_)
    exact (relIndEquiv g ((GlobalTheory.LocGL.compEquiv (GlobalTheory.LocGL.piTensorEquiv fun i =>
      (P i (s i)).nonempty_equiv_rep.some) (swapBlocks k c)).trans
        (GlobalTheory.T.piTensor_doubly_indexed_swap_blocks_equiv k α β c (fun i j => (s i j).rep.V) (fun i j => (s i j).rep.ρ)).some)).trans
      (GlobalTheory.T.normalised_induction_product_parabolic_piTensor k β α m' (fun j i => c i j) g (fun j => ⨂[ℂ] i, (s i j).rep.V)
        (fun j => piTensor fun i => (s i j).rep.ρ) (fun j => isSmooth_piTensor fun i => (s i j).rep.smooth)).some
