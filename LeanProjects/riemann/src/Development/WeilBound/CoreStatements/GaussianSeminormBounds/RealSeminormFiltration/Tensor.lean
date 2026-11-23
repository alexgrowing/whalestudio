import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpectrumNonemptyOfCountableRank

noncomputable section

namespace PositivityTheory.KReal

theorem isAlgebraic_of_rank_le {D : Type} [DivisionRing D] [Algebra ℂ D]
    (h : Module.rank ℂ D ≤ Cardinal.aleph0) (x : D) : IsAlgebraic ℂ x := by
  let S : Subalgebra ℂ D := Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ {x} : Set D)
  have hS : ∀ a : D, a ∈ S ↔ ∀ g : D, x * g = g * x → g * a = a * g := by
    intro a
    simp only [S, Subalgebra.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  have hx : x ∈ S := (hS x).2 fun g hg => hg.symm
  have hF : IsField S :=
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := fun a b => Subtype.ext ((hS b).1 b.2 a ((hS a).1 a.2 x rfl))
      mul_inv_cancel := fun {a} ha => by
        have ha' : (a : D) ≠ 0 := fun h0 => ha (Subtype.ext h0)
        refine ⟨⟨(a : D)⁻¹, (hS _).2 fun g hg => ?_⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
        exact (Commute.inv_right₀ ((hS a).1 a.2 g hg : Commute g a)).eq }
  letI : Field S := hF.toField
  have hx' : IsAlgebraic ℂ (⟨x, hx⟩ : S) := by
    by_contra ht
    have h1 := (Transcendental.linearIndependent_sub_inv (F := ℂ) (E := S) ht).cardinal_le_rank
    have h2 : Module.rank ℂ S ≤ Module.rank ℂ D :=
      LinearMap.rank_le_of_injective S.val.toLinearMap Subtype.val_injective
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans (h2.trans h)) (not_le.2 Cardinal.aleph0_lt_continuum)
  exact hx'.algHom S.val

theorem schur_countable {B V : Type} [Ring B] [Algebra ℂ B] [AddCommGroup V] [Module ℂ V] [Module B V]
    [IsScalarTower ℂ B V] [IsSimpleModule B V] (h : Module.rank ℂ V ≤ Cardinal.aleph0) :
    Function.Surjective (algebraMap ℂ (Module.End B V)) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial B V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ev : Module.End B V →ₗ[ℂ] V :=
    { toFun := fun T => T v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro T hT
    by_contra h0
    exact hv ((LinearMap.injective_of_ne_zero h0) (by rw [map_zero]; exact hT))
  have hr : Module.rank ℂ (Module.End B V) ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_injective ev hev).trans h
  have : Algebra.IsAlgebraic ℂ (Module.End B V) := ⟨isAlgebraic_of_rank_le hr⟩
  have : Algebra.IsIntegral ℂ (Module.End B V) := Algebra.IsAlgebraic.isIntegral
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)).2

theorem dense_countable {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (h : Module.rank ℂ V ≤ Cardinal.aleph0) (B : Subalgebra ℂ (Module.End ℂ V))
    (hB : ∀ N : Submodule ℂ V, (∀ b ∈ B, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End ℂ V) (s : Finset V) : ∃ b ∈ B, ∀ m ∈ s, f m = b m :=
  _root_.UpperTheory.Reformulated.B.DYhd6.main h B hB f s

section

variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def one_op (i : ι) (f : Module.End ℂ (M i)) : Module.End ℂ (PiTensorProduct ℂ M) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i f)

theorem one_op_tprod (i : ι) (f : Module.End ℂ (M i)) (x : ∀ j, M j) :
    one_op i f (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (Function.update x i (f (x i))) := by
  rw [one_op, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem one_op_mul (i : ι) (f g : Module.End ℂ (M i)) : one_op i (f * g) = one_op i f * one_op i g := by
  ext x
  simp [one_op_tprod]

theorem one_op_add (i : ι) (f g : Module.End ℂ (M i)) : one_op i (f + g) = one_op i f + one_op i g := by
  ext x
  simp [one_op_tprod]

theorem one_op_alg (i : ι) (c : ℂ) : one_op i (algebraMap ℂ (Module.End ℂ (M i)) c) = algebraMap ℂ _ c := by
  ext x
  simp [one_op_tprod]

theorem one_op_fin (i : ι) (x : PiTensorProduct ℂ M) :
    ∃ s : Finset (M i), ∀ f g : Module.End ℂ (M i), (∀ m ∈ s, f m = g m) → one_op i f x = one_op i g x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    refine ⟨{y i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, one_op_tprod, one_op_tprod, h _ (Finset.mem_singleton_self _)]
  | add y z hy hz =>
    obtain ⟨s, hs⟩ := hy
    obtain ⟨t, ht⟩ := hz
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      ht f g fun m hm => h m (Finset.mem_union_right _ hm)]

theorem map_mem_of_one_op [Fintype ι] (N : Submodule ℂ (PiTensorProduct ℂ M))
    (hN : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N)
    (f : ∀ i, Module.End ℂ (M i)) (x : PiTensorProduct ℂ M) (hx : x ∈ N) : PiTensorProduct.map f x ∈ N := by
  have key : ∀ s : Finset ι,
      PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) x ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hx
    | insert i s hi ih =>
      have e : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) =
          one_op i (f i) ∘ₗ
            PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) := by
        rw [one_op, ← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj, Function.update_of_ne hj]
      rw [e]
      exact hN i (f i) _ ih
  simpa using key Finset.univ

end

theorem tensorIrr : TensorIrr := by
  intro ι _ _ A M _ _ act hr hnt hirr N hN
  have hall : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N := by
    intro i f x hx
    let B : Subalgebra ℂ (Module.End ℂ (M i)) :=
      { carrier := {b | ∀ y ∈ N, one_op i b y ∈ N}
        mul_mem' := fun {a b} ha hb y hy => by
          rw [one_op_mul]; exact ha _ (hb y hy)
        add_mem' := fun {a b} ha hb y hy => by
          rw [one_op_add]; exact N.add_mem (ha y hy) (hb y hy)
        algebraMap_mem' := fun c y hy => by
          rw [one_op_alg]; exact N.smul_mem c hy }
    obtain ⟨s, hs⟩ := one_op_fin i x
    have := hnt i
    obtain ⟨b, hb, hfb⟩ := dense_countable (hr i) B
      (fun P hP => hirr i P fun a y hy => hP (act i a) (hN i a) y hy) f s
    rw [hs f b hfb]
    exact hb x hx
  rw [or_iff_not_imp_left]
  intro h0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  let b := fun i => Module.Basis.ofVectorSpace ℂ (M i)
  obtain ⟨p, hp⟩ : ∃ p, (Basis.piTensorProduct b).repr x p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 ((Basis.piTensorProduct b).repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      ((Basis.piTensorProduct b).coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext y
    simp [Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]
  have h1 := map_mem_of_one_op N hall (fun i => ((b i).coord (p i)).smulRight (v i)) x hx
  rw [e, LinearMap.smulRight_apply] at h1
  exact (N.smul_mem_iff hp).1 h1

end PositivityTheory.KReal

end
