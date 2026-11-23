import Mathlib
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Poly

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]

def HeckePolyFor (op : I → Module.End K V) (p : K[X]) : Prop :=
  p ≠ 0 ∧ ∃ s : Finset I, (∀ x, ∃ c : I → K, op x = ∑ y ∈ s, c y • op y) ∧ ∀ y ∈ s, Polynomial.aeval (op y) p = 0

theorem HeckePolyFor.of_dvd {op : I → Module.End K V} {p q : K[X]} (h : HeckePolyFor op p) (hq : q ≠ 0) (hpq : p ∣ q) :
    HeckePolyFor op q := by
  obtain ⟨s, hs, hz⟩ := h.2
  obtain ⟨r, rfl⟩ := hpq
  exact ⟨hq, s, hs, fun y hy => by rw [map_mul, hz y hy, zero_mul]⟩

theorem hfs_exists_poly [FiniteDimensional K V] (op : I → Module.End K V) : ∃ p, HeckePolyFor op p := by
  classical
  obtain ⟨b, hbsub, hbsp, hbli⟩ := exists_linearIndependent K (Set.range op)
  have hbfin : b.Finite := by
    first
    | exact hbli.setFinite
    | exact @Set.toFinite _ b hbli.finite
  obtain ⟨s, -, hs⟩ := Finset.subset_set_image_iff.1
    (show (↑hbfin.toFinset : Set (Module.End K V)) ⊆ op '' Set.univ by
      rw [Set.image_univ, Set.Finite.coe_toFinset]; exact hbsub)
  have h1 : ∀ x, op x ∈ Submodule.span K (op '' (s : Set I)) := by
    intro x
    rw [← Finset.coe_image, hs, Set.Finite.coe_toFinset, hbsp]
    exact Submodule.subset_span ⟨x, rfl⟩
  refine ⟨∏ y ∈ s, minpoly K (op y), ?_, s, fun x => ?_, fun y hy => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 (fun y _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral (op y)))
  · obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination K).1 (h1 x)
    refine ⟨l, ?_⟩
    rw [← hlx, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l (fun i hi => hl hi) _ (fun i _ => zero_smul K (op i))]
  · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun y => minpoly K (op y)) hy
    rw [hr, map_mul, minpoly.aeval, zero_mul]

end Poly

section Lifts

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
  {S : GSD K} {S' : GSD L} (b : GSDBC ι S S')

namespace GSDBC

def Lifts (A' : Module.End L S'.EqFun) (A : Module.End K S.EqFun) : Prop := ∀ φ, A' (b.lift φ) = b.lift (A φ)

variable {b}

theorem Lifts.add {A' B' : Module.End L S'.EqFun} {A B : Module.End K S.EqFun} (hA : b.Lifts A' A) (hB : b.Lifts B' B) :
    b.Lifts (A' + B') (A + B) := by
  intro φ
  rw [LinearMap.add_apply, LinearMap.add_apply, hA φ, hB φ, lift_add]

theorem Lifts.sub {A' B' : Module.End L S'.EqFun} {A B : Module.End K S.EqFun} (hA : b.Lifts A' A) (hB : b.Lifts B' B) :
    b.Lifts (A' - B') (A - B) := by
  intro φ
  have hs : ∀ φ ψ : S.EqFun, b.lift (φ - ψ) = b.lift φ - b.lift ψ := fun φ ψ =>
    eq_sub_of_add_eq (by rw [← lift_add, sub_add_cancel])
  rw [LinearMap.sub_apply, LinearMap.sub_apply, hA φ, hB φ, hs]

theorem Lifts.mul {A' B' : Module.End L S'.EqFun} {A B : Module.End K S.EqFun} (hA : b.Lifts A' A) (hB : b.Lifts B' B) :
    b.Lifts (A' * B') (A * B) := by
  intro φ
  show A' (B' (b.lift φ)) = b.lift (A (B φ))
  rw [hB φ, hA]

theorem Lifts.smul {A' : Module.End L S'.EqFun} {A : Module.End K S.EqFun} (hA : b.Lifts A' A) (a : K) :
    b.Lifts (ι a • A') (a • A) := by
  intro φ
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hA φ, lift_smul]

theorem Lifts.one : b.Lifts 1 1 := fun _ => rfl

theorem Lifts.zero : b.Lifts 0 0 := by
  intro φ
  simp only [LinearMap.zero_apply, lift_zero]

theorem Lifts.pow {A' : Module.End L S'.EqFun} {A : Module.End K S.EqFun} (hA : b.Lifts A' A) (k : ℕ) :
    b.Lifts (A' ^ k) (A ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact Lifts.one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hA

theorem Lifts.sum {α : Type} (s : Finset α) (c : α → K) {A' : α → Module.End L S'.EqFun} {A : α → Module.End K S.EqFun}
    (hA : ∀ x ∈ s, b.Lifts (A' x) (A x)) : b.Lifts (∑ x ∈ s, ι (c x) • A' x) (∑ x ∈ s, c x • A x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lifts.zero
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact ((hA x (Finset.mem_insert_self x s)).smul (c x)).add
      (ih (fun y hy => hA y (Finset.mem_insert_of_mem hy)))

theorem Lifts.aeval {A' : Module.End L S'.EqFun} {A : Module.End K S.EqFun} (hA : b.Lifts A' A) (p : K[X]) :
    b.Lifts (Polynomial.aeval A' (p.map ι)) (Polynomial.aeval A p) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Polynomial.natDegree_map]
  simp only [Polynomial.coeff_map]
  exact Lifts.sum _ _ (fun i _ => hA.pow i)

variable (b)

theorem Lifts.eq_zero (F : CoefFrame ι) {A' : Module.End L S'.EqFun} (hA : b.Lifts A' 0) : A' = 0 := by
  refine LinearMap.ext_on (s := Set.range b.lift) ?_ ?_
  · exact eq_top_iff.2 (fun φ _ => mem_span_lift (b := b) (F := F) φ)
  · rintro _ ⟨φ, rfl⟩
    rw [hA φ]
    simp only [LinearMap.zero_apply, lift_zero]

include b in

theorem finiteDimensional (F : CoefFrame ι) [FiniteDimensional K S.EqFun] : FiniteDimensional L S'.EqFun := by
  classical
  let B := Module.finBasis K S.EqFun
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => b.lift (B i)) := by
    intro φ' _
    have h := mem_span_lift (b := b) (F := F) φ'
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨φ, rfl⟩
    rw [← B.sum_repr φ, lift_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  exact ⟨⟨Finset.univ.image fun i => b.lift (B i), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact eq_top_iff.2 hsp⟩⟩

theorem splitOver (F : CoefFrame ι) [FiniteDimensional K S.EqFun] {I : Type} (op : I → Module.End K S.EqFun)
    (op' : I → Module.End L S'.EqFun) (hl : ∀ x, b.Lifts (op' x) (op x)) (hc : PairComm op) {p : K[X]}
    (hp : HeckePolyFor op p) (hsp : (p.map ι).Splits) : SplitOver op' := by
  haveI := b.finiteDimensional F
  obtain ⟨hp0, s, hs, hd⟩ := hp
  have hcomm : ∀ y z, Commute (op' y) (op' z) := fun y z => by
    have h0 : b.Lifts (op' y * op' z - op' z * op' y) 0 := by
      have := ((hl y).mul (hl z)).sub ((hl z).mul (hl y))
      rwa [(hc y z).eq, sub_self] at this
    exact sub_eq_zero.mp (Lifts.eq_zero b F h0)
  have hsplit : ∀ y ∈ s, ⨆ μ, (op' y).maxGenEigenspace μ = ⊤ := by
    intro y hy
    apply hfs_iSup_maxGen_of_splits
    have h0 : b.Lifts (Polynomial.aeval (op' y) (p.map ι)) 0 := by
      have := (hl y).aeval p
      rwa [hd y hy] at this
    have hann : Polynomial.aeval (op' y) (p.map ι) = 0 := Lifts.eq_zero b F h0
    exact hsp.of_dvd (Polynomial.map_ne_zero hp0) (minpoly.dvd L _ hann)
  intro x
  obtain ⟨c, hcx⟩ := hs x
  have h0 : b.Lifts (op' x - ∑ y ∈ s, ι (c y) • op' y) 0 := by
    have := (hl x).sub (Lifts.sum (b := b) s c fun y _ => hl y)
    rwa [← hcx, sub_self] at this
  have hx : op' x = ∑ y ∈ s, ι (c y) • op' y := sub_eq_zero.mp (Lifts.eq_zero b F h0)
  rw [hx]
  exact hfs_iSup_maxGen_sum s op' (fun y => ι (c y)) (fun y _ z _ => hcomm y z) hsplit

end GSDBC

end Lifts

section HeckeLift

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
  {S : GSD K} {S' : GSD L} (b : GSDBC ι S S')
  {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (c : DecoPts S E n ST SG) (c' : DecoPts S' E n ST SG)

namespace GSDBC

end GSDBC

end HeckeLift

end Formalism.L2.Col
