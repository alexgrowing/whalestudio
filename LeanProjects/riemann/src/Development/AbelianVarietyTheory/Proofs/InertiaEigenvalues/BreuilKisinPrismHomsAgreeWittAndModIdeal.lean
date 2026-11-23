import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.IdealSubMembership

theorem padicInt_ringHom_ext {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] {J : Ideal A}
    (hlJ : (l : A) ∈ J) [IsHausdorff J A] (φ ψ : ℤ_[l] →+* A) : φ = ψ := by
  ext c
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
  have h1 : c = ((c.appr n : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * d := by rw [← hd]; ring
  have e : φ c - ψ c = (l : A) ^ n * (φ d - ψ d) := by
    rw [h1]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ n)

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} (hJ : J ≤ (⊥ : Ideal A).jacobson) {q : ℕ}
    (hq : (q : A) ∈ J) {x y : A} (hx : x ^ q = x) (hy : y ^ q = y) (hxy : x - y ∈ J) : x = y := by
  set S := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i) with hS
  have hS1 : S * (x - y) = x - y := by
    rw [hS, geom_sum₂_mul, hx, hy]
  have hSJ : S ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy' : Ideal.Quotient.mk J y = Ideal.Quotient.mk J x := (Ideal.Quotient.eq.2 hxy).symm
    have hq' : (q : A ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]; exact hq
    rw [hS, map_sum]
    simp only [map_mul, map_pow, hxy']
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp
    have : ∀ i ∈ Finset.range q, (Ideal.Quotient.mk J x) ^ i * (Ideal.Quotient.mk J x) ^ (q - 1 - i) =
        (Ideal.Quotient.mk J x) ^ (q - 1) := fun i hi => by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hq', zero_mul]
  have hu : IsUnit (S * (-1) + 1) := (Ideal.mem_jacobson_bot.1 (hJ hSJ)) (-1)
  have h2 : (S * (-1) + 1) * (x - y) = 0 := by linear_combination -hS1
  rw [← sub_eq_zero]
  exact (hu.mul_right_eq_zero).1 h2

variable {l : ℕ} [hl : Fact l.Prime]

theorem sub_mem_I {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (x : bk.S) :
    BK.hf f x - BK.hf g x ∈ B.I := by
  have h : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
    (bk.str.apply_symm_apply _).symm
  rw [← Ideal.Quotient.eq]
  exact (f.f_str _ x h).trans (g.f_str _ x h).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧
      B.I = Ideal.span {BK.hf f bk.E} := by
  intro l _ K bk B f g
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨fun w => ?_, sub_mem_I bk f g X, ?_⟩
  · let φ1 : Wq l bk.a →+* B.A := (BK.hf f).comp C
    let φ2 : Wq l bk.a →+* B.A := (BK.hf g).comp C
    have hz := padicInt_ringHom_ext hlJ (φ1.comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (φ2.comp (algebraMap ℤ_[l] (Wq l bk.a)))
    have ht : ∀ z : Fq l bk.a, φ1 (WittVector.teichmuller l z) = φ2 (WittVector.teichmuller l z) := by
      intro z
      have hq : ((l ^ bk.a : ℕ) : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
        rw [Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hlJ _ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      have hp : WittVector.teichmuller l z ^ (l ^ bk.a) = WittVector.teichmuller l z := by
        rw [← map_pow, Fq.pow_card]
      refine eq_of_pow_eq_self (IsAdicComplete.le_jacobson_bot _) hq ?_ ?_
        (Ideal.mem_sup_right (sub_mem_I bk f g _))
      · rw [← map_pow, hp]
      · rw [← map_pow, hp]
    have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
      rw [span_teich]; exact Submodule.mem_top
    change φ1 w = φ2 w
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ht z
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, hx]
      exact congrArg (· * φ2 x) (RingHom.congr_fun hz c)
  · rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f]
    change Ideal.map f.f (Ideal.span ({bk.E} : Set bk.prism.A)) = _
    rw [Ideal.map_span]
    exact congrArg Ideal.span (Set.image_singleton (f := f.f) (a := bk.E))

end GlobalTheory.BSP.IdealSubMembership
