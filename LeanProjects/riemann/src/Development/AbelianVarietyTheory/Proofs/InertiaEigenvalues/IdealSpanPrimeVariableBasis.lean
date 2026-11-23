import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_residue_basis_of_isMaximal {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : m.IsMaximal] (h : m.map f ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : A, ∃ a : ι →₀ R, x - a.sum (fun i y => f y * b i) ∈ m.map f) ∧
      ∀ a : ι →₀ R, a.sum (fun i y => f y * b i) ∈ m.map f → ∀ i, a i ∈ m := by
  first
  | exact @_root_.GlobalTheory.ClosedStatement.main
  | exact _root_.GlobalTheory.ClosedStatement.main
  | (apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedStatement.main ..)

theorem isMaximal_span_l_sup_span_X (l a : ℕ) [Fact l.Prime] [NeZero a] :
    (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)}).IsMaximal := by
  have hmax : (Ideal.span {(l : Wq l a)}).IsMaximal := by
    rw [← (WittVector.irreducible l (k := Fq l a)).maximalIdeal_eq]
    infer_instance
  have hsurj : Function.Surjective (constantCoeff (R := Wq l a)) := fun w => ⟨C w, by simp⟩
  have heq : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)} =
      (Ideal.span {(l : Wq l a)}).comap (constantCoeff (R := Wq l a)) := by
    apply le_antisymm
    · refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      · rw [map_natCast]
        exact Ideal.mem_span_singleton_self _
      · simp
    · intro x hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hx)
      have hX : (X : (Wq l a)⟦X⟧) ∣ x - C w * l := by
        rw [X_dvd_iff, map_sub, map_mul, map_natCast, constantCoeff_C, hw, sub_self]
      have : x = C w * l + (x - C w * l) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mem_span_singleton.2 hX)
  rw [heq]
  exact Ideal.comap_isMaximal_of_surjective _ hsurj

theorem BK.map_span_l_sup_span_X_ne_top {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev ≠ ⊤ := by
  let M : Ideal (Ainf l) := (IsLocalRing.maximalIdeal (OC l)).comap (Per.θ l)
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ _
  let N : Ideal bk.S := M.comap bk.ev
  haveI hN : N.IsPrime := Ideal.comap_isPrime _ _
  have hl : (l : bk.S) ∈ N := by
    change Per.θ l (bk.ev l) ∈ IsLocalRing.maximalIdeal (OC l)
    rw [map_natCast, map_natCast]
    exact (Fact.out : ¬ IsUnit (l : OC l))
  have hE : bk.E ∈ N := by
    change Per.θ l (bk.ev bk.E) ∈ IsLocalRing.maximalIdeal (OC l)
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.1 this]
    exact Ideal.zero_mem _
  have hX : (X : bk.S) ∈ N := by
    apply hN.mem_of_pow_mem bk.Ep.natDegree
    have h1 := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
    rw [map_add, map_pow, map_sum] at h1
    have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)
        (Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i) ∈ N := by
      refine Ideal.sum_mem _ fun i hi => ?_
      obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
      rw [hw, map_mul, map_mul, map_mul, map_natCast, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hl)
    have h2 := N.sub_mem hE hs
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X] at h1 h2
    have h3 := sub_eq_of_eq_add h1
    rwa [h3] at h2
  intro htop
  apply hM.ne_top
  rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hl) ((Ideal.span_singleton_le_iff_mem _).2 hX)

theorem BK.exists_residue_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧
      ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev →
        ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  intro l _ K bk
  haveI := isMaximal_span_l_sup_span_X l bk.a
  exact exists_residue_basis_of_isMaximal bk.ev _ bk.map_span_l_sup_span_X_ne_top

end GlobalTheory.BSP
