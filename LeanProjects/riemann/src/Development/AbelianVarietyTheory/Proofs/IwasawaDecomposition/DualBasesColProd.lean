import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

def fockQRight {σ : Type} (f : MvPolynomial σ ℚ) : MvPolynomial σ ℚ →ₗ[ℚ] ℚ where
  toFun g := Formalism.GradedWeylDivisibility.fockQ f g
  map_add' g g' := by
    show Formalism.GradedWeylDivisibility.fockQ f (g + g') = Formalism.GradedWeylDivisibility.fockQ f g + Formalism.GradedWeylDivisibility.fockQ f g'
    rw [(Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g g' f 1).1, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1,
      (Formalism.GradedWeylDivisibility.fockQPos σ g' f).1]
  map_smul' c g := by
    show Formalism.GradedWeylDivisibility.fockQ f (c • g) = c • Formalism.GradedWeylDivisibility.fockQ f g
    rw [smul_eq_mul, (Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g 0 f c).2, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1]

theorem fockQRight_apply {σ : Type} (f g : MvPolynomial σ ℚ) : fockQRight f g = Formalism.GradedWeylDivisibility.fockQ f g := rfl

theorem dual_bases_colProd : (∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h) →
  ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b g : ι → MvPolynomial (Fin N × Fin N) ℚ)
    (c : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ι → ℤ) (d : ι → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ℤ) (Nc : ℚ), Nc ≠ 0 ∧
    (∀ J, GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = ∑ k, (c J k : ℚ) • b k) ∧
    (∀ k, b k = ∑ J, (d k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ k, g k = ∑ J, (c J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0) ∧
    Submodule.span ℤ (Set.range g) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
  classical
  intro H N Y hY
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  haveI : Fintype (Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r)) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).fintype
  obtain ⟨b, d, hb, hd, hbd⟩ := GlobalTheory.StdDual.exists_dual_bases N (fun r : Fin N => Y.rowLen r) hanti
  set Nc := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) with hNc
  have hNc0 : Nc ≠ 0 := ((Formalism.GradedWeylDivisibility.fockQPos _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have H' := H N Y hY
  clear H
  set C := GlobalTheory.WeylMinorDual.colProd ℚ N Y hY with hCdef
  have hspanC : Submodule.span ℤ (GlobalTheory.StdDual.bidSet ℚ N (fun r : Fin N => Y.rowLen r)) =
      Submodule.span ℤ (Set.range C) := by
    rw [← GlobalTheory.StdDual.dualWeyl_intQ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY, Submodule.map_span,
      ← Set.range_comp]
    congr 2
    funext J
    exact Formalism.L2.DIV.fk_map_bidet (Int.castRingHom ℚ) _ _ _
  have hbC : Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range C) := hb.trans hspanC
  have hCb : ∀ J, C J ∈ Submodule.span ℤ (Set.range b) := fun J => hbC ▸ Submodule.subset_span ⟨J, rfl⟩
  have hbCm : ∀ k, b k ∈ Submodule.span ℤ (Set.range C) := fun k => hbC ▸ Submodule.subset_span ⟨k, rfl⟩
  choose c hc using fun J => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hCb J)
  choose d' hd' using fun k => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hbCm k)
  have hcQ : ∀ J, C J = ∑ k, (c J k : ℚ) • b k := fun J => by
    rw [← hc J]; simp only [Int.cast_smul_eq_zsmul]
  have hdQ : ∀ k, b k = ∑ J, (d' k J : ℚ) • C J := fun k => by
    rw [← hd' k]; simp only [Int.cast_smul_eq_zsmul]
  set g := fun k => ∑ J, (c J k : ℚ) • C J with hg
  have hdb : ∀ j k, Formalism.GradedWeylDivisibility.fockQ (d j) (b k) = if k = j then Nc else 0 := fun j k =>
    (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1.trans (hbd k j)
  have hdC : ∀ j J, Formalism.GradedWeylDivisibility.fockQ (d j) (C J) = (c J j : ℚ) * Nc := by
    intro j J
    rw [hcQ J, ← fockQRight_apply, map_sum]
    simp only [map_smul, fockQRight_apply, hdb, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hgi : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = ∑ J, (c J k : ℚ) * Formalism.GradedWeylDivisibility.fockQ (b i) (C J) := by
    intro i k
    rw [← fockQRight_apply, hg, map_sum]
    simp only [map_smul, fockQRight_apply, smul_eq_mul]
  have key : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0 := by
    intro i k
    have hmem : b i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.span_le_restrictScalars ℤ ℚ _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    have h1 := congrArg (fockQRight (d k)) (H' (b i) hmem)
    rw [map_sum, map_smul] at h1
    simp only [map_smul, fockQRight_apply, smul_eq_mul, hdC] at h1
    rw [hdb] at h1
    rw [hgi]
    apply mul_right_cancel₀ hNc0
    rw [Finset.sum_mul]
    exact Eq.trans (Finset.sum_congr rfl fun J _ => by ring) (h1.trans (mul_comm _ _))
  have hgd : ∀ k, g k = d k := by
    intro k
    have hg1 : g k ∈ Submodule.span ℤ (Set.range b) := by
      rw [hbC, hg]
      refine Submodule.sum_mem _ fun J _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)
    have hd1 : d k ∈ Submodule.span ℤ (Set.range b) := by
      have h2 : d k ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
        rw [GlobalTheory.StdDual.weyl_intQ, ← hd]
        exact Submodule.subset_span ⟨k, rfl⟩
      have h3 := Submodule.map_mono (f := Formalism.GradedWeylDivisibility.intQ N N) (Formalism.GradedWeylDivisibility.weylLeDual ℤ N N le_rfl _ hanti) h2
      rwa [GlobalTheory.StdDual.dualWeyl_intQ, ← hb] at h3
    have hx := Submodule.sub_mem _ hg1 hd1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have horth : ∀ i, Formalism.GradedWeylDivisibility.fockQ (g k - d k) (b i) = 0 := by
      intro i
      rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← fockQRight_apply, map_sub, fockQRight_apply, fockQRight_apply, key,
        ← (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, hdb]
      split_ifs with h1 h2 h2 <;> first | rfl | simp | (exact absurd h1.symm h2) | (exact absurd h2.symm h1)
    have h0 : Formalism.GradedWeylDivisibility.fockQ (g k - d k) (g k - d k) = 0 := by
      rw [← fockQRight_apply]
      nth_rewrite 2 [← ha]
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, fockQRight_apply, horth, smul_zero]
    by_contra hne
    exact (ne_of_gt ((Formalism.GradedWeylDivisibility.fockQPos _ (g k - d k) (g k - d k)).2 (sub_ne_zero.mpr hne))) h0
  refine ⟨Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r), inferInstance, inferInstance, b, g, c, d', Nc, hNc0,
    hcQ, hdQ, fun k => rfl, key, ?_⟩
  have : g = d := funext hgd
  rw [this, hd, GlobalTheory.StdDual.weyl_intQ]

end GlobalTheory.WeylLatDualProof
