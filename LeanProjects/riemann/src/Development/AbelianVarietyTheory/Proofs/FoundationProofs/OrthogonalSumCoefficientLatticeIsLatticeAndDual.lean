import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualETwo
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.SumLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

def valEquiv (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) : (Fin N → K) ≃ₗ[K] (C → VV K lam) :=
  LinearEquiv.ofBijective (LinearMap.pi fun c => valAt lam e c) (Model.valAt_bijective lam e)

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.idx_nonempty (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : Nonempty (_root_.Formalism.L2.DIV.VVIdx lam) := by
  have hne : (_root_.Formalism.L2.Col.extV ℚ lam : _root_.Formalism.L2.DIV.VV ℚ lam) ≠ 0 := by
    intro h
    apply _root_.Formalism.L2.Col.evV_extV_ne_zero (E := ℚ) (fun _ => RingHom.id ℚ) (1 : Matrix (Fin n) (Fin n) ℚ) lam
      (Rat.castHom ℂ)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})
    rw [h]
    exact map_zero _
  haveI : Nontrivial (_root_.Formalism.L2.DIV.VV ℚ lam) := nontrivial_of_ne _ _ hne
  exact (_root_.Formalism.L2.DIV.bVV ℚ lam).index_nonempty

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat [Finite C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)) (hT : ∀ c, Submodule.IsLattice K (T c)) :
    Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) := by
  classical
  haveI := Fintype.ofFinite C
  set f := _root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e with hf
  let g : C → _root_.Formalism.L2.DIV.VV K lam →ₗ[K] (Fin N → K) := fun c =>
    f.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : C => _root_.Formalism.L2.DIV.VV K lam) c
  have hval : ∀ c c' t, _root_.GlobalTheory.TestLat.valAt lam e c' (g c t) = (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
    intro c c' t
    have h := congrFun (f.apply_symm_apply (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam)) c'
    exact h
  have hsum : ∀ u, ∑ c, g c (_root_.GlobalTheory.TestLat.valAt lam e c u) = u := by
    intro u
    apply f.injective
    rw [map_sum]
    have h : ∀ c, f (g c (_root_.GlobalTheory.TestLat.valAt lam e c u)) =
        Pi.single c (_root_.GlobalTheory.TestLat.valAt lam e c u) := fun c => f.apply_symm_apply _
    simp only [h]
    exact Finset.univ_sum_single (fun c => _root_.GlobalTheory.TestLat.valAt lam e c u)
  set L : Submodule (𝓞 K) (Fin N → K) := ⨆ c, (T c).map ((g c).restrictScalars (𝓞 K)) with hL
  have hP : _root_.GlobalTheory.TestLat.sumLat lam e T = L := by
    apply le_antisymm
    · intro u hu
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hu
      rw [← hsum u]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem (hu c))
    · rw [hL, iSup_le_iff]
      intro c
      rw [Submodule.map_le_iff_le_comap]
      intro t ht
      rw [Submodule.mem_comap, _root_.GlobalTheory.TestLat.Model.mem_sumLat]
      intro c'
      rw [LinearMap.restrictScalars_apply, hval]
      by_cases hc : c' = c
      · subst hc
        rw [Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hc]
        exact zero_mem _
  have key : ∀ c, ∀ t ∈ Submodule.span K (T c : Set (_root_.Formalism.L2.DIV.VV K lam)),
      g c t ∈ Submodule.span K (L : Set (Fin N → K)) := by
    intro c t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem hx))
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  rw [hP]
  refine ⟨Submodule.fg_iSup _ fun c => ((hT c).fg).map _, ?_⟩
  rw [eq_top_iff]
  intro u _
  rw [← hsum u]
  refine Submodule.sum_mem _ fun c _ => key c _ ?_
  rw [(hT c).span_eq_top]
  trivial

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in

theorem _root_.GlobalTheory.TestLat.SumLat.sumLat_lattice_dual : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (C : Type) [Nonempty C]
    (N : ℕ) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)),
    (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) ∧
      0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) →
        _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) (_root_.GlobalTheory.TestLat.sumLat lam e T) =
          _root_.GlobalTheory.TestLat.sumLat lam e fun c => _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) := by
  intro K _ _ _ ι _ n lam C _ N e T hT
  classical
  obtain ⟨i₀⟩ := _root_.GlobalTheory.TestLat.SumLat.idx_nonempty lam
  haveI : Finite (C × _root_.Formalism.L2.DIV.VVIdx lam) := Finite.of_equiv _ e
  haveI : Finite C :=
    Finite.of_surjective (fun p : C × _root_.Formalism.L2.DIV.VVIdx lam => p.1) (fun c => ⟨(c, i₀), rfl⟩)
  haveI : Fintype C := Fintype.ofFinite C
  refine ⟨_root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat lam e T hT, ?_, ?_⟩
  · obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
    refine Nat.pos_of_ne_zero fun h => ?_
    subst h
    exact (e.symm (c₀, i₀)).elim0
  · intro G _
    ext x
    rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
    have hmemD : ∀ L : Submodule (𝓞 K) (Fin N → K), x ∈ _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) L ↔
        ∀ y ∈ L, star y ⬝ᵥ _root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ x ∈ (1 : Submodule (𝓞 K) K) :=
      fun _ => Iff.rfl
    have hmemV : ∀ (c : C) (v : _root_.Formalism.L2.DIV.VV K lam), v ∈ _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) ↔
        ∀ z ∈ T c, _root_.Formalism.L2.DIV.pairK lam G z v ∈ (1 : Submodule (𝓞 K) K) := by
      intro c v
      unfold _root_.Formalism.HermitianLatticesTheory.dual _root_.Formalism.E.hdual
      simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    rw [hmemD]
    simp_rw [_root_.GlobalTheory.TestLat.Model.sumGram_form, hmemV]
    constructor
    · intro h c z hz
      set y := (_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).symm (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) with hydef
      have hy : ∀ c', _root_.GlobalTheory.TestLat.valAt lam e c' y = (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
        intro c'
        have h' := congrFun
          ((_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).apply_symm_apply (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam)) c'
        exact h'
      have hyL : y ∈ _root_.GlobalTheory.TestLat.sumLat lam e T := by
        rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        rw [hy]
        by_cases hc : c' = c
        · subst hc
          rw [Pi.single_eq_same]
          exact hz
        · rw [Pi.single_eq_of_ne hc]
          exact zero_mem _
      have hsum := h y hyL
      rwa [Finset.sum_eq_single c
        (fun c' _ hc => by rw [hy, Pi.single_eq_of_ne hc, map_zero, LinearMap.zero_apply])
        (by simp), hy, Pi.single_eq_same] at hsum
    · intro h y hy
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hy
      exact Submodule.sum_mem _ fun c _ => h c _ (hy c)

end GlobalTheory.TestLat.SumLat
