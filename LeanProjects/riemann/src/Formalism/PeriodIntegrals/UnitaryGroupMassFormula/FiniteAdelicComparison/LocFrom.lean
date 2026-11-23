import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem ratV_add' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (a b : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (a + b) = Formalism.L2.SG.Sub.ratV (F := F) R a + Formalism.L2.SG.Sub.ratV (F := F) R b := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]

theorem ratV_zero' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} : Formalism.L2.SG.Sub.ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]

theorem ratV_zsmul' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (k : ℤ) (a : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (k • a) = k • Formalism.L2.SG.Sub.ratV (F := F) R a := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]

theorem psiV_entry (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : Formalism.MainNotions.S.Af I.F) (e : I.E) :
    psiV I v (((1 : I.E) ⊗ₜ[I.F] a) * (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a) ⊗ₜ[I.F] e := by
  simp [psiV, Algebra.TensorProduct.tmul_mul_tmul]

theorem smul_one_tmul' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : v.adicCompletionIntegers I.F)
    (e : I.E) :
    r • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] e) = ((r : v.adicCompletion I.F) ⊗ₜ[I.F] e) := by
  rw [TensorProduct.smul_tmul']
  congr 1
  rw [Algebra.smul_def, mul_one]
  rfl

theorem memLocFrom_of (hI : InjV) : MemLocFrom := by
  intro I x hx
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) I.L_fg
  let g : s → (Fin I.n → I.E) := fun j => (j : Fin I.n → I.E)
  have hgL : ∀ j, g j ∈ I.L := fun j => by
    have : (j : Fin I.n → I.E) ∈ I.L.restrictScalars ℤ := hs ▸ Submodule.subset_span j.2
    exact this
  have hloc : ∀ v : HeightOneSpectrum (𝓞 I.F), ∃ c : s → v.adicCompletionIntegers I.F,
      ∑ j, c j • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (g j) = vecV I v x := by
    intro v
    rw [← Submodule.mem_span_range_iff_exists_fun]
    have hle : Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) ≤
        Submodule.span (v.adicCompletionIntegers I.F)
          (Set.range fun j => Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (g j)) := by
      rw [Formalism.L2.SG.Sub.latLoc, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      have hl' : l ∈ Submodule.span ℤ (s : Set (Fin I.n → I.E)) := by rw [hs]; exact hl
      clear hl
      induction hl' using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
      | zero => rw [ratV_zero']; exact zero_mem _
      | add a b _ _ ha hb => rw [ratV_add']; exact add_mem ha hb
      | smul k a _ ha => rw [ratV_zsmul']; exact zsmul_mem ha k
    exact hle (hx v)
  choose c hc using hloc
  let α : s → Formalism.MainNotions.S.Af I.F := fun j =>
    RestrictedProduct.mk (fun v => ((c v j : v.adicCompletionIntegers I.F) : v.adicCompletion I.F))
      (Filter.Eventually.of_forall fun v => (c v j).2)
  have hαint : ∀ j, α j ∈ Formalism.UG.intAd I.F := fun j v => (c v j).2
  have hαmem : ∀ j, (1 : I.E) ⊗ₜ[I.F] α j ∈ Formalism.MainNotions.S.IntAf I.F I.E := fun j =>
    Subring.subset_closure (Or.inr ⟨⟨α j, hαint j⟩, rfl⟩)
  let y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
    ∑ j, (⟨_, hαmem j⟩ : Formalism.MainNotions.S.IntAf I.F I.E) •
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (g j i))
  have hy : y ∈ I.Lf := Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g j, hgL j⟩, rfl⟩)
  have hyx : y = x := by
    funext i
    rw [← sub_eq_zero]
    apply hI I
    intro v
    rw [map_sub, sub_eq_zero]
    have hci := congrFun (hc v) i
    simp only [vecV] at hci
    rw [← hci]
    simp only [y, Finset.sum_apply, map_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subring.smul_def, smul_eq_mul]
    change psiV I v (((1 : I.E) ⊗ₜ[I.F] α j) * (g j i ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) = _
    rw [psiV_entry]
    change _ = c v j • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] g j i)
    rw [smul_one_tmul']
    rfl
  exact hyx ▸ hy

end PI.FinKW
