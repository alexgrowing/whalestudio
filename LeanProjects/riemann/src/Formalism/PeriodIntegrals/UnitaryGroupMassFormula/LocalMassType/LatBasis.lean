import Mathlib

noncomputable section

namespace PI.LocMassTypL

open NumberField IsDedekindDomain

theorem lat_basis {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (L : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) (hfg : L.FG)
    (hsp : Submodule.span (v.adicCompletion F) (L : Set (Fin n → v.adicCompletion F)) = ⊤) :
    ∃ A : Matrix (Fin n) (Fin n) (v.adicCompletion F), IsUnit A ∧
      ∀ y, y ∈ L ↔ ∃ c : Fin n → v.adicCompletion F, (∀ i, c i ∈ v.adicCompletionIntegers F) ∧
        y = A.mulVec c := by
  classical
  haveI : Module.Finite (v.adicCompletionIntegers F) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free (v.adicCompletionIntegers F) L := Module.free_of_finite_type_torsion_free'
  obtain ⟨ι, hιf, b, hb⟩ : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι (v.adicCompletionIntegers F) L), True :=
    ⟨_, inferInstance, Module.Free.chooseBasis (v.adicCompletionIntegers F) L, trivial⟩
  obtain ⟨w, hw⟩ : ∃ w : ι → (Fin n → v.adicCompletion F), w = fun i => (b i : Fin n → v.adicCompletion F) :=
    ⟨_, rfl⟩
  have hsmul : ∀ (o : v.adicCompletionIntegers F) (x : Fin n → v.adicCompletion F),
      o • x = (o : v.adicCompletion F) • x := fun o x => rfl
  have hliO : LinearIndependent (v.adicCompletionIntegers F) w := by
    rw [hw]
    exact b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliK : LinearIndependent (v.adicCompletion F) w :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (v.adicCompletion F)).mp hliO
  have hspanO : Submodule.span (v.adicCompletionIntegers F) (Set.range w) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    rw [hw]
    exact h1
  have hspK : ⊤ ≤ Submodule.span (v.adicCompletion F) (Set.range w) := by
    rw [← hsp, Submodule.span_le]
    intro y hy
    rw [← hspanO] at hy
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers F) (v.adicCompletion F) _ hy
  let bK : Module.Basis ι (v.adicCompletion F) (Fin n → v.adicCompletion F) := Module.Basis.mk hliK hspK
  have hcard : Fintype.card ι = n := by
    have h1 := Module.finrank_eq_card_basis bK
    rw [Module.finrank_fin_fun] at h1
    exact h1.symm
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have hAv : ∀ c : Fin n → v.adicCompletion F,
      (Matrix.of fun i j => w (e j) i).mulVec c = ∑ j, c j • w (e j) := by
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨Matrix.of fun i j => w (e j) i, ?_, ?_⟩
  · have hA : (Matrix.of fun i j => w (e j) i) = (Pi.basisFun (v.adicCompletion F) (Fin n)).toMatrix (bK.reindex e.symm) := by
      refine Matrix.ext fun i j => ?_
      simp [Module.Basis.toMatrix_apply, Module.Basis.reindex_apply, bK, Module.Basis.mk_apply]
    rw [hA]
    letI := (Pi.basisFun (v.adicCompletion F) (Fin n)).invertibleToMatrix (bK.reindex e.symm)
    exact isUnit_of_invertible _
  · intro y
    constructor
    · intro hy
      refine ⟨fun j => (b.repr ⟨y, hy⟩ (e j) : v.adicCompletion F), fun j => (b.repr ⟨y, hy⟩ (e j)).2, ?_⟩
      rw [hAv]
      have h1 := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h1
      rw [← Equiv.sum_comp e] at h1
      refine (show y = _ from h1.symm).trans ?_
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Submodule.coe_smul, hsmul, hw]
    · rintro ⟨c, hc, rfl⟩
      rw [hAv, ← hspanO]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have : c j • w (e j) = (⟨c j, hc j⟩ : v.adicCompletionIntegers F) • w (e j) := by rw [hsmul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e j, rfl⟩)

end PI.LocMassTypL
