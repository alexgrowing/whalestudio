import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IrredOfAbsIrred

theorem isIrred_of_absIrrSub :
    ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), AbsIrrSub ρ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ a ρ h
  classical
  obtain ⟨h0, -, h2⟩ := h
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  have hinj : Function.Injective f := f.injective
  refine ⟨fun hb => h0 ?_, fun U hU => ?_⟩
  · rw [hb, Submodule.span_eq_bot]
    rintro _ ⟨v, hv, rfl⟩
    have : v = 0 := by simpa using hv
    subst this
    ext x
    simp
  · have hst : IsInv (mapRep f ρ) (Submodule.span K ((fun v : Fin a → k => f ∘ v) '' (U : Set (Fin a → k)))) := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        refine Submodule.subset_span ⟨(ρ g : Matrix (Fin a) (Fin a) k).mulVec u, hU g u hu, ?_⟩
        ext p
        exact RingHom.map_mulVec f _ u p
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
    rcases h2 _ (Submodule.span_mono (Set.image_mono (fun _ _ => trivial))) hst with h1 | h1
    · left
      rw [Submodule.span_eq_bot] at h1
      rw [eq_bot_iff]
      intro v hv
      have := h1 _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_bot]
      ext p
      apply hinj
      simpa using congrFun this p
    · right
      by_contra hne
      obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
      let F : (Fin a → K) →ₗ[K] K :=
        { toFun := fun X => ∑ i, X i * f (φ (Pi.single i 1))
          map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun c X => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
            exact (Finset.mul_sum _ _ _).symm }
      have hF : ∀ X : Fin a → k, F (f ∘ X) = f (φ X) := by
        intro X
        conv_rhs => rw [← Finset.univ_sum_single X]
        simp only [map_sum]
        change ∑ i, f (X i) * f (φ (Pi.single i 1)) = _
        refine Finset.sum_congr rfl fun i _ => ?_
        have : Pi.single i (X i) = X i • (Pi.single i (1 : k) : Fin a → k) := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [this, map_smul, smul_eq_mul, map_mul]
      have hker : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' (U : Set (Fin a → k))) ≤
          LinearMap.ker F := by
        rw [Submodule.span_le]
        rintro _ ⟨u, hu, rfl⟩
        have : φ u = 0 := hφ hu
        simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
      apply hφ0
      refine LinearMap.ext fun X => ?_
      have h3 : F (f ∘ X) = 0 := hker (by rw [h1]; exact Submodule.subset_span ⟨X, trivial, rfl⟩)
      rw [hF] at h3
      exact hinj (by rw [h3]; simp)

end GlobalTheory.IrredOfAbsIrred
