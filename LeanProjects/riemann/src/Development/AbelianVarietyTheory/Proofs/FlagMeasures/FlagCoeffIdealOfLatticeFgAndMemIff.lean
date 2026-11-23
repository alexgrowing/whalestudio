import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia

open NumberField

namespace GlobalTheory.RowLatXS

private theorem coefX_add_flag_measures {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) {x y : S.V}
    (hx : x ∈ Submodule.span E (Set.range F.e)) (hy : y ∈ Submodule.span E (Set.range F.e)) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  have hxy : x + y ∈ Submodule.span E (Set.range F.e) := Submodule.add_mem _ hx hy
  unfold Formalism.MainNotions.S.FlagG.coefX
  rw [dif_pos hx, dif_pos hy, dif_pos hxy]
  have hsum : (⟨x + y, hxy⟩ : Submodule.span E (Set.range F.e)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [hsum, map_add, Finsupp.add_apply]

private theorem coefX_smul_flag_measures {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) (c : E) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range F.e)) :
    F.coefX (c • x) a = c * F.coefX x a := by
  have hcx : c • x ∈ Submodule.span E (Set.range F.e) := Submodule.smul_mem _ c hx
  unfold Formalism.MainNotions.S.FlagG.coefX
  rw [dif_pos hx, dif_pos hcx]
  have hprod : (⟨c • x, hcx⟩ : Submodule.span E (Set.range F.e)) = c • ⟨x, hx⟩ := rfl
  rw [hprod, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem Ia_fg_and_mem_iff {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ)
    (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r) (hΛ : Λ.FG) :
    (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔
      ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  classical
  have hXle : F.Xa (a.val + 1) ≤ Submodule.span E (Set.range F.e) := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.span_mono (Set.image_subset_range _ _)

  let W : Submodule (𝓞 E) S.V := Λ ⊓ (F.Xa (a.val + 1)).restrictScalars (𝓞 E)
  have hmem : ∀ x : W, (x : S.V) ∈ Submodule.span E (Set.range F.e) := fun x =>
    hXle ((Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_inf.1 x.2).2)
  let g : W →ₗ[𝓞 E] E :=
    { toFun := fun x => F.coefX (x : S.V) a
      map_add' := fun x y => coefX_add_flag_measures F a (hmem x) (hmem y)
      map_smul' := fun c x => by
        change F.coefX (c • (x : S.V)) a = c • F.coefX (x : S.V) a
        rw [← algebraMap_smul E c (x : S.V), coefX_smul_flag_measures F a _ (hmem x), Algebra.smul_def] }
  have hrange : ∀ t : E, t ∈ LinearMap.range g ↔
      ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
    intro t
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (Submodule.mem_inf.1 x.2).1, (Submodule.mem_inf.1 x.2).2, rfl⟩
    · rintro ⟨x, hx, hxa, rfl⟩
      exact ⟨⟨x, Submodule.mem_inf.2 ⟨hx, hxa⟩⟩, rfl⟩

  have hIa : GlobalTheory.RowLatXS.Ia Λ F a = LinearMap.range g := by
    unfold GlobalTheory.RowLatXS.Ia
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hrange t).2 ht
    · intro t ht
      exact Submodule.subset_span ((hrange t).1 ht)
  refine ⟨?_, fun t => by rw [hIa]; exact hrange t⟩

  have : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  have : IsNoetherian (𝓞 E) W := isNoetherian_of_le inf_le_left
  rw [hIa, LinearMap.range_eq_map]
  exact (IsNoetherian.noetherian (⊤ : Submodule (𝓞 E) W)).map g

end GlobalTheory.RowLatXS
