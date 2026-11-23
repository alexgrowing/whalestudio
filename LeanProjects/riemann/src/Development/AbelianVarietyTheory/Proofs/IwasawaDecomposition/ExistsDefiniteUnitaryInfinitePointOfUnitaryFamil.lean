import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InfSurj

theorem list_prod_single {G ι : Type} [Monoid G] [DecidableEq ι] (v : ι) (a : G) :
    ∀ l : List ι, l.Nodup → v ∈ l → (l.map fun u => if u = v then a else 1).prod = a
  | [], _, h => absurd h List.not_mem_nil
  | u :: l, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.prod_cons]
    by_cases hu : u = v
    · subst hu
      have : (l.map fun w => if w = u then a else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun w hw => if_neg fun (e : w = u) => hn.1 (e ▸ hw)
      rw [if_pos rfl, this, List.prod_map_one, mul_one]
    · rw [if_neg hu, one_mul]
      exact list_prod_single v a l hn.2 ((List.mem_cons.1 h).resolve_left (Ne.symm hu))

end GlobalTheory.InfSurj

theorem GlobalTheory.InfSurj.exists_infU_cAll_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  intro E _ _ _ n g hg
  classical
  have he := fun v : InfinitePlace E => GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
  choose e he using he
  let y : InfinitePlace E → UA E n := fun v => ((e v).symm ⟨(g v : Matrix (Fin n) (Fin n) ℂ), hg v⟩ : embU n v.embedding)
  have hy : ∀ v, y v ∈ embU n v.embedding := fun v => ((e v).symm _).2
  have hyv : ∀ v, cEmb v.embedding (y v) = g v := fun v => by
    rw [← he v, ContinuousMulEquiv.apply_symm_apply]
    ext i j
    rfl
  have hyu : ∀ u v, u ≠ v → cEmb v.embedding (y u) = 1 := fun u v huv => by
    have h := (Subgroup.mem_inf.1 (hy u)).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h v.embedding
    rw [Subgroup.mem_iInf] at h2
    exact h2 (by rw [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]; exact Ne.symm huv)
  refine ⟨(Finset.univ.toList.map y).prod, ?_, ?_⟩
  · refine (infU E n).list_prod_mem fun z hz => ?_
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact (Subgroup.mem_inf.1 (hy u)).1
  · funext v
    change cEmb v.embedding _ = g v
    rw [map_list_prod, List.map_map]
    have : (Finset.univ.toList.map (cEmb v.embedding ∘ y)) = Finset.univ.toList.map fun u => if u = v then g v else 1 :=
      List.map_congr_left fun u _ => by
        by_cases h : u = v
        · subst h; simp [hyv]
        · simp [h, hyu u v h]
    rw [this]
    exact GlobalTheory.InfSurj.list_prod_single v (g v) _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ v))
