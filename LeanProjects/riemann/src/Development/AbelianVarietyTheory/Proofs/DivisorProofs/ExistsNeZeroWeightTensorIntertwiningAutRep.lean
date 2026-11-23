import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem exists_ne_zero_wsp_intertwining : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    (∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) →
    ∃ T : Wsp lam →ₗ[ℂ] (UA E n → ℂ), T ≠ 0 ∧ (∀ w, T w ∈ π) ∧
      ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w) := by
  intro E _ _ _ n lam π hπ hW
  let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n := fun v => (embU n v.embedding).subtype
  let σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (lam v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (lam v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    obtain ⟨h1, h2⟩ := (CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (lam v))
    refine (CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have := hS x w hw
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding (x : UA E n)) w ∈ S at this
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding])
      _ a.2 _ b.2
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π'.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π' v.embedding (lam v) (hW v)
  haveI : Nontrivial π'.V := Submodule.nontrivial_iff_ne_bot.2 π'.isAut.ne_bot
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π'.V (fun v => embU n v.embedding)
    (fun v => nablaSq ℂ n (lam v)) π'.rep s σ inferInstance hirr hcomm hspan
  let T : Wsp lam →ₗ[ℂ] (UA E n → ℂ) := π.subtype ∘ₗ PiTensorProduct.lift F
  have hT : ∀ u, T (PiTensorProduct.tprod ℂ u) = (F u).1 := fun u => by
    simp only [T, LinearMap.comp_apply, PiTensorProduct.lift.tprod]
    rfl
  obtain ⟨u0, hu0⟩ : ∃ u, F u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF0 (MultilinearMap.ext h)
  refine ⟨T, fun h => hu0 ?_, fun w => (PiTensorProduct.lift F w).2, fun x hx w => ?_⟩
  · apply Subtype.ext
    rw [← hT, h]
    rfl
  · obtain ⟨y, hy, hyc, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx
    let y' : ∀ v : InfinitePlace E, embU n v.embedding := fun v => ⟨y v, hy v⟩
    have key : ∀ u, T (wInf lam x (PiTensorProduct.tprod ℂ u)) = RU E n x (T (PiTensorProduct.tprod ℂ u)) := by
      intro u
      have h1 := GlobalTheory.DefU.prod_list_apply_multilinear π'.rep s σ F hF y' u Finset.univ.toList
        (Finset.nodup_toList _)
      have h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x := hprod
      rw [h2] at h1
      simp only [Finset.mem_toList, Finset.mem_univ, if_true] at h1
      have h3 : wInf lam x (PiTensorProduct.tprod ℂ u) =
          PiTensorProduct.tprod ℂ (fun v => σ v (y' v) (u v)) := by
        change PiTensorProduct.map _ _ = _
        rw [PiTensorProduct.map_tprod]
        refine congrArg _ (funext fun v => ?_)
        change _ = GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding (y v)) (u v)
        rw [hyc v]
      rw [h3, hT, hT, ← h1]
      rfl
    have hext : T ∘ₗ wInf lam x = RU E n x ∘ₗ T := PiTensorProduct.ext (MultilinearMap.ext fun u => by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
      exact key u)
    exact LinearMap.congr_fun hext w

end GlobalTheory.BCT.TrKer

end
