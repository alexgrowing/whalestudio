import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FiniteHomOfTopFG
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem isOpen_map_of_ker_le {P Z : Type} [Group P] [TopologicalSpace P] [CompactSpace P]
    [Group Z] [TopologicalSpace Z] [T2Space Z] (f : P →* Z) (hf : Continuous f) (hs : Function.Surjective f)
    (V : Subgroup P) (hV : IsOpen (V : Set P)) (hk : f.ker ≤ V) : IsOpen (V.map f : Set Z) := by
  rw [← (hf.isClosedMap.isQuotientMap hf hs).isOpen_preimage]
  have : f ⁻¹' (V.map f : Set Z) = V := by
    rw [← Subgroup.coe_comap, Subgroup.comap_map_eq_self hk]
  rw [this]; exact hV

theorem UpperTheory.V.Pa.ker_oo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T), T.ProL → Λ.h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure := by
  intro l _ L G0 T Λ hT x hx
  set K := (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure with hK
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  refine (totallyDisconnected_quot Λ.G.Γ K (Subgroup.isClosed_topologicalClosure _)).2 x fun O => ?_
  haveI := O.isNormal'
  set W : Subgroup Λ.G.Γ := K ⊔ O.toSubgroup with hW
  haveI hWn : W.Normal := Subgroup.sup_normal _ _
  have hWo : IsOpen (W : Set Λ.G.Γ) := Subgroup.isOpen_mono (le_sup_right : O.toSubgroup ≤ W) O.isOpen'
  have hta : ∀ j, (Λ.ta j : Λ.G.Γ) ∈ W := fun j =>
    Subgroup.mem_sup_left (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨j, rfl⟩))
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := W.comap Λ.πo, isOpen' := hWo.preimage Λ.πo_cont, isNormal' := hWn.comap _ }
  have hVn : V.toSubgroup.Normal := V.isNormal'
  have hVo : IsOpen (V.toSubgroup : Set Λ.Ph) := V.isOpen'
  have hko : Λ.πo.ker ≤ V.toSubgroup := fun g hg => by
    show Λ.πo g ∈ W
    rw [MonoidHom.mem_ker.1 hg]; exact W.one_mem
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG0 : TopFG G0.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 G0.Γ (Λ.h.p.comp Λ.πo) (Λ.h.cont.comp Λ.πo_cont)
    (Λ.h.surj.comp Λ.πo_surj)
  have hidx : V.toSubgroup.index ≠ 0 := by
    haveI : Finite (Λ.Ph ⧸ V.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hVo
    exact Subgroup.index_ne_zero_of_finite
  have hfin := (finite_hom_of_topFG G0.Γ hG0).2.2 _ hidx
  have hall : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ A ∈ {H : Subgroup G0.Γ | IsOpen (H : Set G0.Γ) ∧ H.index = V.toSubgroup.index},
      A.Normal → ∀ g, (T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹ ∈ A := by
    rw [hfin.eventually_all]
    intro A hA
    by_cases hn : A.Normal
    · exact (Λ.p_lim { toSubgroup := A, isOpen' := hA.1, isNormal' := hn }).mono fun N h _ => h
    · exact Eventually.of_forall fun N h => absurd h hn
  obtain ⟨N, h1, h2, h3⟩ := ((Λ.ker_lim V).and ((Λ.ta_lim V).and hall)).exists
  have hkN : (Λ.π N).ker ≤ V.toSubgroup := le_sup_left.trans (h1.le.trans (sup_le hko le_rfl))
  haveI hVNn : (V.toSubgroup.map (Λ.π N)).Normal := hVn.map _ (Λ.π_surj N)
  have hVNo := isOpen_map_of_ker_le (Λ.π N) (Λ.π_cont N) (Λ.π_surj N) _ hVo hkN
  have hkh : (T.h N).p.ker ≤ V.toSubgroup.map (Λ.π N) := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_of_isOpen _ hVNo))
    rw [hT.2 N, sup_bot_eq]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, g', hg, hg', hgg⟩ := h2 j
    have hg'V : g' ∈ V.toSubgroup := by
      show Λ.πo g' ∈ W
      rw [hg']; exact hta j
    refine ⟨g, ?_, hg⟩
    have := mul_mem hg'V (inv_mem hgg)
    simpa using this
  let f : Λ.Ph →* G0.Γ := (T.h N).p.comp (Λ.π N)
  have hfs : Function.Surjective f := (T.h N).surj.comp (Λ.π_surj N)
  have hfk : f.ker ≤ V.toSubgroup := fun g hg => by
    rw [← Subgroup.comap_map_eq_self hkN]
    exact hkh hg
  have hAo := isOpen_map_of_ker_le f ((T.h N).cont.comp (Λ.π_cont N)) hfs _ hVo hfk
  have hAi : (V.toSubgroup.map f).index = V.toSubgroup.index := by
    rw [← Subgroup.index_comap_of_surjective _ hfs, Subgroup.comap_map_eq_self hfk]
  obtain ⟨g, rfl⟩ := Λ.πo_surj x
  have h4 := h3 _ ⟨hAo, hAi⟩ (hVn.map _ hfs) g
  rw [MonoidHom.mem_ker.1 hx, inv_one, mul_one] at h4
  have h5 : g ∈ (V.toSubgroup.map f).comap f := h4
  rw [Subgroup.comap_map_eq_self hfk] at h5
  exact h5
