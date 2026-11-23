import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.AbsSumP
end PositivityTheory.Rg.BcB.G3.AbsSumP

theorem PositivityTheory.Rg.BcB.G3.absSum_pf : PositivityTheory.Rg.BcB.G3.AbsSum := by
  intro V C S L A o f D loc m N hA ho hf hD hN hcard
  set T : Set V := {v | ¬ ∀ l ∈ A v, f v l = if l = o v then 1 else 0} with hTdef
  have hT : T.Finite := Filter.eventually_cofinite.mp hf
  let _ : ∀ v, Fintype (A v) := fun v => (hA v).fintype
  obtain ⟨U, hUS, hgood⟩ : ∃ U : Finset V, (∀ v ∈ U, v ∈ S) ∧
      ∀ v, v ∈ S → v ∉ U → ∀ l ∈ A v, f v l = if l = o v then 1 else 0 := by
    refine ⟨hT.toFinset.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2, ?_⟩
    intro v hvS hvU
    by_contra h
    exact hvU (Finset.mem_filter.mpr ⟨hT.mem_toFinset.mpr h, hvS⟩)
  have hkey : ∀ c ∈ D, (∏ᶠ v ∈ S, f v (loc c v)) =
      if (∀ v ∈ S, v ∉ U → loc c v = o v) then ∏ v ∈ U, f v (loc c v) else 0 := by
    intro c hc
    obtain ⟨hcA, hcf⟩ := hD c hc
    have hW : {v | ¬ loc c v = o v}.Finite := Filter.eventually_cofinite.mp hcf
    obtain ⟨F, hUF, hFS, hWF⟩ : ∃ F : Finset V, U ⊆ F ∧ (↑F : Set V) ⊆ S ∧
        ∀ v ∈ S, ¬ loc c v = o v → v ∈ F := by
      refine ⟨U ∪ hW.toFinset.filter (fun v => v ∈ S), Finset.subset_union_left, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hv) with hv | hv
        · exact hUS v hv
        · exact (Finset.mem_filter.mp hv).2
      · intro v hvS hne
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW.mem_toFinset.mpr hne, hvS⟩)
    have hsupp : S ∩ Function.mulSupport (fun v => f v (loc c v)) ⊆ ↑F := by
      rintro v ⟨hvS, hv1⟩
      rw [Function.mem_mulSupport] at hv1
      rw [Finset.mem_coe]
      by_cases hvU : v ∈ U
      · exact hUF hvU
      · apply hWF v hvS
        intro heq
        apply hv1
        rw [hgood v hvS hvU _ (hcA v), if_pos heq]
    rw [finprod_mem_eq_prod_of_subset _ hsupp hFS]
    rw [← Finset.prod_sdiff hUF]
    have hrest : ∀ v ∈ F \ U, f v (loc c v) = if loc c v = o v then 1 else 0 := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      exact hgood v (hFS hv.1) hv.2 _ (hcA v)
    rw [Finset.prod_congr rfl hrest, Finset.prod_boole]
    have hiff : (∀ v ∈ F \ U, loc c v = o v) ↔ (∀ v ∈ S, v ∉ U → loc c v = o v) := by
      constructor
      · intro h v hvS hvU
        by_contra hne
        exact hne (h v (Finset.mem_sdiff.mpr ⟨hWF v hvS hne, hvU⟩))
      · intro h v hv
        rw [Finset.mem_sdiff] at hv
        exact h v (hFS hv.1) hv.2
    by_cases hc' : ∀ v ∈ S, v ∉ U → loc c v = o v
    · rw [if_pos (hiff.mpr hc'), if_pos hc', one_mul]
    · rw [if_neg (fun h => hc' (hiff.mp h)), if_neg hc', zero_mul]
  let zmap : C → ((v : U) → A v.1) := fun c v =>
    if h : loc c v.1 ∈ A v.1 then ⟨loc c v.1, h⟩ else ⟨o v.1, ho v.1⟩
  let yz : ((v : U) → A v.1) → (∀ v, L v) := fun z v => if h : v ∈ U then (z ⟨v, h⟩).1 else o v
  have hyz_ok : ∀ z, (∀ v, yz z v ∈ A v) ∧ (∀ᶠ v in cofinite, yz z v = o v) := by
    intro z
    refine ⟨fun v => ?_, ?_⟩
    · dsimp only [yz]
      split_ifs with h
      · exact (z ⟨v, h⟩).2
      · exact ho v
    · rw [Filter.eventually_cofinite]
      apply (U.finite_toSet).subset
      intro v hv
      by_contra hvU
      exact hv (by dsimp only [yz]; rw [dif_neg (fun h => hvU (Finset.mem_coe.mpr h))])
  have hfibfin : ∀ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}.Finite := by
    intro z
    have h := hcard (yz z) (hyz_ok z).1 (hyz_ok z).2
    have hne : Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact hN h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  set G : Set C := {c | c ∈ D ∧ ∀ v ∈ S, v ∉ U → loc c v = o v} with hGdef
  have hGsub : G ⊆ ⋃ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    rintro c ⟨hcD, hc⟩
    refine Set.mem_iUnion.mpr ⟨zmap c, hcD, fun v hvS => ?_⟩
    dsimp only [yz, zmap]
    by_cases hvU : v ∈ U
    · rw [dif_pos hvU, dif_pos ((hD c hcD).1 v)]
    · rw [dif_neg hvU]; exact hc v hvS hvU
  have hGfin : G.Finite := (Set.finite_iUnion hfibfin).subset hGsub
  have hsuppG : ∀ c, c ∈ D → (∏ᶠ v ∈ S, f v (loc c v)) ≠ 0 → c ∈ G := by
    intro c hcD hne
    rw [hkey c hcD] at hne
    by_contra hcG
    apply hne
    rw [if_neg]
    intro h; exact hcG ⟨hcD, h⟩
  refine ⟨hGfin.subset (fun c hc => hsuppG c hc.1 hc.2), ?_⟩
  have hsum1 : (∑ᶠ c : C, if c ∈ D then ∏ᶠ v ∈ S, f v (loc c v) else 0) =
      ∑ c ∈ hGfin.toFinset, ∏ v : U, f v.1 (zmap c v).1 := by
    rw [finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset) ?_]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨hcD, hcG⟩ := hc
      rw [if_pos hcD, hkey c hcD, if_pos hcG, ← Finset.prod_coe_sort U (fun v => f v (loc c v))]
      apply Finset.prod_congr rfl
      intro v _
      dsimp only [zmap]
      rw [dif_pos ((hD c hcD).1 v.1)]
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      by_cases hcD : c ∈ D
      · rw [if_pos hcD] at hc; exact hsuppG c hcD hc
      · rw [if_neg hcD] at hc; exact absurd rfl hc
  have hmem : ∀ z c, (c ∈ hGfin.toFinset ∧ zmap c = z) ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v) := by
    intro z c
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hcD, hcG⟩, hzc⟩
      refine ⟨hcD, fun v hvS => ?_⟩
      dsimp only [yz]
      by_cases hvU : v ∈ U
      · rw [dif_pos hvU, ← hzc]
        dsimp only [zmap]
        rw [dif_pos ((hD c hcD).1 v)]
      · rw [dif_neg hvU]; exact hcG v hvS hvU
    · rintro ⟨hcD, hc⟩
      refine ⟨⟨hcD, fun v hvS hvU => ?_⟩, ?_⟩
      · rw [hc v hvS]; dsimp only [yz]; rw [dif_neg hvU]
      · funext v
        apply Subtype.ext
        dsimp only [zmap]
        rw [dif_pos ((hD c hcD).1 v.1)]
        show loc c v.1 = (z v).1
        rw [hc v.1 (hUS v.1 v.2)]
        dsimp only [yz]
        rw [dif_pos v.2]
  have hcardfib : ∀ z (s' : Finset C), (∀ c, c ∈ s' ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)) →
      s'.card = Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    intro z s' hs'
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hs')
  rw [hsum1, ← Finset.sum_fiberwise hGfin.toFinset zmap (fun c => ∏ v : U, f v.1 (zmap c v).1),
    Finset.sum_mul]
  rw [Finset.sum_congr rfl (g := fun z => (N : ℂ) * ∏ v : U, f v.1 (z v).1) ?_, ← Finset.mul_sum]
  swap
  · intro z _
    rw [Finset.sum_congr rfl (g := fun _ => ∏ v : U, f v.1 (z v).1) ?_, Finset.sum_const, nsmul_eq_mul,
      mul_right_comm]
    swap
    · intro c hc
      rw [(Finset.mem_filter.mp hc).2]
    congr 1
    rw [← hcard (yz z) (hyz_ok z).1 (hyz_ok z).2, Nat.cast_mul,
      hcardfib z _ (fun c => Finset.mem_filter.trans (hmem z c))]
  congr 1
  have hR : ∀ v, (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = ∑ l : A v, f v l.1 := by
    intro v
    rw [finsum_eq_sum_of_support_subset _ (s := (A v).toFinset) ?_,
      Finset.sum_set_coe (f := fun l => f v l)]
    · exact Finset.sum_congr rfl (fun l hl => if_pos (Set.mem_toFinset.mp hl))
    · intro l hl
      rw [Function.mem_support] at hl
      rw [Set.coe_toFinset]
      by_contra h
      exact hl (if_neg h)
  have hR1 : ∀ v, v ∈ S → v ∉ U → (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = 1 := by
    intro v hvS hvU
    rw [hR, Finset.sum_set_coe (f := fun l => f v l),
      Finset.sum_congr rfl (fun l hl => hgood v hvS hvU l (Set.mem_toFinset.mp hl)), Finset.sum_ite_eq',
      if_pos (Set.mem_toFinset.mpr (ho v))]
  rw [← Fintype.prod_sum (fun (v : U) (l : A v.1) => f v.1 l.1)]
  rw [finprod_mem_eq_prod_of_subset _ (t := U) ?_ ?_]
  · rw [← Finset.prod_coe_sort U]
    exact Finset.prod_congr rfl (fun v _ => (hR v.1).symm)
  · rintro v ⟨hvS, hv1⟩
    by_contra hvU
    rw [Function.mem_mulSupport] at hv1
    exact hv1 (hR1 v hvS hvU)
  · intro v hv
    exact hUS v hv
