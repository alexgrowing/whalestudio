import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi

private theorem relIndex_positions {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)] (K : Subgroup G)
    (q : ∀ i, G →* A i) (j : ∀ i, A i →* G) (B N : ∀ i, Subgroup (A i)) (T : Finset ι)
    (hqj : ∀ i ∈ T, ∀ a, q i (j i a) = a)
    (hqk : ∀ i ∈ T, ∀ k ∈ T, i ≠ k → ∀ a, q k (j i a) = 1)
    (hj : ∀ i ∈ T, ∀ a ∈ B i, j i a ∈ K)
    (hq : ∀ i ∈ T, ∀ k ∈ K, q i k ∈ B i) :
    (K ⊓ ⨅ i ∈ T, (N i).comap (q i)).relIndex K = ∏ i ∈ T, (N i).relIndex (B i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have ih' := ih (fun k hk => hqj k (Finset.mem_insert_of_mem hk))
      (fun k hk l hl => hqk k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl))
      (fun k hk => hj k (Finset.mem_insert_of_mem hk))
      (fun k hk => hq k (Finset.mem_insert_of_mem hk))
    have hiT : i ∈ insert i T := Finset.mem_insert_self i T
    set L : Subgroup G := K ⊓ ⨅ k ∈ T, (N k).comap (q k) with hL
    have hins : (K ⊓ ⨅ k ∈ insert i T, (N k).comap (q k)) = L ⊓ (N i).comap (q i) := by
      rw [Finset.iInf_insert, inf_left_comm, inf_comm]
    have hmap : L.map (q i) = B i := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hq i hiT x (Subgroup.mem_inf.1 hx).1
      · intro a ha
        refine ⟨j i a, ?_, hqj i hiT a⟩
        refine Subgroup.mem_inf.2 ⟨hj i hiT a ha, ?_⟩
        simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
        intro k hk
        have hne : i ≠ k := fun h => hi (h ▸ hk)
        rw [hqk i hiT k (Finset.mem_insert_of_mem hk) hne a]
        exact (N k).one_mem
    rw [hins, Finset.prod_insert hi, ← ih',
      ← Subgroup.relIndex_mul_relIndex (L ⊓ (N i).comap (q i)) L K inf_le_left inf_le_left,
      Subgroup.inf_relIndex_left, Subgroup.relIndex_comap, hmap]

private theorem mem_Lev {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}
    (S : Set (GlobalTheory.BCT.Pl E)) (N : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (g : GF E n) :
    g ∈ Lev S N ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ N i.1 := by
  unfold Lev
  rw [Subgroup.mem_iInf]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩

theorem levIdx_pf :
    SlotBasic → LevTop → LevIdx := by
  intro hF _ E _ _ _ n S Z N hS hZ hG
  obtain ⟨-, -, h3, h4, -, -, h7⟩ := hF E n S hS
  have hK : ∀ g, g ∈ PositivityTheory.Rg.BcB.G8.Kf E n ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ GlobalTheory.LFun.KGL i.1 n := fun g => by
    rw [← h7, mem_Lev]
  have hLe : Lev S N ≤ PositivityTheory.Rg.BcB.G8.Kf E n := fun g hg =>
    (hK g).2 fun i hi => (hG i.1).2.1 ((mem_Lev S N g).1 hg i hi)
  refine ⟨hLe, ?_⟩
  have hposition : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), Sl S i := fun i hi => by
    have hw := hZ i.1 (Finset.mem_product.1 hi).1
    exact ⟨hw.1, fun _ => hw.2⟩
  have hEq : Lev S N = PositivityTheory.Rg.BcB.G8.Kf E n ⊓ ⨅ i ∈ Z ×ˢ (Finset.univ : Finset Bool),
      (N i.1).comap (qw n i.1 i.2) := by
    apply le_antisymm
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨hLe hg, ?_⟩
      simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
      exact fun i hi => (mem_Lev S N g).1 hg i (hposition i hi)
    · intro g hgg
      obtain ⟨hg, hg'⟩ := Subgroup.mem_inf.1 hgg
      simp only [Subgroup.mem_iInf, Subgroup.mem_comap] at hg'
      refine (mem_Lev S N g).2 fun i hi => ?_
      by_cases hw : i.1 ∈ Z
      · exact hg' i (Finset.mem_product.2 ⟨hw, Finset.mem_univ _⟩)
      · rw [(hG i.1).2.2.2 hw]
        exact (hK g).1 hg i hi
  have key := relIndex_positions (A := fun i : GlobalTheory.BCT.Pl E × Bool => GlobalTheory.BCT.GLw n i.1) (PositivityTheory.Rg.BcB.G8.Kf E n)
    (fun i => qw n i.1 i.2) (fun i => jw n i.1 i.2) (fun i => GlobalTheory.LFun.KGL i.1 n) (fun i => N i.1)
    (Z ×ˢ (Finset.univ : Finset Bool))
    (fun i _ a => (h3 i.1 i.2).2.2.1 a)
    (fun i hi k hk hne a => h4 i k (hposition i hi) (hposition k hk) hne a)
    (fun i hi a ha => (hK _).2 fun k hk => by
      by_cases hik : i = k
      · subst hik
        rw [(h3 i.1 i.2).2.2.1 a]
        exact ha
      · rw [h4 i k (hposition i hi) hk hik a]
        exact (GlobalTheory.LFun.KGL k.1 n).one_mem)
    (fun i hi k hk => (hK k).1 hk i (hposition i hi))
  rw [hEq, key, Finset.prod_product]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp [Fintype.prod_bool, sq]

end UpperTheory.V.Z.Mult.Pi
