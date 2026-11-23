import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CompositeOfChainHolds
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.SplitExt

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem chain_from_primitive_data : ChainFromPrimitiveData := by
  intro O _ _ _ _ X _ T d _ _ G _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨hP, hA, h2, hG3, hε⟩ := hyp
  obtain ⟨eB, e₁, hI⟩ := idem O X T d G r π t bl χ₁ ε hP hA h2
  obtain ⟨m, jj, a, hja, hsep⟩ := x0 O X T d G r π t bl χ₁ ε hP eB e₁ hI hG3 g₀ hε L ϖ hϖ
  refine ⟨eB, e₁, fun x => ϖ ^ L • ∑ i, jj i x • (eB x * a i x * eB x),
    ⟨hI, ⟨m, jj, a, hja, rfl⟩, hsep⟩, ?_⟩
  intro O' _ _ _ _ _ _ e he hspl
  obtain ⟨b1, b2, b3, b4⟩ := bridge O X T d G r π eB hI.1 hI.2.2.1 m jj a hja (ϖ ^ L)
  obtain ⟨cP, cA, cI, cX, cv⟩ := stageC O O' e he X T d G r π t bl χ₁ ε hP hA eB e₁ hI g₀ _ b1 b2 b3 b4
    hsep hspl
  obtain ⟨D, hD, ⟨i1, i2, i3, i4, i5⟩, i3', hT⟩ := ring_objects_exist O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _
    cP cA _ _ cI g₀ _ cX
  have hpπ : D.p D.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  refine ⟨D, hD, ⟨i1, i2, i3', i4, i5, hT, fun Z => ?_⟩, fun Z => by rw [hpπ]; exact cv Z⟩
  exact displayFree O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _ cP cA _ _ cI g₀ _ cX D hD hT Z

theorem chain_with_extension_of_split (hE : StatSplitExt) : ChainWithExtension := by
  intro O _ _ _ _ X _ T d _ _ G _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, hall⟩ := chain_from_primitive_data O X T d G r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  refine ⟨eB, e₁, s, hAB, ?_⟩
  obtain ⟨hI, ⟨m, jj, a, hja, hs⟩, hsep⟩ := hAB
  obtain ⟨-, b2, b3, -⟩ := bridge O X T d G r π eB hI.1 hI.2.2.1 m jj a hja (ϖ ^ L)
  rw [← hs] at b2 b3
  let ι : O →+* FractionRing O := algebraMap O (FractionRing O)
  have hι : Function.Injective ι := IsFractionRing.injective O (FractionRing O)
  have hmon : ∀ x, (blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).Monic := by
    intro x
    have hbb : eB x * eB x = eB x := congrFun hI.2.2.1 x
    have hbs : eB x * s x = s x := congrFun b2 x
    have hsb : s x * eB x = s x := congrFun b3 x
    refine Polynomial.monic_of_injective hι ?_
    rw [blockPoly_map]
    refine (bcSplit (FractionRing O) d _ _ t ?_ ?_ ?_ (hI.2.2.2.2.2.2.1 x)).1
    · rw [← Matrix.map_mul, hbb]
    · rw [← Matrix.map_mul, mul_add, ← mul_assoc, ← mul_assoc, hbb, hbs]
    · rw [← Matrix.map_mul, add_mul, mul_assoc, hbb, hsb]
  obtain ⟨O', i1, i2, i3, i4, i5, i6, e, he, hspl⟩ := hE O X
    (fun x => blockPoly (eB x) (eB x * r g₀ x * eB x + s x)) hmon
    (fun x => by rw [blockPoly_map]; exact hsep x)
  exact ⟨O', i1, i2, i3, i4, i5, i6, e, he, hall O' e he hspl⟩

theorem chain_with_extension_holds : ChainWithExtension := chain_with_extension_of_split splitExt

end Formalism.RepresentationBoundsCohomology.ringDataObjects
