import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ClosureBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.StarMap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mem_closureIdeal_of_mem {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (S : Set (MonoidAlgebra A G)) (x : MonoidAlgebra A G) (hx : x ∈ S) : x ∈ closureIdeal I S := by
  unfold closureIdeal
  simp only [TwoSidedIdeal.mem_iInf]
  intro N H
  exact TwoSidedIdeal.subset_span (Or.inl (Or.inl hx))

theorem UpperTheory.V.Pa.BC.mem_span_map_e0ker_of_pair_maps :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n) (B B' : Type) [CommRing B] [Algebra O B] [IsCO O B] [CommRing B'] [Algebra O' B'] [IsCO O' B'] (u : Pair r B) (u' : Pair r' B') (g : B →+* B') [IsLocalHom g], PhiCond F.G₀ l → (∀ w, r'.Ip w = r.Ip w) → (∀ a : ℤ_[l], g (algebraMap O B (algebraMap ℤ_[l] O a)) = algebraMap O' B' (algebraMap ℤ_[l] O' a)) → u.Maps g u'.D u'.ψ → ∀ z ∈ augmentationIdealKernel u', z ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom F.G₀ g '' augmentationIdealKernel u) := by
  intro l _ F O O' _ _ _ _ _ _ _ _ n r r' B B' _ _ _ _ _ _ u u' g _ hPhi hIp hg hM z hz
  obtain ⟨hD, hψ⟩ := hM
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨hfin, ⟨χ, h, hmap, hmf⟩, -⟩ := BC.pair_mf l F O n r B u hPhi
  haveI := hfin
  obtain ⟨-, hstar, hoEl⟩ := BC.star_map l F O O' B B' g hg
  have hz' : z ∈ (u.D.map g).chBar (pairGens u') := by
    rw [hD]
    exact hz
  have hψ' : ∀ v, u'.ψ v = fun i => pushCh g (u.ψ v i) := fun v => funext fun i => (hψ v i).symm
  have hin : ∀ x ∈ pairGens u, MonoidAlgebra.mapRingHom F.G₀ g x ∈
      TwoSidedIdeal.span (MonoidAlgebra.mapRingHom F.G₀ g '' {y | y ∈ u.D.chBar (pairGens u)}) :=
    fun x hx => TwoSidedIdeal.subset_span ⟨x, mem_closureIdeal_of_mem _ _ x (Or.inr hx), rfl⟩
  refine BC.closure_bc n h B B' F.G₀ u.D χ u.cont hmap hmf g (pairGens u) (pairGens u') ?_ z hz'
  intro y hy
  rcases hy with ⟨v, γ, hy | hy⟩ | ⟨w, γ, hγ, hy | hy⟩
  · have e := hin (F.oEl v (u.ψ v) γ) (Or.inl ⟨v, γ, Or.inl rfl⟩)
    rwa [hoEl, ← hψ', ← hy] at e
  · have e := hin (F.star O B n (F.oEl v (u.ψ v) γ)) (Or.inl ⟨v, γ, Or.inr rfl⟩)
    rwa [hstar, hoEl, ← hψ', ← hy] at e
  · rw [hIp] at hγ
    have e := hin (MonoidAlgebra.single γ 1 - 1) (Or.inr ⟨w, γ, hγ, Or.inl rfl⟩)
    rwa [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one, ← hy] at e
  · rw [hIp] at hγ
    have e := hin (F.star O B n (MonoidAlgebra.single γ 1) - 1) (Or.inr ⟨w, γ, hγ, Or.inr rfl⟩)
    rwa [map_sub, map_one, hstar, MonoidAlgebra.mapRingHom_single, map_one, ← hy] at e
