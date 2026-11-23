import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TwoTorsionPointsSpreading

set_option backward.isDefEq.respectTransparency false

theorem exists_open_injective {S : Scheme.{0}} {X G : Over S} [IsIntegral X.left] [IsSeparated G.hom] {m : ℕ}
    (s : Fin m → (X ⟶ G)) (hs : Function.Injective s) :
    ∃ W : X.left.Opens, (W : Set X.left).Nonempty ∧ ∀ (T : Over S) [Nonempty T.left] (y : T ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ W → Function.Injective fun i => y ≫ s i := by
  classical
  let C : Fin m → Fin m → Set X.left := fun i j =>
    closure (Set.range (equalizer.ι (s i) (s j)).left)
  have hopen : IsOpen (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isClosed_closure.isOpen_compl
  refine ⟨⟨_, hopen⟩, ?_, ?_⟩
  · refine ⟨genericPoint X.left, ?_⟩
    show genericPoint X.left ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left)
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro i j hij hmem
    apply hij
    apply hs
    have hg : closure ({genericPoint X.left} : Set X.left) = Set.univ := genericPoint_spec X.left
    have huniv : C i j = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← hg]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
    have : IsDominant (equalizer.ι (s i) (s j)).left := ⟨by
      rw [DenseRange, dense_iff_closure_eq]; exact huniv⟩
    ext1
    exact ext_of_isDominant_of_isSeparated G.hom (by simp) (equalizer.ι (s i) (s j)).left
      (by rw [← Over.comp_left, equalizer.condition, Over.comp_left])
  · intro T _ y hy i j hij
    by_contra hne
    obtain ⟨t⟩ := ‹Nonempty T.left›
    have ht : y.left t ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left) := hy (Set.mem_univ t)
    simp only [Set.mem_iInter, Set.mem_compl_iff] at ht
    apply ht i j hne
    apply subset_closure
    refine ⟨(equalizer.lift y hij).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]

theorem exists_spread {Z S Y : Scheme.{0}} [IsIntegral Z] (c : Z ⟶ S) (G : Over S) [LocallyOfFiniteType G.hom]
    (j : Y ⟶ Z) (hj : GlobalTheory.IsGenericPointHom j) {m : ℕ} (P : Fin m → (Over.mk (j ≫ c) ⟶ G)) :
    ∃ (U : Z.Opens) (_ : genericPoint Z ∈ U) (k : Over.mk (j ≫ c) ⟶ Over.mk (U.ι ≫ c)) (_ : IsDominant k.left)
      (s : Fin m → (Over.mk (U.ι ≫ c) ⟶ G)), ∀ i, k ≫ s i = P i := by
  classical
  have hr := GlobalTheory.IsGenericPointHom.range_eq hj
  obtain ⟨e, he⟩ := hj
  have hφ : ∀ i, (e.inv ≫ (P i).left) ≫ G.hom = Z.fromSpecStalk (genericPoint Z) ≫ c := by
    intro i
    rw [Category.assoc, Over.w (P i)]
    simp [← he]
  choose U hU f hf₁ hf₂ using fun i =>
    spread_out_of_isGermInjective' c G.hom (e.inv ≫ (P i).left) (hφ i)
  have hopen : IsOpen (⋂ i, (U i : Set Z)) := isOpen_iInter_of_finite fun i => (U i).isOpen
  let V : Z.Opens := ⟨_, hopen⟩
  have hηV : genericPoint Z ∈ V := Set.mem_iInter.mpr hU
  have hle : ∀ i, V ≤ U i := fun i => Set.iInter_subset _ i
  have hres : ∀ i, V.fromSpecStalkOfMem _ hηV ≫ Z.homOfLE (hle i) =
      (U i).fromSpecStalkOfMem _ (hU i) := by
    intro i
    rw [← cancel_mono (U i).ι]
    simp [Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨V, hηV, Over.homMk (e.hom ≫ V.fromSpecStalkOfMem _ hηV) ?_, ?_,
    fun i => Over.homMk (Z.homOfLE (hle i) ≫ f i) ?_, ?_⟩
  · simp [Scheme.Opens.fromSpecStalkOfMem_ι_assoc, ← he]
  · show IsDominant (e.hom ≫ V.fromSpecStalkOfMem _ hηV)
    rw [isDominant_iff, DenseRange, dense_iff_inter_open]
    rintro W hW ⟨w, hw⟩
    have h1 : IsOpen (V.ι '' W) := V.ι.isOpenEmbedding.isOpenMap _ hW
    obtain ⟨v, hvW, hv⟩ :=
      ((genericPoint_spec Z).mem_open_set_iff h1).mpr ⟨_, trivial, w, hw, rfl⟩
    have hη : genericPoint Z ∈ Set.range j := by rw [hr]; rfl
    obtain ⟨y, hy⟩ := hη
    refine ⟨v, hvW, y, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, he, hy, hv]
  · rw [Category.assoc, hf₂, Scheme.homOfLE_ι_assoc]
    rfl
  · intro i
    ext1
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [reassoc_of% (hres i), ← hf₁, Iso.hom_inv_id_assoc]

end PositivityTheory.Xgn.TwoTorsionPointsSpreading

set_option backward.isDefEq.respectTransparency false in
theorem PositivityTheory.Xgn.two_torsion_points_spread_open : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  intro Z' S _ c G _ _ _ L' _ j hj m P hP hP2
  obtain ⟨U, hηU, k, hk, s, hs⟩ :=
    PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_spread c G j hj P
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : IsIntegral (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsIntegral U.toScheme)
  haveI : IsReduced (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsReduced U.toScheme)
  have hsinj : Function.Injective s := fun a b hab => hP (by rw [← hs a, ← hs b, hab])
  have hs2 : ∀ i, s i ^ 2 = 1 := by
    intro i
    have h1 : k ≫ s i ^ 2 = k ≫ 1 := by
      rw [pow_two, MonObj.comp_mul, ← pow_two, hs i, hP2 i]
      simp
    ext1
    exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w, Over.w]) k.left
      (by rw [← Over.comp_left, h1, Over.comp_left])
  obtain ⟨W, hWne, hW⟩ :=
    PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_open_injective (X := Over.mk (U.ι ≫ c)) s hsinj
  obtain ⟨w, hw⟩ := hWne
  refine ⟨U.ι ''ᵁ W, ⟨U.ι w, w, hw, rfl⟩, ?_⟩
  intro K _ x hx
  have hxW : ∀ t, ∃ w ∈ W, U.ι w = x t := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hx (Set.mem_univ t)
    exact ⟨w, hw, hwt⟩
  let x' := IsOpenImmersion.lift U.ι x (by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, -, h⟩ := hxW t
    exact ⟨w, h⟩)
  let y : Over.mk (x ≫ c) ⟶ Over.mk (U.ι ≫ c) := Over.homMk x' (by
    simp only [Over.mk_hom]
    rw [IsOpenImmersion.lift_fac_assoc])
  haveI : Nonempty (Over.mk (x ≫ c)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  refine ⟨fun i => y ≫ s i, hW (Over.mk (x ≫ c)) y ?_, fun i => ?_⟩
  · intro t _
    show x' t ∈ W
    obtain ⟨w, hw, hwt⟩ := hxW t
    have : x' t = w := U.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hwt])
    rw [this]
    exact hw
  · show (y ≫ s i) ^ 2 = 1
    rw [pow_two, ← MonObj.comp_mul, ← pow_two, hs2 i]
    simp
