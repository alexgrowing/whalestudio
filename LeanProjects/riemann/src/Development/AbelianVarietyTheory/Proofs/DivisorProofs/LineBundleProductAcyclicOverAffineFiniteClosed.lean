import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProductAcyclicFin

open GlobalTheory.Cube HomologicalComplex

theorem cech_sliceFst_singleton_acyclic {𝔦 𝔧 : Type} [LinearOrder 𝔦] [LinearOrder 𝔧] [Finite 𝔧]
    {R : Type} [Ring R] (A : GlobalTheory.Cube.{0} (𝔦 ⊕ₗ 𝔧) R)
    (h₀ : ∀ n, IsZero ((cubeComplex (trunc₂ A)).homology (n + 2)))
    (hA : ∀ t : Finset 𝔧, 2 ≤ t.card → (cechComplex (sliceFst A t)).Acyclic) (k : 𝔧) :
    (cechComplex (sliceFst A {k})).Acyclic := by
  have hc := isCompl_range_inlEmb_inrEmb 𝔦 𝔧
  have hQ : Set.OrdConnected {s : Finset 𝔦 | s.Nonempty} := ordConnected_nonempty
  have hU₁ : IsUpperSet {t : Finset 𝔧 | 2 ≤ t.card} :=
    fun s t hst (hs : 2 ≤ s.card) => le_trans hs (Finset.card_le_card hst)
  have hT₁ : Set.OrdConnected {t : Finset 𝔧 | 2 ≤ t.card} := hU₁.ordConnected
  have hT₂ : Set.OrdConnected {t : Finset 𝔧 | t.card = 1} := ⟨fun a (ha : a.card = 1) b
    (hb : b.card = 1) x hx => by
      have h1 := Finset.card_le_card hx.1
      have h2 := Finset.card_le_card hx.2
      show x.card = 1
      omega⟩
  have hTk : Set.OrdConnected ({{k}} : Set (Finset 𝔧)) := Set.ordConnected_singleton
  have hS := cubeFunctor_shortExact _ (suppSequence_shortExact A
    (ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hT₁)
    (ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ ordConnected_nonempty)
    (ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hT₂)
    (fun u => by
      simp only [mem_partsIn, Set.mem_setOf_eq, ← Finset.card_pos]
      constructor <;> intro h <;> omega)
    (fun u hu hu' => by
      simp only [mem_partsIn, Set.mem_setOf_eq] at hu hu'
      omega)
    (fun _ _ hst hs ht => ⟨ht.1, le_trans hs.2 (Finset.card_le_card (monotone_part _ hst))⟩))

  have h₁ : (cubeComplex (supp A (partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) {s | s.Nonempty}
      {t | 2 ≤ t.card}) (ordConnected_partsIn _ _ hQ hT₁))).Acyclic := by
    rw [supp_partsIn_comm hQ hT₁ A]
    refine cubeComplex_supp_partsIn_acyclic hc.symm hT₁ hQ A fun t ht => ?_
    rw [← sliceFst_eq_slice]
    exact (cubeComplex_trunc₁_acyclic_iff _).2 (hA t ht)

  have h₂ : (cubeComplex (trunc₂ A)).Acyclic := by
    intro n
    match n with
    | n + 2 => exact (exactAt_iff_isZero_homology _ _).2 (h₀ n)
    | 0 | 1 =>
      refine ExactAt.of_isZero (isZero_cubeComplex_X_of_subsingleton _ _ fun u hu => ?_)
      refine subsingleton_supp A (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty) fun hmem => ?_
      simp only [mem_partsIn, Set.mem_setOf_eq] at hmem
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hmem
      rw [mem_part] at hi hj
      have : 1 < u.card := Finset.one_lt_card.2 ⟨_, hi, _, hj, by simp⟩
      omega

  have h₃ : ∀ n, IsZero ((cubeComplex (supp A (partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧)
      {s | s.Nonempty} {t | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₂))).homology n) := by
    intro n
    have hx := hS.homology_exact₃ n (n + 1) rfl
    exact hx.isZero_X₂ (((exactAt_iff_isZero_homology _ _).1 (h₂ n)).eq_of_src _ _)
      (((exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))).eq_of_tgt _ _)

  have hPk := ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hTk
  have hP₂ := ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hT₂
  let ι₁ := suppMap (𝟙 A) hPk hP₂ fun s t hst hs ht => by
    simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs ht ⊢
    refine iff_of_true ⟨ht.1, ?_⟩ ⟨hs.1, by rw [hs.2]; rfl⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 ht.2
    have : k ∈ part (inrEmb 𝔦 𝔧) t := monotone_part _ hst (by rw [hs.2]; exact Finset.mem_singleton_self k)
    rw [ha, Finset.mem_singleton] at this
    rw [ha, this]
  let ρ₁ := suppMap (𝟙 A) hP₂ hPk fun s t hst hs ht => by
    simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs ht ⊢
    refine iff_of_true ⟨ht.1, by rw [ht.2]; rfl⟩ ⟨hs.1, ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hs.2
    have : a ∈ part (inrEmb 𝔦 𝔧) t := monotone_part _ hst (by rw [ha]; exact Finset.mem_singleton_self a)
    rw [ht.2, Finset.mem_singleton] at this
    rw [ha, this]
  have hr : ι₁ ≫ ρ₁ = 𝟙 _ := by
    ext s x
    refine supp_ext fun hs => ?_
    have hs₂ : s ∈ partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) {s | s.Nonempty} {t | t.card = 1} := by
      simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs ⊢
      exact ⟨hs.1, by rw [hs.2]; rfl⟩
    change suppEquiv A hPk hs (suppMapApp (𝟙 A) hP₂ hPk s (suppMapApp (𝟙 A) hPk hP₂ s x)) =
      suppEquiv A hPk hs x
    rw [suppEquiv_suppMapApp (𝟙 A) hs₂ hs, suppEquiv_suppMapApp (𝟙 A) hs hs₂]
    rfl
  have h₄ : ∀ n, IsZero ((cubeComplex (supp A (partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧)
      {s | s.Nonempty} {{k}}) hPk)).homology n) := by
    intro n
    rw [IsZero.iff_id_eq_zero]
    have := congrArg (fun φ => homologyMap ((cubeFunctor _ R).map φ) n) hr
    simp only [Functor.map_comp, Functor.map_id, homologyMap_comp, homologyMap_id] at this
    have h0 : homologyMap ((cubeFunctor _ R).map ρ₁) n = 0 := (h₃ n).eq_of_src _ _
    rw [h0, comp_zero, CategoryTheory.Functor.map_id, homologyMap_id] at this
    exact this.symm
  have h₅ : (cubeComplex (supp (slice (inlEmb 𝔦 𝔧) (({k} : Finset 𝔧).map (inrEmb 𝔦 𝔧).toEmbedding) A)
      {s | s.Nonempty} hQ)).Acyclic := fun n =>
    (exactAt_iff_isZero_homology _ _).2 ((h₄ (n + 1)).of_iso (suppSingletonHomologyIso hc hQ k A n).symm)
  rw [← cubeComplex_trunc₁_acyclic_iff, trunc₁, sliceFst_eq_slice]
  exact h₅

variable {K : Type} [Field K] {Z T X : Scheme.{0}} {p : Z ⟶ T} {g : T ⟶ Spec (CommRingCat.of K)}
  {q : Z ⟶ X} {h : X ⟶ Spec (CommRingCat.of K)} {F : LB Z}

theorem acyclic_over_of_pairs (sq : IsPullback p q g h) [IsSeparated g] [IsSeparated h] (hF : F.IsLB)
    {σ : Type} [LinearOrder σ] [Fintype σ] (V : σ → T.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVc : ⨆ j, V j = ⊤)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t →
      ∀ j j', j ≠ j' → (∀ y, t y ∈ V j ⊓ V j') →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic)
    {ν : Type} [LinearOrder ν] [Fintype ν] (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hBc : ⨆ i, B i = ⊤)
    (hac : ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (D i)) →
      ⨆ i, D i = ⊤ → (cechLB (p ≫ g) F D).Acyclic) (k : σ) :
    (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V k).Acyclic := by
  have : T.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from h]
    infer_instance⟩
  have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›
  let P : ν ×ₗ σ → Z.Opens := fun u => q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2
  have hP (u) : IsAffineOpen (P u) := GlobalTheory.ProductAcyclic.isAffineOpen_prod sq hF (hV _) B hB hBc _
  have hPc : ⨆ u, P u = ⊤ := by
    refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))
    exact ⟨toLex (i, j), hi, hj⟩
  have h₀ : ∀ n, IsZero ((cubeComplex (Cube.trunc₂ (secCube (p ≫ g) F fun u : ν ⊕ₗ σ =>
      Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u)))).homology (n + 2)) := by
    intro n
    obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F _ P _
      (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hP hPc
      (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
      (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
      (fun i _ hW => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) hW)
      (fun j _ hW => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) hW)
      (fun i j => GlobalTheory.ProductAcyclic.isAffineOpen_prod sq hF (hV j) B hB hBc i) n
    have h₁ := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac _ P hP hPc n)
    rw [ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
    exact e₁.symm.injective.subsingleton
  have hs : ∀ s : Finset σ, 2 ≤ s.card → (cechComplex (Cube.sliceFst (secCube (p ≫ g) F
      fun u : ν ⊕ₗ σ => Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u)) s)).Acyclic := by
    intro s hs
    obtain ⟨j, hj, j', hj', hjj⟩ := Finset.one_lt_card.1 hs
    have hne : s.Nonempty := ⟨j, hj⟩
    have hVs : IsAffineOpen (⨅ j ∈ s, V j) :=
      IsAffineOpen.biInf _ s.finite_toSet hne fun j _ => hV j
    have H₀ := IsPullback.of_hasPullback p hVs.fromSpec
    have h₁ := (GlobalTheory.ProductAcyclic.over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀
      hVs.opensRange_fromSpec B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j j' hjj
        fun y => le_inf (biInf_le V hj) (biInf_le V hj') (hVs.range_fromSpec.le ⟨y, rfl⟩))
    obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
      (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)
    exact fun m => (h₁ m).of_iso i₂
  have hk := cech_sliceFst_singleton_acyclic _ h₀ hs k
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
    (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)
  exact fun m => (hk m).of_iso i₂.symm

end GlobalTheory.ProductAcyclicFin

namespace GlobalTheory.ProductAcyclicFin

theorem acyclic_over_affine_of_finite_closed : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ∀ S : Finset T, (∀ s ∈ S, IsClosed ({s} : Set T)) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ∉ S) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  intro K _ Z T p g X q h sq _ _ _ _ F hF S hS H hac R _ t Y π f H₀ ht
  classical
  haveI := ht
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨m, B, hB, hBc, -, -⟩ :=
    GlobalTheory.ProductAcyclic.exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial

  have hU : ∀ s ∈ S, ∃ U : T.Opens, IsAffineOpen U ∧ s ∈ U ∧ ∀ x ∈ S, x ∈ U → x = s := by
    intro s hs
    have hC : IsClosed (⋃ x ∈ S.erase s, ({x} : Set T)) :=
      Set.Finite.isClosed_biUnion (S.erase s).finite_toSet fun x hx =>
        hS x (Finset.mem_of_mem_erase hx)
    have hsC : s ∈ (⋃ x ∈ S.erase s, ({x} : Set T))ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
      intro x hx hsx
      exact Finset.ne_of_mem_erase hx hsx.symm
    obtain ⟨_, ⟨U, hUa, rfl⟩, hsU, hUC⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hsC hC.isOpen_compl
    refine ⟨U, hUa, hsU, fun x hx hxU => by_contra fun hne => hUC hxU ?_⟩
    exact Set.mem_iUnion₂.2 ⟨x, Finset.mem_erase.2 ⟨hne, hx⟩, rfl⟩
  choose! U hUa hUs hUS using hU
  let S' := S.filter (fun s => s ∉ t.opensRange)
  let pt : Fin S'.card → T := fun j => (S'.equivFin.symm j).1
  have hpt (j) : pt j ∈ S ∧ pt j ∉ t.opensRange := Finset.mem_filter.1 (S'.equivFin.symm j).2
  let G : Fin (S'.card + 1) → T.Opens := Fin.cons t.opensRange fun j => U (pt j)
  have hGa : ∀ a, IsAffineOpen (G a) :=
    Fin.cases (isAffineOpen_opensRange t) fun j => hUa _ (hpt j).1
  have hGS : ∀ a b, a ≠ b → ∀ x ∈ S, x ∈ G a → x ∈ G b → False := by
    have h₁ : ∀ j, ∀ x ∈ S, x ∈ t.opensRange → x ∈ U (pt j) → False := fun j x hx hx₁ hx₂ =>
      (hpt j).2 (hUS _ (hpt j).1 x hx hx₂ ▸ hx₁)
    intro a b hab x hx ha hb
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact hab rfl
      | succ j => exact h₁ j x hx ha hb
    | succ i =>
      induction b using Fin.cases with
      | zero => exact h₁ i x hx hb ha
      | succ j =>
        refine hab (congrArg Fin.succ (S'.equivFin.symm.injective (Subtype.ext ?_)))
        exact (hUS _ (hpt i).1 x hx ha).symm.trans (hUS _ (hpt j).1 x hx hb)
  have hGc : ∀ x ∈ S, x ∈ ⨆ a, G a := by
    intro x hx
    refine TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hxt : x ∈ t.opensRange
    · exact ⟨0, hxt⟩
    · have hx' : x ∈ S' := Finset.mem_filter.2 ⟨hx, hxt⟩
      refine ⟨(S'.equivFin ⟨x, hx'⟩).succ, ?_⟩
      have : pt (S'.equivFin ⟨x, hx'⟩) = x := by simp [pt]
      simp only [G, Fin.cons_succ]
      rw [this]
      exact hUs x hx

  obtain ⟨r, V', hV'a, hV'S, hV'c⟩ : ∃ (r : ℕ) (V' : Fin r → T.Opens), (∀ j, IsAffineOpen (V' j)) ∧
      (∀ j, ∀ x ∈ V' j, x ∉ S) ∧ ∀ x, x ∉ ⨆ a, G a → ∃ j, x ∈ V' j := by
    have hSc : IsOpen (↑S : Set T)ᶜ := by
      have := Set.Finite.isClosed_biUnion S.finite_toSet fun x hx => hS x hx
      rw [Set.biUnion_of_singleton] at this
      exact this.isOpen_compl
    have hc : IsCompact (↑(⨆ a, G a) : Set T)ᶜ := (⨆ a, G a).isOpen.isClosed_compl.isCompact
    obtain ⟨s, hs⟩ := hc.elim_finite_subcover
      (fun W : {W : T.Opens // IsAffineOpen W ∧ (W : Set T) ⊆ (↑S)ᶜ} => (W.1 : Set T))
      (fun W => W.1.isOpen) (by
        intro x hx
        have hxS : x ∈ (↑S : Set T)ᶜ := fun hxS => hx (hGc x hxS)
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
          T.isBasis_affineOpens.exists_subset_of_mem_open hxS hSc
        exact Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)
    refine ⟨s.card, fun j => (s.equivFin.symm j).1.1, fun j => (s.equivFin.symm j).1.2.1,
      fun j x hx => (s.equivFin.symm j).1.2.2 hx, fun x hx => ?_⟩
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
    exact ⟨s.equivFin ⟨W, hW⟩, by simpa using hxW⟩
  let V : Fin (S'.card + 1 + r) → T.Opens := Fin.append G V'
  have hV : ∀ j, IsAffineOpen (V j) := Fin.addCases (fun a => by simpa [V] using hGa a)
    (fun j => by simpa [V] using hV'a j)
  have hVc : ⨆ j, V j = ⊤ := by
    refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ ⨆ a, G a
    · obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨Fin.castAdd r a, by simpa [V] using ha⟩
    · obtain ⟨j, hj⟩ := hV'c x hx
      exact ⟨Fin.natAdd _ j, by simpa [V] using hj⟩
  have hVS : ∀ j j', j ≠ j' → ∀ x, x ∈ V j → x ∈ V j' → x ∉ S := by
    intro j j' hjj x hx hx' hxS
    induction j using Fin.addCases with
    | left a =>
      induction j' using Fin.addCases with
      | left b =>
        simp only [V, Fin.append_left] at hx hx'
        exact hGS a b (fun hab => hjj (hab ▸ rfl)) x hxS hx hx'
      | right c =>
        simp only [V, Fin.append_right] at hx'
        exact hV'S c x hx' hxS
    | right c =>
      simp only [V, Fin.append_right] at hx
      exact hV'S c x hx hxS
  have hk : V (Fin.castAdd r 0) = t.opensRange := by simp [V, G]
  have h₁ := GlobalTheory.ProductAcyclicFin.acyclic_over_of_pairs sq hF V hV hVc
    (fun R _ t Y π f H₁ ht j j' hjj hy => H R t Y π f H₁ ht fun y hyS =>
      hVS j j' hjj _ (hy y).1 (hy y).2 hyS)
    B hB hBc hac (Fin.castAdd r 0)
  exact (GlobalTheory.ProductAcyclic.over_affineOpen sq hF H₀ hk.symm B hB hBc).2.2 h₁

end GlobalTheory.ProductAcyclicFin
