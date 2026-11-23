import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem isLB_of_gm {Y : Scheme.{0}} (L : LB Y) (hc : ∀ y : Y, ∃ i, y ∈ L.U i)
    (h : ∀ (y : Y) i j k, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y _ (L.g i j) * gm (𝟙 Y) y _ (L.g j k) = gm (𝟙 Y) y _ (L.g i k)) : L.IsLB where
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    refine (gm_res (𝟙 Y) y _ hy _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy =>
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 Y) y _ hy _) (gm_res (𝟙 Y) y _ hy _))).trans
      ((h y i j k hy.1.1 hy.1.2 hy.2).trans (gm_res (𝟙 Y) y _ hy _).symm)

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in

theorem exists_isLB_of_isLimit {i : I} [CompactSpace (D.obj i)] (M : LB (D.obj i)) [Finite M.ι]
    (hM : ∀ a b c, IsCompact ((M.U a ⊓ M.U b ⊓ M.U c : (D.obj i).Opens) : Set (D.obj i)))
    (hcov : ∀ y : X, ∃ a, π i y ∈ M.U a)
    (h : ∀ (y : X) a b c, π i y ∈ M.U a → π i y ∈ M.U b → π i y ∈ M.U c →
      gm (π i) y _ (M.g a b) * gm (π i) y _ (M.g b c) = gm (π i) y _ (M.g a c)) :
    ∃ (j : I) (f : j ⟶ i), (M.pull (D.map f)).IsLB := by
  have l₁ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U b := fun a b c => inf_le_left
  have l₂ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U b ⊓ M.U c := fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U c := fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  have val : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj i) (z : Z) a b c, r z ∈ M.U a ⊓ M.U b ⊓ M.U c →
      gm r z _ (res (l₁ a b c) (M.g a b) * res (l₂ a b c) (M.g b c)) =
        gm r z _ (M.g a b) * gm r z _ (M.g b c) := fun r z a b c hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : M.ι × M.ι × M.ι) k g =>
      pullU (D.map g) _ (res (l₁ p.1 p.2.1 p.2.2) (M.g _ _) * res (l₂ p.1 p.2.1 p.2.2) (M.g _ _)) =
        pullU (D.map g) _ (res (l₃ p.1 p.2.1 p.2.2) (M.g _ _)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      exact exists_pullU_eq D π w hc (hM a b c) _ _ fun y hy =>
        (val (π i) y a b c hy).trans ((h y a b c hy.1.1 hy.1.2 hy.2).trans (gm_res _ y _ hy _).symm))
  obtain ⟨j', f', hj'⟩ := exists_map_preimage_le_map_preimage D _ hc (U := ⊤) (V := ⨆ a, M.U a)
    isCompact_univ (fun y _ => Opens.mem_iSup.2 (hcov y))
  obtain ⟨k, g, g', hg⟩ := IsCofiltered.cospan f f'
  refine ⟨k, g ≫ f, isLB_of_gm _ (fun y => ?_) fun y a b c ha hb hc' => ?_⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hj' (show D.map g' y ∈ D.map f' ⁻¹ᵁ ⊤ from trivial))
    refine ⟨fun _ => a, mem_pull.2 ?_⟩
    rw [hg, D.map_comp]
    exact ha
  · rw [gm_pull_g M _ (𝟙 _) y a b ha hb, gm_pull_g M _ (𝟙 _) y b c hb hc', gm_pull_g M _ (𝟙 _) y a c ha hc',
      Category.id_comp]
    have hy : D.map (g ≫ f) y ∈ M.U (a PUnit.unit) ⊓ M.U (b PUnit.unit) ⊓ M.U (c PUnit.unit) :=
      ⟨⟨mem_pull.1 ha, mem_pull.1 hb⟩, mem_pull.1 hc'⟩
    rw [D.map_comp] at hy ⊢
    have e := congrArg (gm (D.map g) y _) (hj (a PUnit.unit, b PUnit.unit, c PUnit.unit))
    exact (val _ y _ _ _ hy).symm.trans ((gm_pull (D.map g) (D.map f) y _ hy _).symm.trans (e.trans
      ((gm_pull (D.map g) (D.map f) y _ hy _).trans (gm_res _ y _ hy _))))

include hc in

theorem exists_lb_of_isLimit {i : I} [CompactSpace (D.obj i)] [CompactSpace X]
    (hsep : ∀ U V : (D.obj i).Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hπ : Topology.IsInducing (π i)) (L₀ : LB X) (hL : L₀.IsLB) :
    ∃ (j : I) (L : LB (D.obj j)), L.IsLB ∧ LBIso L₀ (L.pull (π j)) := by
  have loc : ∀ x : X, ∃ (V : (D.obj i).Opens) (c : L₀.ι),
      IsAffineOpen V ∧ π i x ∈ V ∧ π i ⁻¹ᵁ V ≤ L₀.U c := by
    intro x
    obtain ⟨c, hc⟩ := exists_chart hL x
    obtain ⟨W, hW, hW'⟩ := hπ.isOpen_iff.1 (L₀.U c).isOpen
    have hx : π i x ∈ W := hW'.ge hc
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ := (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open hx hW
    exact ⟨V, c, hV, hx, fun y hy => hW'.le (hle hy)⟩
  choose V c hV hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => ((π i ⁻¹ᵁ V x : X.Opens) : Set X))
    (fun x => (π i ⁻¹ᵁ V x).isOpen.mem_nhds (hx x))
  have cov : ∀ x : X, ∃ a : σ, π i x ∈ V a := fun x => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have l : ∀ a b, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L₀.U (c a) ⊓ L₀.U (c b) := fun a b _ hy => ⟨hle a hy.1, hle b hy.2⟩
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V p.1 ⊓ V p.2) →
      gm (π j) y (D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2)) t = gm (𝟙 X) y _ (res (l p.1 p.2) (L₀.g _ _)))
    (by
      rintro p j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V p.1 ⊓ V p.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun p => exists_unit_π_eq D π w hc (hsep _ _ (hV _) (hV _)) _)
  choose t ht using hj
  let M : LB (D.obj j) := ⟨σ, fun a => D.map f ⁻¹ᵁ V a, fun a b => t (a, b)⟩
  have mem : ∀ (y : X) (a : σ), π j y ∈ M.U a ↔ π i y ∈ V a := fun y a => by
    rw [← w f]; rfl
  have val : ∀ (y : X) (a b : σ), π j y ∈ M.U a → π j y ∈ M.U b →
      gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L₀.g (c a) (c b)) := fun y a b ha hb =>
    have hy : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := ⟨(mem y a).1 ha, (mem y b).1 hb⟩
    (ht (a, b) y hy).trans (gm_res _ y _ hy _)
  have : CompactSpace (D.obj j) := QuasiCompact.compactSpace_of_compactSpace (D.map f)
  have : Finite M.ι := inferInstanceAs (Finite σ)
  obtain ⟨k, g, hk⟩ := exists_isLB_of_isLimit D π w hc M
    (fun a b e => ((hsep _ _ (hsep _ _ (hV a) (hV b)) (hV e)).preimage (D.map f)).isCompact)
    (fun y => (cov y).imp fun a ha => (mem y a).2 ha)
    (fun y a b e ha hb he => by
      rw [val y a b ha hb, val y b e hb he, val y a e ha he]
      exact gm_cocycle hL (𝟙 X) y (hle a ((mem y a).1 ha)) (hle b ((mem y b).1 hb)) (hle e ((mem y e).1 he)))
  have mem' : ∀ (y : X) J, y ∈ ((M.pull (D.map g)).pull (π k)).U J → π j y ∈ M.U (J PUnit.unit PUnit.unit) :=
    fun y J hy => by
      rw [← w g]
      have hy' : π k y ∈ (M.pull (D.map g)).U (J PUnit.unit) := mem_pull.1 hy
      exact (mem_pull (F := D.map g)).1 hy'
  refine ⟨k, _, hk, (lbIso_of_chartPull (B' := (M.pull (D.map g)).pull (π k))
    ⟨fun J => c (J PUnit.unit PUnit.unit).1, fun J y hy => hle _ ((mem y _).1 (mem' y J hy)),
      fun y J J' hJ hJ' => ?_⟩ hL).symm⟩
  rw [gm_pull_g _ _ (𝟙 _) y J J' hJ hJ', Category.id_comp,
    gm_pull_g M _ (π k) y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'), w g]
  exact val y _ _ (mem' y J hJ) (mem' y J' hJ')

end Limit

theorem exists_lb {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [IsSeparated f] {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K}
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L₀ : LB X₀} (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ f).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f V₀.1.ι)
  have : QuasiCompact f₀ := MorphismProperty.of_isPullback (P := @QuasiCompact) h inferInstance
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h₁.flip inferInstance
  have hs : (pullback f V₀.1.ι).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.snd f V₀.1.ι)]; infer_instance⟩
  have : ((StalkLimit.diagram _ f).obj V₀).IsSeparated := hs
  have hi : Topology.IsInducing ((StalkLimit.cone h₁).π.app V₀) := by
    refine Topology.IsInducing.of_comp (g := pullback.fst f V₀.1.ι) (Scheme.Hom.continuous _)
      (Scheme.Hom.continuous _) ?_
    have := φ.isEmbedding.isInducing
    rw [← StalkLimit.cone_π_fst h₁ V₀] at this
    exact this
  obtain ⟨V, L, hL', H⟩ := exists_lb_of_isLimit (StalkLimit.diagram _ f) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (i := V₀) (fun U W hU hW => hU.inf hW) hi L₀ hL
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg X' π f' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open f V.1 e (Ha R' g hg)
  refine ⟨L.pull l, pull_isLB hL' _, fun φ' hφ' => ?_⟩
  have : (StalkLimit.cone h₁).π.app V = φ' ≫ l := by
    rw [← cancel_mono (pullback.fst f V.1.ι), Category.assoc, hl, hφ', StalkLimit.cone_π_fst]
  exact LBIso.trans hL (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) H (lbIso_pull_pull hL' φ' this)

theorem lineBundle_spreads_out (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X)
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) (_ : Flat f) (_ : IsProper f) (L₀ : LB X₀) (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') :=
  exists_lb f h hL

end GlobalTheory.GenSpread
