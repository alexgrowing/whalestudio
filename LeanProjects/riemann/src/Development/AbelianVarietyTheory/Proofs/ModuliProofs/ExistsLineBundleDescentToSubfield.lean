import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.LBDescent

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [∀ i, CompactSpace (D.obj i)] in
set_option backward.isDefEq.respectTransparency false in
include hc in

theorem exists_appLE_eq {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s : Γ(X, π i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      ((π j).appLE _ _ (cone_preimage_le D π w f U)).hom t = s := by
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isLimit _ _
    (isLimitOpensCone D _ hc i U) ((π i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, ?_⟩
  have h := (congrArg (π i ⁻¹ᵁ U).topIso.hom hj.symm).trans (Iso.inv_hom_id_apply _ s)
  have e : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), (f.appLE U V e).hom (U.topIso.hom t) =
        V.topIso.hom ((f.resLE U V e).appTop t) := by
    intro X Y f U V e t
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
  exact (e _ _ _ _ t).trans h

omit [∀ i, CompactSpace (D.obj i)] in
include hc in

theorem exists_unit_eq {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s : Γ(X, π i ⁻¹ᵁ U)ˣ) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ), ∀ y : X, y ∈ π i ⁻¹ᵁ U →
      gm (π j) y (D.map f ⁻¹ᵁ U) t = gm (𝟙 X) y (π i ⁻¹ᵁ U) s := by
  obtain ⟨j, f, t, ht⟩ := exists_appLE_eq D π w hc hU s.val
  have h₁ : π j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) ≤ π j ⁻¹ᵁ (D.obj j).basicOpen t := by
    have h := X.basicOpen_of_isUnit (ht ▸ s.isUnit)
    rw [Scheme.basicOpen_appLE] at h
    rw [← Scheme.Hom.comp_preimage, w, ← h]
    exact inf_le_right
  obtain ⟨k, g, hg⟩ := exists_map_preimage_le_map_preimage D _ hc
    (QuasiCompact.isCompact_preimage (f := D.map f) _ U.2 hU) h₁
  have le : D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have hu : IsUnit (((D.map g).appLE _ _ le).hom t) := by
    refine (D.obj k).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
    refine ((D.obj k).mem_basicOpen _ y hy).1 ?_
    rw [Scheme.basicOpen_appLE]
    exact ⟨hy, hg (le hy)⟩
  refine ⟨k, g ≫ f, hu.unit, fun y hy => Units.ext ?_⟩
  have hy' := cone_preimage_le D π w (g ≫ f) U hy
  rw [gm_val _ y _ hy', gm_val (𝟙 X) y _ hy, IsUnit.unit_spec, ← ht]
  have e : (D.map g).appLE _ _ le ≫ (π k).appLE _ _ (cone_preimage_le D π w (g ≫ f) U) =
      (π j).appLE _ _ (cone_preimage_le D π w f U) := by
    simp only [Scheme.Hom.appLE_comp_appLE, w]
  rw [← e]
  exact (TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE (cone_preimage_le D π w (g ≫ f) U)) y hy _).symm

theorem pull_isLB_of_germ {Y Z : Scheme.{0}} (M : LB Y) (F : Z ⟶ Y) (hcov : ∀ y : Y, ∃ a, y ∈ M.U a)
    (hco : ∀ (z : Z) a b c, F z ∈ M.U a → F z ∈ M.U b → F z ∈ M.U c →
      gm F z _ (M.g a b) * gm F z _ (M.g b c) = gm F z _ (M.g a c)) : (M.pull F).IsLB where
  cover := top_le_iff.1 fun y _ => by
    obtain ⟨i, hi⟩ := hcov (F y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  g_self J := unit_ext fun y hy => by
    rw [gm_res (𝟙 Z) y _ hy, map_one, gm_pull_g M F (𝟙 Z) y J J hy hy]
    exact mul_eq_left.1 (hco y _ _ _ (mem_pull.1 hy) (mem_pull.1 hy) (mem_pull.1 hy))
  cocycle I J K := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy,
      gm_pull_g M F (𝟙 Z) y I J hy.1.1 hy.1.2,
      gm_pull_g M F (𝟙 Z) y J K hy.1.2 hy.2, gm_pull_g M F (𝟙 Z) y I K hy.1.1 hy.2]
    exact hco y _ _ _ (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)

omit [∀ i, CompactSpace (D.obj i)] in
include hc in

theorem exists_cocycle {j : I} (M : LB (D.obj j)) [Finite M.ι]
    (hM : ∀ a, IsCompact (M.U a : Set (D.obj j)))
    (h : ∀ (y : X) a b c, π j y ∈ M.U a → π j y ∈ M.U b → π j y ∈ M.U c →
      gm (π j) y _ (M.g a b) * gm (π j) y _ (M.g b c) = gm (π j) y _ (M.g a c)) :
    ∃ (k : I) (g : k ⟶ j), ∀ (z : D.obj k) a b c, D.map g z ∈ M.U a → D.map g z ∈ M.U b →
      D.map g z ∈ M.U c →
      gm (D.map g) z _ (M.g a b) * gm (D.map g) z _ (M.g b c) = gm (D.map g) z _ (M.g a c) := by
  have l₁ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U b := fun a b c => inf_le_left
  have l₂ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U b ⊓ M.U c := fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U c := fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨k, g, hk⟩ := exists_common_refinement (i := j)
    (fun (p : M.ι × M.ι × M.ι) k g =>
      pullU (D.map g) _ (res (l₁ p.1 p.2.1 p.2.2) (M.g p.1 p.2.1) * res (l₂ p.1 p.2.1 p.2.2) (M.g p.2.1 p.2.2)) =
        pullU (D.map g) _ (res (l₃ p.1 p.2.1 p.2.2) (M.g p.1 p.2.2)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      refine exists_pullU_eq D π w hc ?_ _ _ fun y hy => ?_
      · exact QuasiSeparatedSpace.inter_isCompact _ _ (M.U a ⊓ M.U b).isOpen
          (QuasiSeparatedSpace.inter_isCompact _ _ (M.U a).isOpen (hM a) (M.U b).isOpen (hM b))
          (M.U c).isOpen (hM c)
      · rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
        exact h y a b c hy.1.1 hy.1.2 hy.2)
  refine ⟨k, g, fun z a b c ha hb hc' => ?_⟩
  have hz : D.map g z ∈ M.U a ⊓ M.U b ⊓ M.U c := ⟨⟨ha, hb⟩, hc'⟩
  have e := (gm_id_pullU (D.map g) z _ hz _).symm.trans
    ((congrArg (gm (𝟙 (D.obj k)) z (D.map g ⁻¹ᵁ (M.U a ⊓ M.U b ⊓ M.U c))) (hk (a, b, c))).trans
      (gm_id_pullU (D.map g) z _ hz _))
  rwa [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz] at e

include hc in

theorem exists_lb_of_isLimit (L : LB X) (hL : L.IsLB) :
    ∃ (k : I) (M : LB (D.obj k)), M.IsLB ∧ LBIso L (M.pull (π k)) := by
  have : CompactSpace X := Scheme.compactSpace_of_isLimit D _ hc
  have loc : ∀ x : X, ∃ (W : X.Opens) (e : L.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ L.U e := by
    intro x
    obtain ⟨p, hp⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hp (L.U p).isOpen
    exact ⟨V, p, hV, hx, hle⟩
  choose W e hW hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen.mem_nhds (hx x))
  have cov : IsOpenCover (fun a : σ => W a) := top_le_iff.1 fun x _ => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, hx⟩
  obtain ⟨i, V, hV, hVW⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite D _ hc
    (fun a : σ => W a) cov (fun a => hW a)
  have hle' : ∀ a : σ, π i ⁻¹ᵁ V a ≤ L.U (e a) := fun a => (hVW a).2.ge.trans (hle a)
  have l : ∀ a b : σ, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L.U (e a) ⊓ L.U (e b) := fun a b y hy =>
    ⟨hle' a hy.1, hle' b hy.2⟩
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V p.1 ⊓ V p.2) → gm (π j) y (D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2)) t =
        gm (𝟙 X) y (π i ⁻¹ᵁ (V p.1 ⊓ V p.2)) (res (l p.1 p.2) (L.g (e p.1) (e p.2))))
    (by
      rintro a j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V a.1 ⊓ V a.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun p => exists_unit_eq D π w hc (QuasiSeparatedSpace.inter_isCompact _ _ (V p.1).isOpen
      (hVW p.1).1.isCompact (V p.2).isOpen (hVW p.2).1.isCompact) _)
  choose t ht using hj
  let M : LB (D.obj j) := ⟨σ, fun a => D.map f ⁻¹ᵁ V a, fun a b => t (a, b)⟩
  have mem : ∀ (y : X) a, π j y ∈ M.U a → y ∈ π i ⁻¹ᵁ V a := fun y a h => by
    rw [← w f]; exact h
  have val : ∀ (y : X) a b, π j y ∈ M.U a → π j y ∈ M.U b →
      gm (π j) y (M.U a ⊓ M.U b) (M.g a b) = gm (𝟙 X) y _ (L.g (e a.1) (e b.1)) := fun y a b ha hb =>
    have hy : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := ⟨mem y a ha, mem y b hb⟩
    (ht (a, b) y hy).trans (gm_res (𝟙 X) y _ hy _)
  have : Finite M.ι := inferInstanceAs (Finite σ)
  obtain ⟨k, g, hk⟩ := exists_cocycle D π w hc M
    (fun a => ((hVW a).1.preimage (D.map f)).isCompact) (fun y a b c ha hb hc' => by
      rw [val y a b ha hb, val y b c hb hc', val y a c ha hc']
      exact gm_cocycle hL (𝟙 X) y (hle' a (mem y a ha)) (hle' b (mem y b hb)) (hle' c (mem y c hc')))
  refine ⟨k, M.pull (D.map g), pull_isLB_of_germ M _ (fun y => hV.exists_mem (D.map f y)) hk, ?_⟩
  have c₁ : ChartPull (M.pull (π j)) L (𝟙 X) :=
    { idx := fun J => e (J PUnit.unit).1
      le := fun J y hy => hle' _ (mem y _ (mem_pull.1 hy))
      g := fun y J J' hJ hJ' => (gm_pull_g M (π j) (𝟙 X) y J J' hJ hJ').trans
        (val y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ')) }
  exact LBIso.chartPull (chartPullId L)
    (chartPullLinComb M (D.map g) (fun _ : PUnit => π k) (fun _ => π j) (fun _ => 1) (𝟙 X)
      (fun _ => (w g).trans (Category.id_comp _).symm))
    (LBIso.chartPull (chartPullId L) c₁ (PolBaseChange.lbIso_refl hL))

end Limit

theorem exists_fg_lb {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {B X : Scheme.{0}}
    (pB : B ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] (p : X ⟶ Sp C) (φ : X ⟶ B)
    (hX : IsPullback φ p pB (spMap (algebraMap k C))) (L : LB X) (hL : L.IsLB) :
    ∃ (R : Subalgebra k C) (M : LB (pullback pB (spMap (algebraMap k R))))
      (ρ : X ⟶ pullback pB (spMap (algebraMap k R))), R.FG ∧ M.IsLB ∧ ρ ≫ pullback.fst _ _ = φ ∧
      ρ ≫ pullback.snd _ _ = p ≫ spMap R.val.toRingHom ∧ LBIso L (M.pull ρ) := by
  have h : (⊥ : Subalgebra k C).FG := Subalgebra.fg_bot
  have := FGAbove.isFiltered h
  obtain ⟨hc⟩ := nonempty_isLimit_baseChange pB h
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom ((baseChangeDiagram (⊥ : Subalgebra k C) pB).map f) :=
    fun _ => isAffineHom_baseChangeMap pB _
  have q : ∀ (A : Type) [CommRing A] [Algebra k A], CompactSpace ↥(pullback pB (spMap (algebraMap k A))) ∧
      QuasiSeparatedSpace ↥(pullback pB (spMap (algebraMap k A))) := by
    intro A _ _
    have q₁ : QuasiCompact (pullback.snd pB (spMap (algebraMap k A))) :=
      quasiCompact_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
    have q₂ : QuasiSeparated (pullback.snd pB (spMap (algebraMap k A))) :=
      quasiSeparated_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (pullback.snd pB (spMap (algebraMap k A))),
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd pB (spMap (algebraMap k A)))⟩
  have : ∀ i, CompactSpace ((baseChangeDiagram (⊥ : Subalgebra k C) pB).obj i) := fun i =>
    (q i.unop.1).1
  have : ∀ i, QuasiSeparatedSpace ((baseChangeDiagram (⊥ : Subalgebra k C) pB).obj i) := fun i =>
    (q i.unop.1).2
  have hc' : IsLimit (schemeConeOfFamily (baseChangeDiagram (⊥ : Subalgebra k C) pB) (X := X)
      (fun R => hX.isoPullback.hom ≫ baseChangeMap pB R.unop.1.val)
      (fun {R T} f => (Category.assoc _ _ _).trans (congrArg _ (baseChangeMap_comp pB
        (Subalgebra.inclusion (show T.unop.1 ≤ R.unop.1 from leOfHom f.unop)) R.unop.1.val)))) :=
    hc.ofIsoLimit (Cone.ext hX.isoPullback.symm fun R => (hX.isoPullback.inv_hom_id_assoc _).symm)
  obtain ⟨R, M, hM, hI⟩ := exists_lb_of_isLimit _ _ _ hc' L hL
  refine ⟨R.unop.1, M, hX.isoPullback.hom ≫ baseChangeMap pB R.unop.1.val, R.unop.2.1, hM, ?_, ?_, hI⟩
  · rw [Category.assoc, baseChangeMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [Category.assoc, baseChangeMap_snd, IsPullback.isoPullback_hom_snd_assoc]

theorem exists_lb_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀)
    (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB →
    IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁),
      (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁),
      IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype →
      ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  intro K _ K₀ X₀ X p₀ p φ _ _ L hL hX
  obtain ⟨R, M, ρ, ⟨s, hs⟩, hM, h₁, h₂, hI⟩ := exists_fg_lb (k := K₀) (C := K) p₀ p φ hX L hL
  refine ⟨s, fun K₁ h hsK X₁ p₁ φ₁ ψ hX₁ e₁ e₂ => ?_⟩
  have hR : ∀ x ∈ R, x ∈ K₁ := by
    intro x hx
    rw [← hs] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hsK hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let ι : R →+* K₁ := R.val.toRingHom.codRestrict K₁ fun x => hR x x.2
  let r : X₁ ⟶ pullback p₀ (spMap (algebraMap K₀ R)) := pullback.lift φ₁ (p₁ ≫ spMap ι) (by
    rw [hX₁.w, Category.assoc, spMap_comp_ring]
    rfl)
  have hr : ψ ≫ r = ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, e₁, h₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e₂, h₂, Category.assoc, spMap_comp_ring]
      rfl
  exact ⟨M.pull r, pull_isLB hM r, LBIso.chartPull (chartPullId L)
    (chartPullLinComb M r (fun _ : PUnit => ψ) (fun _ => ρ) (fun _ => 1) (𝟙 X)
      (fun _ => hr.trans (Category.id_comp _).symm)) hI⟩

end GlobalTheory.LBDescent
