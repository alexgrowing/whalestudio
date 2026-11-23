import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.NotExistsOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatQuasicoherentLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatAffineAvoiding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

noncomputable section

namespace UpperTheory.ProjForm

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Vert GlobalTheory.Twist

section CutPull

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X}

private theorem homEquiv_pullbackZIso_hom (hL : L.IsLB) (G : X.Modules) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackZIso G f hL n).hom =
      Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist G (lbZPow L n)) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom G (lbZPow L n) f) =
        Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
          (projIso (lbZPow L n) f _).inv :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [Adjunction.homEquiv_unit, pullbackZIso, Iso.trans_hom, Functor.map_comp, ← Category.assoc,
    pullbackIso_hom, e, projZIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]

private theorem pullback_mulSecOfEq (hL : L.IsLB) (G : X.Modules) {n m k : ℤ} (σ : LB.Sec (lbZPow L m))
    (h : n + m = k) :
    (Scheme.Modules.pullback f).map (mulSecOfEq G σ h) ≫ (pullbackZIso G f hL k).hom =
      (pullbackZIso G f hL n).hom ≫ mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackZIso_hom, homEquiv_pullbackZIso_hom, Category.assoc]
  have e := projZIso_mulSecOfEq f hL ((Scheme.Modules.pullback f).obj G) σ h
  have e' : (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv ≫
      (Scheme.Modules.pushforward f).map (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) =
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h ≫
          (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e
  rw [e', ← Category.assoc, ← Category.assoc]
  congr 1
  exact (mulSecOfEq_naturality σ h _).symm

end CutPull

private theorem cut_pullback_iso : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent] {L : LB X} (hL : L.IsLB) (s : L.Sec) (hL' : (L.pull f).IsLB), Nonempty ((Scheme.Modules.pullback f).obj (cut G hL s) ≅ cut ((Scheme.Modules.pullback f).obj G) hL' (GlobalTheory.secPull s f)) := by
  intro X Y f G _ L hL s hL'
  have : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  have hz : ∀ j, zfun (zpull f (zofSec s)) j = zfun (zofSec (GlobalTheory.secPull s f)) j := fun j => by
    rw [zfun_zpull, zfun_zofSec, zfun_zofSec]
    rfl
  have hM : mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f (zofSec s)) (neg_add_cancel (1 : ℤ)) =
      mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (GlobalTheory.secPull s f)) (neg_add_cancel (1 : ℤ)) :=
    zhom_ext fun V t j => by rw [zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, hz]
  have e := pullback_mulSecOfEq f hL G (zofSec s) (neg_add_cancel (1 : ℤ))
  rw [hM, ← Iso.eq_comp_inv] at e
  have key : (Scheme.Modules.pullback f).map (cutHom G hL s) =
      (pullbackZIso G f hL (-1)).hom ≫
        (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (GlobalTheory.secPull s f)) (neg_add_cancel (1 : ℤ)) ≫
          ((pullbackZIso G f hL 0).symm ≪≫ (Scheme.Modules.pullback f).mapIso (twistZZeroIso G hL).symm).hom) := by
    rw [cutHom, Functor.map_comp, e]
    simp
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) (cutHom G hL s) ≪≫ cokernelIsoOfEq key ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    (cokernelCompIsIso _ (twistZZeroIso ((Scheme.Modules.pullback f).obj G) hL').inv).symm⟩

open TensorProduct in

private theorem nontrivial_fibre_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

private theorem mem_support_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_of_isBaseChange hl _ _ rfl

private theorem support_pullback' {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  ext y
  obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
  have hfy : f y ∈ V := e hy
  rw [Set.mem_preimage, mem_support_iff_primeIdealOf hU ⟨y, hy⟩,
    mem_support_iff_primeIdealOf hV ⟨f y, hfy⟩]
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have := finite_sections G hV
  rw [mem_support_of_isBaseChange (isBaseChange_pullbackSections f G hU hV e)]
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hy
  convert Iff.rfl using 2
  exact h.symm

set_option backward.isDefEq.respectTransparency.types false in

private theorem fibre_finite_isClosed_of_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V))
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU
  haveI hg : IsFinite (f ∣_ V) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := by
      rw [Scheme.Opens.ι_image_top]; exact hfin
    have h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite := fun e _ =>
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2
    rw [morphismRestrict_appTop]
    exact (h2 _).comp h1
  have hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V := fun y hy => by
    show f.base y ∈ V
    rw [hy]; exact hxV
  have hres : ∀ (y : Y) (hy : f.base y = x),
      (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme) := by
    intro y hy
    exact Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)
  refine ⟨?_, ?_⟩
  · refine (((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image
      (f ⁻¹ᵁ V).ι.base).subset ?_
    intro y hy
    exact ⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩
  · intro y hy
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [← specializes_iff_mem_closure] at hz
    have hfz : f.base z = x := by
      have h1 : f.base y ⤳ f.base z := hz.map f.base.hom.continuous
      rw [hy, specializes_iff_mem_closure, hx.closure_eq] at h1
      exact h1
    have hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩ :=
      (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz
    have hdisc := ((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype
    have hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳
        ⟨_, hres z hfz⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    have := congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq
    exact (Set.mem_singleton_iff.2 this.symm)

private theorem chiLen_eq_length_sections {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (R : Type) [CommRing R]
    [Algebra R Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] (h : suppDim F ≤ 0) :
    chiLen R F = (Module.length R (sectionsOn F ⊤)).toNat := by
  rw [chiLen_eq_sum_range R 1 fun n hn => subsingleton_coh_of_suppDim_le_zero h (by omega)]
  simp [(cohOn.zeroEquiv R F ⊤).length_eq]

private theorem topDim_le_zero_of_finite_closed {T : Type} [TopologicalSpace T] {s : Set T} (hs : s.Finite)
    (hc : ∀ x ∈ s, IsClosed ({x} : Set T)) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := hs.to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

private def FreeOver {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (n : ℕ) : Prop :=
  ∀ x ∈ U, ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f ⁻¹ᵁ V) ∧
    (letI := (f.app V).hom.toAlgebra
     Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧
      Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n)

private theorem chiLen_pullback_eq_mul (O : Type) [CommRing O] {X Y : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X)
    (hO : ∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r)
    (U : X.Opens) (n : ℕ) (hU : FreeOver f U n) (G : X.Modules) [IsFiniteQC G]
    (hdim : suppDim G ≤ 0) (hsub : support G ⊆ (U : Set X)) :
    chiLen O ((Scheme.Modules.pullback f).obj G) = n * chiLen O G := by
  classical
  have hfin : (support G).Finite := finite_support_of_suppDim_le_zero hdim
  have hcl : ∀ x ∈ support G, IsClosed ({x} : Set X) := fun x hx =>
    isClosed_singleton_of_suppDim_le_zero hdim hx
  have key : ∀ x : support G, ∃ W : X.Opens, x.1 ∈ W ∧ (∀ y ∈ support G \ {x.1}, y ∉ W) ∧
      IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧
      (letI := (f.app W).hom.toAlgebra; Module.Free Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧
        Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.finrank Γ(X, W) Γ(Y, f ⁻¹ᵁ W) = n) := by
    intro x
    obtain ⟨V, hxV, hVa, hV'a, hfree⟩ := hU x.1 (hsub x.2)
    obtain ⟨W, hxW, -, hWT, hWa, hW'a, hWfree⟩ := exists_basicOpen_free_avoiding_finite f n V hVa hV'a hfree x.1 hxV
      (support G \ {x.1}) (hfin.subset Set.diff_subset) (fun y hy => hcl y hy.1) (by simp)
    exact ⟨W, hxW, hWT, hWa, hW'a, hWfree⟩
  choose W hxW hWS hWa hW'a hWfree using key
  letI : Fintype (support G) := hfin.fintype
  have hsupp' : support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G :=
    support_pullback' f G
  have hmem : ∀ x : support G, ∀ y ∈ support G, y ∈ W x → y = x.1 := fun x y hy hyW => by
    by_contra h; exact hWS x y ⟨hy, h⟩ hyW
  have hpts : ∀ y ∈ support ((Scheme.Modules.pullback f).obj G), IsClosed ({y} : Set Y) := by
    intro y hy
    rw [hsupp'] at hy
    exact (fibre_finite_isClosed_of_affine_finite f (W ⟨_, hy⟩) (hWa _) (hW'a _) (hWfree _).2.1 _ (hxW _) (hcl _ hy)).2 y rfl
  have hfin' : (support ((Scheme.Modules.pullback f).obj G)).Finite := by
    rw [hsupp']
    refine (Set.Finite.biUnion (t := fun x => f.base ⁻¹' {x}) hfin fun x hx => (fibre_finite_isClosed_of_affine_finite f (W ⟨x, hx⟩) (hWa _) (hW'a _)
      (hWfree _).2.1 _ (hxW _) (hcl _ hx)).1).subset fun y hy => ?_
    exact Set.mem_biUnion hy rfl
  have hdim' : suppDim ((Scheme.Modules.pullback f).obj G) ≤ 0 :=
    topDim_le_zero_of_finite_closed hfin' hpts
  rw [chiLen_eq_length_sections O _ hdim, chiLen_eq_length_sections O _ hdim',
    length_sectionsOn_top_eq_sum_of_separating G O W (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩)
      (fun i j hij y hy hyi hyj => hij (Subtype.ext ((hmem i y hy hyi).symm.trans (hmem j y hy hyj)))),
    length_sectionsOn_top_eq_sum_of_separating _ O (fun x => f ⁻¹ᵁ W x) ?_ ?_]
  · simp_rw [length_sectionsOn_pullback_of_free O f hO _ n (hWa _) (hW'a _) (hWfree _) G]
    rw [← Finset.mul_sum, ENat.toNat_mul]
    simp
  · intro y hy
    rw [hsupp'] at hy
    exact Set.mem_iUnion.2 ⟨⟨_, hy⟩, hxW _⟩
  · intro i j hij y hy hyi hyj
    rw [hsupp'] at hy
    exact hij (Subtype.ext ((hmem i _ hy hyi).symm.trans (hmem j _ hy hyj)))

private theorem closure_nonzeroLocus_eq_top {X : Scheme.{0}} [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) {S : Set X} (hS : S.Finite) :
    AddSubgroup.closure {c : Pic X | ∃ (N : LB X) (hN : N.IsLB) (t : N.Sec),
      S ⊆ nonzeroLocus t ∧ c = cls N hN} = ⊤ := by
  refine eq_top_iff.2 fun c _ => ?_
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨n, h₁, h₂⟩ := ((hA.eventually_exists_finite_subset_nonzeroLocus hM hS).and
    (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X) hS)).exists
  obtain ⟨P, hP, eP⟩ := cls_surj (cls M hM + n • cls A hA.isLB)
  obtain ⟨Q, hQ, eQ⟩ := cls_surj (cls _ (LB.isLB_triv X) + n • cls A hA.isLB)
  obtain ⟨s, hs⟩ := h₁ P hP eP
  obtain ⟨t, ht⟩ := h₂ Q hQ eQ
  have e : cls M hM = cls P hP - cls Q hQ := by
    rw [eP, eQ, cls_triv, zero_add, add_sub_cancel_right]
  rw [e]
  exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
    (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)

private theorem eq_empty_of_dim_add_one_le_zero {T : Type} [TopologicalSpace T] {S : Set T}
    (h : topologicalKrullDim S + 1 ≤ ((0 : ℕ) : WithBot ℕ∞)) : S = ∅ := by
  by_contra hS
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
  have : Nonempty S := ⟨⟨x, hx⟩⟩
  have hne : topologicalKrullDim S ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← ha] at h
  have h' : ((a + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
  rw [WithBot.coe_le_coe] at h'
  simp at h'

private abbrev cmpFn (k : Type) [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
    (f : Y ⟶ X) (n : ℕ) (G : X.Modules) : Pic X → ℤ :=
  (chiPic k ((Scheme.Modules.pullback f).obj G) ∘ pull f) -
    (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G

set_option backward.isDefEq.respectTransparency false in

private theorem diffVanish_cmpFn (O : Type) [Field O] {X Y : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X)
    (hO : ∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r)
    {A : LB X} (hA : IsAmpleLB A)
    (hX : ∀ (G : X.Modules) [IsFiniteQC G], FiniteCohTwists O G)
    (hY : ∀ (G : Y.Modules) [IsFiniteQC G], FiniteCohTwists O G)
    (U : X.Opens) (n : ℕ) (hU : FreeOver f U n) :
    ∀ (k : ℕ) (G : X.Modules) [IsFiniteQC G], suppDim G ≤ k →
      topologicalKrullDim (support G ∩ (U : Set X)ᶜ : Set X) + 1 ≤ (k : WithBot ℕ∞) →
      DiffVanish k (cmpFn O f n G) := by
  intro k
  induction k with
  | zero =>
    intro G _ h0 hk
    have hGU : support G ⊆ (U : Set X) := fun x hx => by
      by_contra h
      have := eq_empty_of_dim_add_one_le_zero hk
      exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩
    refine diffVanish_zero_iff.2 (funext fun c => ?_)
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    have hM' := Semi.LB.isLB_pull hM f
    have := isFiniteQC_twist (F := G) hM
    have e := pullbackIso G f hM
    have hb := chiLen_pullback_eq_mul O f hO U n hU (twist G M)
      (by rwa [suppDim_twist hM])
      (by rwa [support_twist hM])
    simp only [cmpFn, Pi.sub_apply, Function.comp_apply, Pi.zero_apply, AddMonoidHom.coe_mulLeft]
    rw [← cls_pull hM f hM', chiPic_cls, chiPic_cls, ← chiLen_eq_chi, ← chiLen_eq_chi,
      ← chiLen_congr O e, hb, sub_self]
  | succ k ih =>
    intro G _ hk hUk
    set G' := (Scheme.Modules.pullback f).obj G
    have hZ : IsClosed (support G ∩ (U : Set X)ᶜ) :=
      (isClosed_support (F := G)).inter U.isOpen.isClosed_compl
    obtain ⟨S₃, hS₃, hS₃'⟩ := exists_finite_topologicalKrullDim_inter_add_one_le _ hZ
    let S : Set X := assPoints G ∪ f.base '' assPoints G' ∪ S₃
    have hS : S.Finite := ((finite_assPoints G).union ((finite_assPoints G').image _)).union hS₃
    refine diffVanish_of_generators (closure_nonzeroLocus_eq_top hA hS) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f
    haveI hmono : Mono (cutHom G hN t) :=
      (mono_cutHom_iff G hN t).2 fun x hx => hSt (Or.inl (Or.inl hx))
    haveI hmono' : Mono (cutHom G' hN' (GlobalTheory.secPull t f)) :=
      (mono_cutHom_iff G' hN' _).2 fun x hx => by
        rw [GlobalTheory.nonzeroLocus_secPull]
        exact hSt (Or.inl (Or.inr ⟨x, hx, rfl⟩))
    have h₁ := bwdDiff_chiPic_eq_chiPic_cut hN t (hX G)
    have h₂ := bwdDiff_chiPic_eq_chiPic_cut hN' (GlobalTheory.secPull t f) (hY G')
    obtain ⟨ec⟩ := cut_pullback_iso f G hN t hN'
    have key : bwdDiff (cls N hN) (cmpFn O f n G) = cmpFn O f n (cut G hN t) := by
      funext c
      have a₁ := congrFun h₁ c
      have a₂ := congrFun h₂ (pull f c)
      rw [chiPic_congr O ec.symm] at a₂
      simp only [bwdDiff_apply] at a₁ a₂
      simp only [cmpFn, bwdDiff_apply, Pi.sub_apply, Function.comp_apply,
        AddMonoidHom.coe_mulLeft, map_sub, cls_pull hN f hN'] at a₂ ⊢
      rw [← a₁, ← a₂]
      ring
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    refine ih (cut G hN t) (suppDim_cut_le G hN t hk) ?_ _
    have hdim := hS₃' (nonzeroLocus t : Set X)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))
    have hZk : topologicalKrullDim (support G ∩ (U : Set X)ᶜ : Set X) ≤ k :=
      ENat.WithBot.add_le_add_one_right_iff.1 (hUk.trans_eq (Nat.cast_succ k))
    refine le_trans ?_ (hdim.trans hZk)
    refine add_le_add_left (topologicalKrullDim_mono ?_) 1
    rw [support_cut]
    rintro x ⟨⟨hx, hx'⟩, hxU⟩
    exact ⟨⟨hx, hxU⟩, hx'⟩

private theorem eq_genericPoint {Z' Z : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z] (f : Z' ⟶ Z)
    (hg : f (genericPoint Z') = genericPoint Z) (hdeg : f.residueDegree (genericPoint Z') ≠ 0)
    (x : Z') (hx : f x = genericPoint Z) : x = genericPoint Z' := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  have hηV : genericPoint Z' ∈ V :=
    ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : f (genericPoint Z') ∈ U := hVU hηV
  letI := (Z.evaluation U _ hyU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := ProjFin.isFractionRing_evaluation Z hU hg hyU
  have : Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z'))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))
  have : Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  have : Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _
  have hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV =
      Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z') := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  let ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z') :=
    { (Z'.evaluation V _ hηV).hom with
      commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }
  have hψ : Function.Injective ψ := by
    letI := (Z'.evaluation V _ hηV).hom.toAlgebra
    haveI := ProjFin.isFractionRing_evaluation Z' hV rfl hηV
    exact IsFractionRing.injective Γ(Z', V) (Z'.residueField (genericPoint Z'))
  have halg : Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V) := Algebra.IsAlgebraic.of_injective ψ hψ
  by_contra hne
  have hns : genericPoint Z' ∉ closure ({x} : Set Z') := fun h =>
    hne ((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes x)).eq
  obtain ⟨b, hb, hηb⟩ := hV.exists_basicOpen_le
    (V := ⟨(closure ({x} : Set Z'))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨_, hns⟩ hηV
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hηb
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_algebraic_mem (R := Γ(Z, U)) hb0 (Ideal.mem_span_singleton_self b)
      (halg.1 b))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 ha)
  have h1 : f x ∈ Z.basicOpen a := by
    rw [hx]
    refine ((genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).2).mpr ?_
    rw [Set.univ_inter]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp (by simpa using ha0)
  have h2 : x ∈ Z'.basicOpen (f.appLE U V hVU a) := by
    rw [Scheme.basicOpen_appLE]
    exact ⟨hxV, h1⟩
  have h3 : f.appLE U V hVU a = b * c := hc
  rw [h3, Scheme.basicOpen_mul] at h2
  exact hb h2.1 (subset_closure rfl)

private theorem finrank_app_eq {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z']
    (f : Z' ⟶ Z) (h : f (genericPoint Z') = genericPoint Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen (f ⁻¹ᵁ U)) (hxU : f (genericPoint Z') ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) = f.residueDegree (genericPoint Z') := by
  letI := (f.app U).hom.toAlgebra
  letI := (Z.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    (Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (f.app U ≫ Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := ProjFin.isFractionRing_evaluation Z hU h hxU
  haveI := ProjFin.isFractionRing_evaluation Z' hU' rfl hxU
  exact (IsFractionRing.finrank_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
    Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z'))).symm

private theorem exists_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    [IsFinite (f ∣_ V)] (x : X) (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧ (f.app W).hom.Finite := by
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    V.toScheme.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (⟨x, hx⟩ : V.toScheme))
  refine ⟨V.ι ''ᵁ W, ⟨_, hxW, rfl⟩, hW.image_of_isOpenImmersion _, ?_, ?_⟩
  · rw [← image_morphismRestrict_preimage]
    exact (hW.preimage (f ∣_ V)).image_of_isOpenImmersion _
  · have h := (f ∣_ V).finite_app W hW
    rw [morphismRestrict_app] at h
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).1 h

private theorem exists_basicOpen_free {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Y ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : (f.app V).hom.Finite) (hx : genericPoint X ∈ V) :
    ∃ W : X.Opens, genericPoint X ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧
      (letI := (f.app W).hom.toAlgebra
       Module.Free Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W)) := by
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have hFin : Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := hfin
  have : Module.FinitePresentation Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := Module.finitePresentation_of_finite _ _
  obtain ⟨a, ha, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors Γ(X, V))
    (LocalizedModule.mkLinearMap (nonZeroDivisors Γ(X, V)) Γ(Y, f ⁻¹ᵁ V)) (FractionRing Γ(X, V))
  have hxa : genericPoint X ∈ X.basicOpen a := by
    refine ((genericPoint_spec X).mem_open_set_iff (X.basicOpen a).2).mpr ?_
    rw [Set.univ_inter]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp
      (by simpa using nonZeroDivisors.ne_zero ha)
  refine ⟨X.basicOpen a, hxa, hV.basicOpen a, ?_, ?_⟩
  · rw [Scheme.preimage_basicOpen]; exact hV'.basicOpen _
  letI : Algebra Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    (f.app (X.basicOpen a)).hom.toAlgebra
  let iX : X.basicOpen a ⟶ V := homOfLE (X.basicOpen_le a)
  let iY : f ⁻¹ᵁ X.basicOpen a ⟶ f ⁻¹ᵁ V := homOfLE (fun y hy => X.basicOpen_le a hy)
  letI : Algebra Γ(X, V) Γ(X, X.basicOpen a) := (X.presheaf.map iX.op).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) := (Y.presheaf.map iY.op).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    ((algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V))).toAlgebra
  haveI : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : (algebraMap Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, V) Γ(X, X.basicOpen a)) =
      (algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
        (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V)) :=
    congrArg CommRingCat.Hom.hom (f.naturality iX.op)
  haveI : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' hcomm.symm
  haveI : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  haveI : IsLocalization.Away (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a)
      Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    hV'.isLocalization_of_eq_basicOpen _ iY (Scheme.preimage_basicOpen f a)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ V) (Submonoid.powers a))
      Γ(Y, f ⁻¹ᵁ X.basicOpen a) := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers a)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr this
  have hbc : IsBaseChange Γ(X, X.basicOpen a)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Γ(X, X.basicOpen a) _).mp
      inferInstance
  refine ⟨?_, Module.Finite.equiv hbc.equiv⟩
  let φ := IsLocalization.algEquiv (Submonoid.powers a) (Localization (Submonoid.powers a))
    Γ(X, X.basicOpen a)
  letI : Algebra (Localization (Submonoid.powers a)) Γ(X, X.basicOpen a) :=
    φ.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower Γ(X, V) (Localization (Submonoid.powers a)) Γ(X, X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI := Module.Free.of_equiv
    (LocalizedModule.equivTensorProduct (Submonoid.powers a) Γ(Y, f ⁻¹ᵁ V))
  exact Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, V)
    (Localization (Submonoid.powers a)) Γ(X, X.basicOpen a) Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ V) ≪≫ₗ
      hbc.equiv)

private theorem exists_freeOver {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] (f : Y ⟶ X) [IsProper f] (hg : f (genericPoint Y) = genericPoint X)
    (hdeg : f.residueDegree (genericPoint Y) ≠ 0) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ FreeOver f U (f.residueDegree (genericPoint Y)) := by
  obtain ⟨V, hV, _⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f
    (genericPoint X) ((Set.finite_singleton _).subset fun x hx => eq_genericPoint f hg hdeg x hx)
  obtain ⟨W, hxW, hW, hW', hfin⟩ := exists_affine_finite f V _ hV
  obtain ⟨U, hxU, hU, hU', hfree, hfin'⟩ := exists_basicOpen_free f W hW hW' hfin hxW
  exact ⟨U, hxU, fun x hx => ⟨U, hx, hU, hU', hfree, hfin',
    finrank_app_eq f hg hU hU' (hg ▸ hxU)⟩⟩

end UpperTheory.ProjForm

end

open UpperTheory.ProjForm in
theorem UpperTheory.intersection_number_pullback_degree :
    ∀ (k : Type) [Field k] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (s : X ⟶ Sp k) (f : X' ⟶ X) (d : ℕ), IsProjOver s → IsProjOver (f ≫ s) → topologicalKrullDim X = d → f (genericPoint X') = genericPoint X → f.residueDegree (genericPoint X') ≠ 0 → ∀ L : Fin d → LB X, (∀ i, (L i).IsLB) → (letI := algebraΓOfHom (f ≫ s); interNum k (GlobalTheory.structureModule X') fun i => (L i).pull f) = (f.residueDegree (genericPoint X') : ℤ) * (letI := algebraΓOfHom s; interNum k (GlobalTheory.structureModule X) L) := by
  intro k _ X X' _ _ s f d hs hs' hd hg hdeg L hL
  letI := algebraΓOfHom (f ≫ s)
  letI := algebraΓOfHom s
  have := isNoetherian_of_isProjOver hs
  have := isNoetherian_of_isProjOver hs'
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hs
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hs').1
  have : IsProper f := IsProper.of_comp f s
  obtain ⟨U, hU, hfree⟩ := exists_freeOver f hg hdeg
  have hUd : topologicalKrullDim ((U : Set X)ᶜ : Set X) + 1 ≤ (d : WithBot ℕ∞) := by
    refine (topologicalKrullDim_add_one_le U.isOpen.isClosed_compl isClosed_univ fun x _ =>
      ⟨genericPoint X, trivial, fun h => h hU, genericPoint_specializes x⟩).trans ?_
    exact (topologicalKrullDim_subspace_le X _).trans hd.le
  have hD := diffVanish_cmpFn k f (appTop_algebraΓOfHom f s rfl) hA
    (fun G _ => finiteCohTwists_of_isProjOver (f := s) (fun _ => rfl) G hs)
    (fun G _ => finiteCohTwists_of_isProjOver (f := f ≫ s) (fun _ => rfl) G hs')
    U _ hfree d (GlobalTheory.structureModule X) (suppDim_structureModule.trans_le hd.le)
    (by rw [support_structureModule, Set.univ_inter]; exact hUd)
  obtain ⟨e⟩ := AbLaw.LbSheafModel.pullback_unit (X := X) f
  have e' : (Scheme.Modules.pullback f).obj (GlobalTheory.structureModule X) ≅ GlobalTheory.structureModule X' := e
  have h0 := congrFun (hD fun i => cls (L i) (hL i)) 0
  simp only [cmpFn, multiDiff_sub, multiDiff_map, multiDiff_comap, Pi.sub_apply, Pi.zero_apply,
    Function.comp_apply, chiPic_congr k e', map_zero] at h0
  rw [AddMonoidHom.coe_mulLeft, sub_eq_zero] at h0
  rw [interNum_eq_multiDiff k _ hL, interNum_eq_multiDiff k _ fun i => Semi.LB.isLB_pull (hL i) f]
  exact h0
