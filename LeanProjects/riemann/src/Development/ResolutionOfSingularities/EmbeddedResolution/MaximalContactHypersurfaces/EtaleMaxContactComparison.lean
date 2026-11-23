import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

structure EtaleMaxContactComparison (k : Type u) [Field k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (A : P.IdealSheafData) (μ : ℕ) (N : List P.IdealSheafData)
    (H₁ H₂ : P.IdealSheafData) (pt : P) where
  W : Scheme.{u}
  f₁ : W ⟶ P
  f₂ : W ⟶ P
  w : W
  [isAffine : IsAffine W]
  [etale_f₁ : Etale f₁]
  [etale_f₂ : Etale f₂]
  [lft_f₁ : LocallyOfFiniteType (f₁ ≫ p)]
  base_f₁ : f₁.base w = pt
  base_f₂ : f₂.base w = pt
  comap_A : A.comap f₁ = A.comap f₂
  comap_H : H₁.comap f₁ = H₂.comap f₂
  comap_N : ∀ J ∈ N, J.comap f₁ = J.comap f₂
  comp_p : f₁ ≫ p = f₂ ≫ p
  maxContact_comp :
    (@maxContactIdeal k _ _ W (f₁ ≫ p) lft_f₁ (A.comap f₁) μ).subschemeι ≫ f₁ =
      (@maxContactIdeal k _ _ W (f₁ ≫ p) lft_f₁ (A.comap f₁) μ).subschemeι ≫ f₂

private theorem ideal_eq_of_map_eq_of_leftInverse {R S : Type*} [CommRing R] [CommRing S]
    (σ : R →+* S) (τ : S →+* R) (hτσ : τ.comp σ = RingHom.id R)
    {A B : Ideal R} (hmap : Ideal.map σ A = Ideal.map σ B) : A = B := by
  have h2 := congrArg (Ideal.map τ) hmap
  rwa [Ideal.map_map, Ideal.map_map, hτσ, Ideal.map_id, Ideal.map_id] at h2

theorem idealSheafData_eq_of_forall_comap_eq {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : (⋃ i, Set.range ⇑(f i).base) = Set.univ)
    (I J : X.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  have key : ∀ x : X, stalkIdeal I x = stalkIdeal J x := by
    intro x
    have hx : x ∈ (⋃ i, Set.range ⇑(f i).base) := by
      rw [hcov]
      exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy⟩ := Set.mem_range.mp hi
    subst hy
    have hiso : IsIso ((f i).stalkMap y) := inferInstance
    have hinv : (inv ((f i).stalkMap y)).hom.comp ((f i).stalkMap y).hom
        = RingHom.id (X.presheaf.stalk ((f i).base y)) := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id]
    have hmap : Ideal.map ((f i).stalkMap y).hom (stalkIdeal I ((f i).base y))
        = Ideal.map ((f i).stalkMap y).hom (stalkIdeal J ((f i).base y)) := by
      rw [← stalkIdeal_comap (f i) I y, ← stalkIdeal_comap (f i) J y, h i]
    exact ideal_eq_of_map_eq_of_leftInverse _ _ hinv hmap
  refine le_antisymm ?_ ?_
  · exact (le_iff_forall_stalkIdeal_le I J).mpr fun x => le_of_eq (key x)
  · exact (le_iff_forall_stalkIdeal_le J I).mpr fun x => le_of_eq (key x).symm

private theorem comap_eq_ker_pullback_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    I.comap f = Scheme.Hom.ker (Limits.pullback.fst f I.subschemeι) := rfl

open CategoryTheory.Limits in
private theorem iUnion_range_sigmaι_base_eq_univ {ι : Type u} (X : ι → Scheme.{u}) :
    (⋃ i, Set.range ⇑(Sigma.ι X i).base) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk X).surjective x
  have hx' : (Sigma.ι X i).base y = x := by simpa using hx
  exact Set.mem_iUnion.mpr ⟨i, ⟨y, hx'⟩⟩

private theorem derivIdealSheafIterate_congr_of_eq_of_eq (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p q : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (hpq : p = q) (r : ℕ)
    (I J : X.IdealSheafData) (hIJ : I = J) :
    derivIdealSheafIterate k p r I = derivIdealSheafIterate k q r J := by
  subst hpq
  subst hIJ
  rfl

private theorem hom_ext_of_opens_cover {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hcov : ∀ x : ↥X, ∃ i, x ∈ U i) {Q : Scheme.{u}} (a b : X ⟶ Q)
    (hab : ∀ i, (U i).ι ≫ a = (U i).ι ≫ b) : a = b := by
  have hc : ∀ x : ↥X, ∃ i, ∃ y : ↥((U i).toScheme), ((U i).ι).base y = x := by
    intro x
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  exact Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers ι (fun i => (U i).toScheme) (fun i => (U i).ι) hc) a b
    (fun i => hab i)

open CategoryTheory.Limits in
private theorem subschemeι_comp_eq_of_forall_sigmaι_comap {ι : Type u} (Wf : ι → Scheme.{u})
    {Q : Scheme.{u}} (M : (∐ Wf).IdealSheafData) (a b : (∐ Wf) ⟶ Q)
    (h : ∀ i, (M.comap (Sigma.ι Wf i)).subschemeι ≫ Sigma.ι Wf i ≫ a
            = (M.comap (Sigma.ι Wf i)).subschemeι ≫ Sigma.ι Wf i ≫ b) :
    M.subschemeι ≫ a = M.subschemeι ≫ b := by
  refine hom_ext_of_opens_cover
    (fun i => M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange) ?_ _ _ ?_
  · intro x
    have hx : M.subschemeι.base x ∈ (⋃ i, Set.range ⇑(Sigma.ι Wf i).base) := by
      rw [iUnion_range_sigmaι_base_eq_univ]
      trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩
  · intro i
    have hrange : Set.range ⇑((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι
          ≫ M.subschemeι).base ⊆ Set.range ⇑(Sigma.ι Wf i).base := by
      rintro y ⟨z, rfl⟩
      exact z.2
    obtain ⟨α, hα⟩ : ∃ α : (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).toScheme ⟶ Wf i,
        α ≫ Sigma.ι Wf i
          = (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι :=
      ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ hrange⟩
    obtain ⟨β, hβ⟩ : ∃ β : (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).toScheme
          ⟶ pullback (Sigma.ι Wf i) M.subschemeι,
        β ≫ pullback.fst (Sigma.ι Wf i) M.subschemeι = α :=
      ⟨pullback.lift α ((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι) hα,
        pullback.lift_fst _ _ _⟩
    have hker : Scheme.Hom.ker ((M.comap (Sigma.ι Wf i)).subschemeι)
        ≤ Scheme.Hom.ker (pullback.fst (Sigma.ι Wf i) M.subschemeι) := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact le_of_eq (comap_eq_ker_pullback_fst (Sigma.ι Wf i) M)
    obtain ⟨u, hu⟩ : ∃ u : pullback (Sigma.ι Wf i) M.subschemeι
          ⟶ (M.comap (Sigma.ι Wf i)).subscheme,
        u ≫ (M.comap (Sigma.ι Wf i)).subschemeι
          = pullback.fst (Sigma.ι Wf i) M.subschemeι :=
      ⟨IsClosedImmersion.lift _ _ hker, IsClosedImmersion.lift_fac _ _ hker⟩
    have keyA : (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι
        = (β ≫ u) ≫ ((M.comap (Sigma.ι Wf i)).subschemeι ≫ Sigma.ι Wf i) := by
      simp only [Category.assoc]
      rw [← Category.assoc u, hu, ← Category.assoc, hβ, hα]
    have e1 : ((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι) ≫ a
        = ((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι) ≫ b := by
      rw [keyA]
      simp only [Category.assoc]
      rw [h i]
    simpa only [Category.assoc] using e1

open CategoryTheory.Limits in
private theorem exists_etale_maxContactIdeal_comparison_of_finite_cover {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (A : P.IdealSheafData) (μ : ℕ) (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    {ι : Type u} [Finite ι] (pts : ι → ↥P)
    (c : ∀ i, EtaleMaxContactComparison k p A μ N H₁ H₂ (pts i))
    (hcov : orderAtLeastLocus A μ ⊆ ⋃ i, (Set.range ⇑(c i).f₁.base ∩ Set.range ⇑(c i).f₂.base)) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ := by
  classical
  have hWaff : ∀ i, IsAffine (c i).W := fun i => (c i).isAffine
  have hWe₁ : ∀ i, Etale (c i).f₁ := fun i => (c i).etale_f₁
  have hWe₂ : ∀ i, Etale (c i).f₂ := fun i => (c i).etale_f₂
  have hWlft : ∀ i, LocallyOfFiniteType ((c i).f₁ ≫ p) := fun i => (c i).lft_f₁
  have hoi : ∀ i, IsOpenImmersion (Sigma.ι (fun j => (c j).W) i) := fun i => inferInstance
  have hVaff : IsAffine (∐ fun i => (c i).W) := inferInstance
  have he₁ : Etale (Sigma.desc fun i => (c i).f₁) :=
    etale_sigmaDesc (fun i => (c i).f₁) fun i => (c i).etale_f₁
  have he₂ : Etale (Sigma.desc fun i => (c i).f₂) :=
    etale_sigmaDesc (fun i => (c i).f₂) fun i => (c i).etale_f₂
  have hlft : LocallyOfFiniteType ((Sigma.desc fun i => (c i).f₁) ≫ p) := inferInstance
  have hcsV : CompactSpace ↥(∐ fun i => (c i).W) := inferInstance
  have hss : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hqc : QuasiCompact ((Sigma.desc fun i => (c i).f₁) ≫ p) := by
    apply AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
  refine ⟨∐ (fun i => (c i).W), Sigma.desc (fun i => (c i).f₁), Sigma.desc (fun i => (c i).f₂),
    he₁, he₂, hqc, hlft, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun i => ?_
    simp only [← Category.assoc, Sigma.ι_desc]
    exact (c i).comp_p
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
    obtain ⟨w, hw⟩ := hi.1
    refine ⟨(Sigma.ι (fun j => (c j).W) i).base w, ?_⟩
    show (Sigma.ι (fun j => (c j).W) i ≫ Sigma.desc fun j => (c j).f₁).base w = y
    rw [Sigma.ι_desc]
    exact hw
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
    obtain ⟨w, hw⟩ := hi.2
    refine ⟨(Sigma.ι (fun j => (c j).W) i).base w, ?_⟩
    show (Sigma.ι (fun j => (c j).W) i ≫ Sigma.desc fun j => (c j).f₂).base w = y
    rw [Sigma.ι_desc]
    exact hw
  · refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
      (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaι_base_eq_univ _) _ _ fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).comap_A
  · refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
      (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaι_base_eq_univ _) _ _ fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).comap_H
  · refine List.map_congr_left fun J hJ => ?_
    refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
      (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaι_base_eq_univ _) _ _ fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).comap_N J hJ
  · have hMc : ∀ i, (@maxContactIdeal k _ _ (∐ fun j => (c j).W)
          ((Sigma.desc fun j => (c j).f₁) ≫ p) hlft
          (A.comap (Sigma.desc fun j => (c j).f₁)) μ).comap (Sigma.ι (fun j => (c j).W) i)
        = @maxContactIdeal k _ _ (c i).W ((c i).f₁ ≫ p) (hWlft i) (A.comap (c i).f₁) μ := by
      intro i
      rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate,
        ← derivIdealSheafIterate_comap k ((Sigma.desc fun j => (c j).f₁) ≫ p)
          (Sigma.ι (fun j => (c j).W) i) (μ - 1) (A.comap (Sigma.desc fun j => (c j).f₁))]
      refine derivIdealSheafIterate_congr_of_eq_of_eq k _ _ ?_ (μ - 1) _ _ ?_
      · rw [← Category.assoc, Sigma.ι_desc]
      · rw [← Scheme.IdealSheafData.comap_comp, Sigma.ι_desc]
    refine subschemeι_comp_eq_of_forall_sigmaι_comap _ _ _ _ fun i => ?_
    rw [hMc i, Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).maxContact_comp

theorem exists_etale_maxContactIdeal_comparison (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (A : P.IdealSheafData) (μ : ℕ)
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hloc : ∀ pt ∈ orderAtLeastLocus A μ, Nonempty (EtaleMaxContactComparison k p A μ N H₁ H₂ pt)) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ := by
  classical
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcsS : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcP : CompactSpace ↥P := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ
    rwa [Set.preimage_univ] at h
  have hcomp : IsCompact (orderAtLeastLocus A μ) := (isClosed_orderAtLeastLocus k p A μ).isCompact
  have c : ∀ x : ↥(orderAtLeastLocus A μ), EtaleMaxContactComparison k p A μ N H₁ H₂ x.1 :=
    fun x => Classical.choice (hloc x.1 x.2)
  have hopen : ∀ x : ↥(orderAtLeastLocus A μ),
      IsOpen (Set.range ⇑(c x).f₁.base ∩ Set.range ⇑(c x).f₂.base) := by
    intro x
    have := (c x).etale_f₁
    have := (c x).etale_f₂
    exact (c x).f₁.isOpenMap.isOpen_range.inter (c x).f₂.isOpenMap.isOpen_range
  have hsub2 : orderAtLeastLocus A μ ⊆ ⋃ x : ↥(orderAtLeastLocus A μ),
      (Set.range ⇑(c x).f₁.base ∩ Set.range ⇑(c x).f₂.base) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ⟨⟨(c ⟨y, hy⟩).w, (c ⟨y, hy⟩).base_f₁⟩,
      ⟨(c ⟨y, hy⟩).w, (c ⟨y, hy⟩).base_f₂⟩⟩⟩
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover
    (fun x : ↥(orderAtLeastLocus A μ) => Set.range ⇑(c x).f₁.base ∩ Set.range ⇑(c x).f₂.base)
    hopen hsub2
  refine exists_etale_maxContactIdeal_comparison_of_finite_cover p A μ N H₁ H₂
    (fun i : {x : ↥(orderAtLeastLocus A μ) // x ∈ T} => (i.1 : ↥P)) (fun i => c i.1) ?_
  intro y hy
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hT hy)
  obtain ⟨hxT, hmem⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨x, hxT⟩, hmem⟩

end FunctorialResolution.EmbeddedResolution
