import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.GlueFn

theorem le_of_forall_point {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {O W : X.left.Opens}
    (h : ∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ x.left ⁻¹ᵁ O → ⊤ ≤ x.left ⁻¹ᵁ W) : O ≤ W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  by_contra hne
  have hne' : ((O : Set X.left) ∩ (W : Set X.left)ᶜ).Nonempty := by
    obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 hne
    exact ⟨p, hp, hp'⟩
  obtain ⟨c, ⟨hcO, hcW⟩, hc⟩ := nonempty_inter_closedPoints hne'
    (O.isOpen.isLocallyClosed.inter W.isOpen.isClosed_compl.isLocallyClosed)
  have hc' : IsClosed {c} := hc
  let x : 𝟙_ (Over (Sp ℂ)) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom c hc') (pointOfClosedPoint_comp X.hom c hc')
  have hx : ∀ U : X.left.Opens, ⊤ ≤ x.left ⁻¹ᵁ U ↔ c ∈ U := fun U => by
    refine (top_le_preimage_iff_mem (pointOfClosedPoint X.hom c hc') U).trans ?_
    exact (pointOfClosedPoint_apply X.hom c hc' _).symm ▸ Iff.rfl
  exact hcW ((hx W).1 (h x ((hx O).2 hcO)))

theorem ext_val {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {E : Type}
    (e : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (he : Function.Surjective e) (U : X.left.Opens) (f f' : Γ(X.left, U))
    (h : ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ U → valAt' (e z).left U f = valAt' (e z).left U f') : f = f' := by
  refine eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom X inferInstance inferInstance U f f' ?_
  intro x hx
  obtain ⟨z, rfl⟩ := he x
  exact h z hx

theorem existsUnique_glue {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {E : Type}
    (e : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (he : Function.Surjective e) (O : X.left.Opens) (ψ : E → ℂ)
    (h : ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → ∃ (O' : X.left.Opens) (a : Γ(X.left, O')), O' ≤ O ∧
      ⊤ ≤ (e z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (e z').left ⁻¹ᵁ O' → valAt' (e z').left O' a = ψ z') :
    ∃! a : Γ(X.left, O), ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → valAt' (e z).left O a = ψ z := by
  choose U c hUO hzU hc using h
  have hcov : O ≤ ⨆ p : {z // ⊤ ≤ (e z).left ⁻¹ᵁ O}, U p.1 p.2 := by
    refine le_of_forall_point fun x hx => ?_
    obtain ⟨z, rfl⟩ := he x
    exact top_le_preimage_mono _ (le_iSup (fun p : {z // ⊤ ≤ (e z).left ⁻¹ᵁ O} => U p.1 p.2) ⟨z, hx⟩) (hzU z hx)
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.left.sheaf
    (fun p : {z // ⊤ ≤ (e z).left ⁻¹ᵁ O} => U p.1 p.2) O (fun p => homOfLE (hUO p.1 p.2)) hcov
    (fun p => c p.1 p.2) (by
      intro p q
      refine ext_val e he (U p.1 p.2 ⊓ U q.1 q.2) _ _ fun z hz => ?_
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      exact ((valAt'_map _ _ _ hz).trans (hc _ _ z h1)).trans
        ((valAt'_map _ _ _ hz).trans (hc _ _ z h2)).symm)
  have hval : ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → valAt' (e z).left O s = ψ z := fun z hz => by
    rw [← hc z hz z (hzU z hz), ← hs ⟨z, hz⟩]
    exact (valAt'_map _ _ _ (hzU z hz)).symm
  exact ⟨s, hval, fun t ht => ext_val e he O t s fun z hz => (ht z hz).trans (hval z hz).symm⟩

end GlobalTheory.GlueFn

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma exists_complex_section_through_closed_point (X : Scheme) (p : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ q : Spec (CommRingCat.of ℂ) ⟶ X, q ≫ p = 𝟙 _ ∧ ∀ s, q.base s = x := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ p) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = X.fromSpecResidueField x ≫ p :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hφ] at h2
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  letI := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ (X.residueField x) := hft
  haveI : Module.Finite ℂ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing ℂ _
  have hsurj : Function.Surjective (algebraMap ℂ (X.residueField x)) := by
    apply IsSepClosed.algebraMap_surjective
  let e := RingEquiv.ofBijective (algebraMap ℂ (X.residueField x))
    ⟨(algebraMap ℂ _).injective, hsurj⟩
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ)
    ext a
    exact e.symm_apply_apply a
  · intro s
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma valAt'_sub_of_top_le {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (a b : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U (a - b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a - _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dif_pos hU, dif_pos hU, dif_pos hU]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  simp only [map_sub]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma not_mem_basicOpen_of_valAt'_eq_zero {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)
    (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U) (f : Γ(X, U)) (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U f = 0)
    (s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) : q.base s ∉ X.basicOpen f := by
  intro hs
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at hf
  rw [dif_pos hU] at hf
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hf
  have h0 : q.appLE U ⊤ hU f = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hf
    simpa using this
  have hmem : s ∈ q ⁻¹ᵁ X.basicOpen f := hs
  rw [Scheme.Hom.preimage_basicOpen] at hmem
  have hres : (Spec (CommRingCat.of ℂ)).basicOpen (q.appLE U ⊤ hU f) =
      ⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) := by
    rw [← Scheme.basicOpen_res]
    rfl
  rw [h0, Scheme.basicOpen_zero] at hres
  have : s ∈ (⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) :
      (Spec (CommRingCat.of ℂ)).Opens) := ⟨trivial, hmem⟩
  rw [← hres] at this
  exact this

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma valAt'_presheaf_map {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) {U V : X.Opens} (i : V ⟶ U)
    (hV : ⊤ ≤ q ⁻¹ᵁ V) (a : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q V (X.presheaf.map i.op a) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := fun s hs => i.le (hV hs)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dif_pos hU, dif_pos hV]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  rw [← Scheme.Hom.map_appLE q hV i.op]
  rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in

theorem _root_.GlobalTheory.existsUnique_section_of_locally_regular :
    ∀ (P₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), _root_.GlobalTheory.KS.GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
  intro P₀ u Hm χ _ O h H
  haveI := P₀.smoothDim
  have hsm : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g P₀.A.hom
  haveI := hsm
  haveI : IsReduced P₀.A.left := _root_.GlobalTheory.isReduced_of_smooth_complex _ _ hsm
  haveI : JacobsonSpace P₀.A.left := LocallyOfFiniteType.jacobsonSpace P₀.A.hom
  have hpt : ∀ y : P₀.A.left, IsClosed ({y} : Set P₀.A.left) →
      ∃ z, ∀ s, (u.ex z).left.base s = y := by
    intro y hy
    obtain ⟨q, hq, hqy⟩ := exists_complex_section_through_closed_point P₀.A.left P₀.A.hom y hy
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk q hq : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ P₀.A)
    exact ⟨z, fun s => by rw [hz]; exact hqy s⟩
  have hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ := IsLocalRing.closedPoint ℂ
  have huniq : ∀ (V : P₀.A.left.Opens) (a b : Γ(P₀.A.left, V)), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V a = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V b) → a = b := by
    intro V a b hab
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
    by_contra hne
    obtain ⟨y, hyB, hyc⟩ := nonempty_inter_closedPoints
      ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
      (P₀.A.left.basicOpen (a - b)).isOpen.isLocallyClosed
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ V := fun s _ => by
      show (u.ex z).left.base s ∈ V
      rw [hz]
      exact P₀.A.left.basicOpen_le _ hyB
    have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V (a - b) = 0 := by
      rw [valAt'_sub_of_top_le _ _ hzV, hab z hzV, sub_self]
    exact not_mem_basicOpen_of_valAt'_eq_zero _ _ hzV _ h0 hs₀ (by rw [hz]; exact hyB)
  have hloc : ∀ w : {z // ⊤ ≤ (u.ex z).left ⁻¹ᵁ O}, ∃ (O' : P₀.A.left.Opens)
      (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex w.1).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z' := fun w => H w.1 w.2
  choose W aW hWO hWz hWv using hloc
  have hcover : O ≤ iSup W := by
    by_contra hle
    have hZ : ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ).Nonempty := by
      rw [← Set.diff_eq, Set.diff_nonempty]
      exact hle
    have hZlc : IsLocallyClosed ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ) :=
      ⟨O, ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ, O.isOpen, (iSup W).isOpen.isClosed_compl, rfl⟩
    obtain ⟨y, ⟨hyO, hyW⟩, hyc⟩ := nonempty_inter_closedPoints hZ hZlc
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O := fun s _ => by
      show (u.ex z).left.base s ∈ O
      rw [hz]
      exact hyO
    have hyz : y ∈ W ⟨z, hzO⟩ := by
      rw [← hz hs₀]
      exact hWz ⟨z, hzO⟩ (show hs₀ ∈ (⊤ : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) from trivial)
    exact hyW (TopologicalSpace.Opens.mem_iSup.mpr ⟨_, hyz⟩)
  have hcompat : TopCat.Presheaf.IsCompatible P₀.A.left.sheaf.obj W aW := by
    intro i j
    apply huniq
    intro z hz
    have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W i := fun s hs => (inf_le_left : W i ⊓ W j ≤ W i) (hz hs)
    have hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W j := fun s hs => (inf_le_right : W i ⊓ W j ≤ W j) (hz hs)
    erw [valAt'_presheaf_map _ _ hz, valAt'_presheaf_map _ _ hz]
    rw [hWv i z hi, hWv j z hj]
  obtain ⟨a, ha, -⟩ := P₀.A.left.sheaf.existsUnique_gluing' W O (fun i => homOfLE (hWO i))
    hcover aW hcompat
  have hval : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
    intro z hz
    rw [← valAt'_presheaf_map (u.ex z).left (homOfLE (hWO ⟨z, hz⟩)) (hWz ⟨z, hz⟩) a]
    erw [ha ⟨z, hz⟩]
    exact hWv ⟨z, hz⟩ z (hWz ⟨z, hz⟩)
  refine ⟨a, hval, fun b hb => huniq O b a fun z hz => ?_⟩
  rw [hb z hz, hval z hz]

end GlobalTheory
