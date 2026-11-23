import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

namespace GluingInclusion

variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))

abbrev cm (V : B.Opens) (h : V ≤ W) : AddMonoidAlgebra Γ(B, V) X →+* Γ(G, q ⁻¹ᵁ V) :=
  AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)

omit [AddCommMonoid X] in
lemma app_res {V₁ V₂ : B.Opens} (h : V₁ ≤ V₂) (c : Γ(B, V₂)) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom ((q.app V₂).hom c) =
      (q.app V₁).hom ((B.presheaf.map (homOfLE h).op).hom c) := by
  have h2 := congrArg (fun f => f.hom c) (q.naturality (homOfLE h).op)
  first
  | exact h2.symm
  | simpa using h2.symm

lemma res_res {Y : Scheme.{0}} {U₁ U₂ U₃ : Y.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (s : Γ(Y, U₃)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom s) =
      (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  have h2 := congrArg (fun f => f.hom s) (Y.presheaf.map_comp (homOfLE h₂).op (homOfLE h₁).op)
  first
  | exact h2.symm
  | simpa using h2.symm

variable (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (x : Multiplicative X),
    φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))

include hnat in
lemma cm_nat {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom.comp (cm q φ V₂ h₂) =
      (cm q φ V₁ h₁).comp (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp [AddMonoidAlgebra.liftNC_single, app_res]
  · intro x
    simp [AddMonoidAlgebra.liftNC_single, hnat V₁ V₂ h₁ h₂ h]

include hnat in
lemma cm_nat_apply {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (p : AddMonoidAlgebra Γ(B, V₂) X) :
    cm q φ V₁ h₁ (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom p) =
      (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (cm q φ V₂ h₂ p) := (congrArg (fun f => f p) (cm_nat q φ hnat h₁ h₂ h)).symm

include hnat in

lemma inj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} (U : ι → B.Opens) (hU : ∀ i, U i ≤ V)
    (hcov : V ≤ iSup U) (hinj : ∀ i, Function.Injective (cm q φ (U i) ((hU i).trans h))) :
    Function.Injective (cm q φ V h) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom p = 0 := by
    intro i
    apply hinj i
    rw [cm_nat_apply q φ hnat ((hU i).trans h) h (hU i), hp, map_zero, map_zero]
  ext x
  apply B.sheaf.eq_of_locally_eq' U V (fun i => homOfLE (hU i)) hcov
  intro i
  have h2 := congrArg (fun r => r.coeff x) (h1 i)
  have h3 : (B.presheaf.map (homOfLE (hU i)).op).hom (p.coeff x) = 0 := by simpa using h2
  refine h3.trans ?_
  exact (map_zero _).symm

include hnat in

lemma surj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} [Finite ι] (U : ι → B.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ iSup U)
    (hsurj : ∀ i, Function.Surjective (cm q φ (U i) ((hU i).trans h)))
    (hinj2 : ∀ i j, Function.Injective (cm q φ (U i ⊓ U j) (inf_le_left.trans ((hU i).trans h)))) :
    Function.Surjective (cm q φ V h) := by
  classical
  intro s
  haveI := Fintype.ofFinite ι
  have hloc : ∀ i, ∃ p : AddMonoidAlgebra Γ(B, U i) X, cm q φ (U i) ((hU i).trans h) p =
      (G.presheaf.map (homOfLE (q.preimage_mono (hU i))).op).hom s := fun i => hsurj i _
  choose p hp using hloc
  have hcompat : ∀ i j,
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (p i) =
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (p j) := by
    intro i j
    apply hinj2 i j
    rw [cm_nat_apply q φ hnat _ ((hU i).trans h) inf_le_left,
      cm_nat_apply q φ hnat _ ((hU j).trans h) inf_le_right, hp i, hp j, res_res, res_res]
  have hcx : ∀ x : X, TopCat.Presheaf.IsCompatible B.sheaf.1 U (fun i => (p i).coeff x) := by
    intro x i j
    have e := congrArg (fun r => r.coeff x) (hcompat i j)
    simp only [AddMonoidAlgebra.coeff_mapRingHom] at e
    exact e
  have hglue : ∀ x : X, ∃ c : Γ(B, V), ∀ i, (B.presheaf.map (homOfLE (hU i)).op).hom c = (p i).coeff x := by
    intro x
    obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' B.sheaf U V (fun i => homOfLE (hU i)) hcov
      (fun i => (p i).coeff x) (hcx x)
    exact ⟨c, hc⟩
  choose c hc using hglue
  let S : Finset X := Finset.univ.biUnion (fun i => (p i).coeff.support)
  let F : X →₀ Γ(B, V) := ∑ x ∈ S, Finsupp.single x (c x)
  have hF : ∀ x, F x = if x ∈ S then c x else 0 := by
    intro x
    simp [F, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hres : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom
      (AddMonoidAlgebra.ofCoeff F) = p i := by
    intro i
    apply AddMonoidAlgebra.coeff_injective
    ext x
    rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_ofCoeff, hF]
    split_ifs with hx
    · exact hc x i
    · rw [map_zero]
      symm
      by_contra hne
      exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hne⟩)
  refine ⟨AddMonoidAlgebra.ofCoeff F, ?_⟩
  have hcovG : q ⁻¹ᵁ V ≤ iSup (fun i => q ⁻¹ᵁ U i) := by
    have e := q.preimage_mono hcov
    rw [Scheme.Hom.preimage_iSup] at e
    exact e
  apply TopCat.Sheaf.eq_of_locally_eq' G.sheaf (fun i => q ⁻¹ᵁ U i) (q ⁻¹ᵁ V)
    (fun i => homOfLE (q.preimage_mono (hU i))) hcovG
  intro i
  have e1 := cm_nat_apply q φ hnat ((hU i).trans h) h (hU i) (AddMonoidAlgebra.ofCoeff F)
  rw [hres i, hp i] at e1
  exact e1.symm

end GluingInclusion

open GluingInclusion in

theorem coord_glue {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
    (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
    (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) (x : Multiplicative X),
      φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
    (hgood : ∀ x ∈ W, ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, x ∈ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀),
      IsAffineOpen V₁ → Function.Bijective
        (AddMonoidAlgebra.liftNCRingHom (q.app V₁).hom (φ V₁ (h₁.trans hV₀))
          (fun _ _ => Commute.all _ _)))
    (V : B.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)) := by
  classical
  have hbasis := AlgebraicGeometry.Scheme.isBasis_affineOpens B
  have hloc : ∀ x ∈ W, ∀ O : B.Opens, x ∈ O → ∃ A : B.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ O ∧
      ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ →
        Function.Bijective (cm q φ V₁ (h₁.trans hV₀)) := by
    intro x hx O hxO
    obtain ⟨V₀, hV₀, hxV₀, hb⟩ := hgood x hx
    obtain ⟨A, hA, hxA, hAle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis) (show x ∈ O ⊓ V₀ from ⟨hxO, hxV₀⟩)
    exact ⟨A, hA, hxA, hAle.trans inf_le_left, V₀, hV₀, hAle.trans inf_le_right, hb⟩
  have hinj : ∀ (O : B.Opens) (hO : O ≤ W), Function.Injective (cm q φ O hO) := by
    intro O hO
    let ι := {A : B.Opens // IsAffineOpen A ∧ A ≤ O ∧ ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧
      ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ → Function.Bijective (cm q φ V₁ (h₁.trans hV₀))}
    refine inj_of_cover q φ hnat hO (fun a : ι => a.1) (fun a => a.2.2.1) ?_ ?_
    · intro x hx
      obtain ⟨A, hA, hxA, hAO, rest⟩ := hloc x (hO hx) O hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨A, hA, hAO, rest⟩, hxA⟩
    · intro a
      obtain ⟨V₀, hV₀, hAV₀, hb⟩ := a.2.2.2
      exact (hb a.1 hAV₀ a.2.1).1
  constructor
  · exact hinj V h
  · have hx : ∀ x ∈ V, ∃ A : B.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ V ∧
        ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ →
          Function.Bijective (cm q φ V₁ (h₁.trans hV₀)) := fun x hxV => hloc x (h hxV) V hxV
    choose A hA using hx
    obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (A x.1 x.2 : Set B))
      (fun x => (A x.1 x.2).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hA y hy).2.1⟩)
    refine surj_of_cover q φ hnat h (fun i : t => A i.1.1 i.1.2) (fun i => (hA _ _).2.2.1) ?_ ?_
      (fun i j => hinj _ _)
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
    · intro i
      obtain ⟨V₀, hV₀, hAV₀, hb⟩ := (hA _ _).2.2.2
      exact (hb _ hAV₀ (hA _ _).1).2

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
