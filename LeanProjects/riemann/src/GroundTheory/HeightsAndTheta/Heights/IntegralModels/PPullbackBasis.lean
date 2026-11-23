import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

noncomputable section

universe u

namespace PullbackBasis

variable {X : Scheme.{u}}

def unitFn (V : X.Opens) (r : Γ(X, V)) : Γ(structureModule X, V) := r

lemma unitFn_eq_smul (V : X.Opens) (r : Γ(X, V)) : unitFn V r = r • unitFn V 1 :=
  (mul_one r).symm

lemma res_unitFn_one {V W : X.Opens} (h : V ≤ W) :
    ((structureModule X).presheaf.map (homOfLE h).op).hom (unitFn W 1) = unitFn V 1 :=
  map_one (X.presheaf.map (homOfLE h).op).hom

def sectionOf (N : X.Modules) {W : X.Opens} (hW : ⊤ ≤ W) (t : Γ(N, W)) : N.val.sections :=
  ⟨fun j => (N.presheaf.map (homOfLE (le_top.trans hW : j.unop ≤ W)).op).hom t,
    fun {j j'} g => by
      change (N.presheaf.map g).hom ((N.presheaf.map (homOfLE _).op).hom t) =
        (N.presheaf.map (homOfLE _).op).hom t
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl⟩

def homOfSection (N : X.Modules) {W : X.Opens} (hW : ⊤ ≤ W) (t : Γ(N, W)) :
    structureModule X ⟶ N :=
  (SheafOfModules.unitHomEquiv N).symm (sectionOf N hW t)

lemma homOfSection_app (N : X.Modules) {W : X.Opens} (hW : ⊤ ≤ W) (t : Γ(N, W)) (V : X.Opens)
    (r : Γ(X, V)) :
    (homOfSection N hW t).app V (unitFn V r) =
      r • (N.presheaf.map (homOfLE (le_top.trans hW : V ≤ W)).op).hom t := by
  have e : (homOfSection N hW t).app V (unitFn V 1) =
      (N.presheaf.map (homOfLE (le_top.trans hW : V ≤ W)).op).hom t := by
    have hs := congrArg (fun x : N.val.sections => x.val (op V))
      ((SheafOfModules.unitHomEquiv N).apply_symm_apply (sectionOf N hW t))
    exact hs
  rw [← e, ← Scheme.Modules.Hom.app_smul, ← unitFn_eq_smul]

lemma eq_homOfSection {N : X.Modules} (φ : structureModule X ⟶ N) {W : X.Opens} (hW : ⊤ ≤ W) :
    φ = homOfSection N hW (φ.app W (unitFn W 1)) := by
  refine Scheme.Modules.hom_ext _ _ fun U => ConcreteCategory.hom_ext _ _ fun x => ?_
  have key : ∀ y : Γ(X, U), φ.app U (unitFn U y) =
      (homOfSection N hW (φ.app W (unitFn W 1))).app U (unitFn U y) := by
    intro y
    rw [homOfSection_app, ← app_map_apply, res_unitFn_one, unitFn_eq_smul,
      Scheme.Modules.Hom.app_smul]
  exact key x

lemma unit_hom_ext {N : X.Modules} {φ ψ : structureModule X ⟶ N} {W : X.Opens} (hW : ⊤ ≤ W)
    (h : φ.app W (unitFn W 1) = ψ.app W (unitFn W 1)) : φ = ψ := by
  rw [eq_homOfSection φ hW, eq_homOfSection ψ hW, h]

variable (X) in

abbrev freeRank (n : ℕ) : X.Modules := ⨁ fun _ : Fin n => structureModule X

def basisHom (N : X.Modules) {W : X.Opens} (hW : ⊤ ≤ W) {n : ℕ} (t : Fin n → Γ(N, W)) :
    freeRank X n ⟶ N :=
  biproduct.desc fun i => homOfSection N hW (t i)

def freeSec {n : ℕ} (V : X.Opens) (r : Fin n → Γ(X, V)) : Γ(freeRank X n, V) :=
  ∑ i, (biproduct.ι (fun _ : Fin n => structureModule X) i).app V (unitFn V (r i))

def freeCoord {n : ℕ} (V : X.Opens) (m : Γ(freeRank X n, V)) (j : Fin n) : Γ(X, V) :=
  (biproduct.π (fun _ : Fin n => structureModule X) j).app V m

lemma freeSec_bijective {n : ℕ} (V : X.Opens) : Function.Bijective (freeSec (X := X) (n := n) V) := by
  refine Function.bijective_iff_has_inverse.2 ⟨freeCoord V, fun r => ?_, fun m => ?_⟩
  · funext j
    rw [freeCoord, freeSec, map_sum, Finset.sum_eq_single j]
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, biproduct.ι_π_self]
      rfl
    · intro i _ hij
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, biproduct.ι_π_ne _ hij]
      rfl
    · simp
  · exact (GroundTheory.Arith.SchemeCoh.biproduct_app_eq_sum _ V m).symm

lemma basisHom_app_freeSec (N : X.Modules) {W : X.Opens} (hW : ⊤ ≤ W) {n : ℕ}
    (t : Fin n → Γ(N, W)) (V : X.Opens) (r : Fin n → Γ(X, V)) :
    (basisHom N hW t).app V (freeSec V r) =
      ∑ i, r i • (N.presheaf.map (homOfLE (le_top.trans hW : V ≤ W)).op).hom (t i) := by
  rw [freeSec, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, basisHom, biproduct.ι_desc,
    homOfSection_app]

lemma isBasisOn_iff_isIso (N : X.Modules) {W : X.Opens} (hW : ⊤ ≤ W) {n : ℕ}
    (t : Fin n → Γ(N, W)) : IsBasisOn N W t ↔ IsIso (basisHom N hW t) := by
  have comm : ∀ (V : X.Opens) (h : V ≤ W),
      (fun r : Fin n → Γ(X, V) => ∑ i, r i • (N.presheaf.map (homOfLE h).op).hom (t i)) =
        (basisHom N hW t).app V ∘ freeSec V := by
    intro V h
    funext r
    exact (basisHom_app_freeSec N hW t V r).symm
  constructor
  · intro hb
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    have := hb V (le_top.trans hW)
    rw [comm] at this
    exact (Function.Bijective.of_comp_iff _ (freeSec_bijective V)).1 this
  · intro hI V h
    rw [comm]
    exact (ConcreteCategory.bijective_of_isIso _).comp (freeSec_bijective V)

section Pull

variable {T Z : Scheme.{u}}

open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)

lemma pullbackStructureIso_inv_one (g : T ⟶ Z) :
    (pullbackStructureIso g).inv.app (g ⁻¹ᵁ ⊤) (unitFn (g ⁻¹ᵁ ⊤) 1) =
      pullbackUnitApp g (structureModule Z) ⊤ (unitFn ⊤ 1) := by
  have h := GroundTheory.Arith.SchemeCoh.pullbackUnitIso_hom_one g
  have h2 := congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤).hom
      (pullbackUnitApp g (SheafOfModules.unit Z.ringCatSheaf) ⊤
        (GroundTheory.Arith.SchemeCoh.unitOne Z ⊤)))
    (pullbackStructureIso g).hom_inv_id
  exact (congrArg (fun x => (pullbackStructureIso g).inv.app ⊤ x) h).symm.trans h2

lemma homOfSection_pull (g : T ⟶ Z) (M : Z.Modules) (t : Γ(M, ⊤))
    (hW : ⊤ ≤ g ⁻¹ᵁ (⊤ : Z.Opens)) :
    homOfSection ((Scheme.Modules.pullback g).obj M) hW (pullSectionOn g M ⊤ t) =
      (pullbackStructureIso g).inv ≫ (Scheme.Modules.pullback g).map (homOfSection M le_rfl t) := by
  refine unit_hom_ext hW ?_
  have e1 : (homOfSection ((Scheme.Modules.pullback g).obj M) hW (pullSectionOn g M ⊤ t)).app _
      (unitFn _ 1) = pullSectionOn g M ⊤ t := by
    have hid : homOfLE (le_top.trans hW : g ⁻¹ᵁ (⊤ : Z.Opens) ≤ g ⁻¹ᵁ ⊤) = 𝟙 _ := rfl
    rw [homOfSection_app, one_smul, hid, op_id, CategoryTheory.Functor.map_id]
    rfl
  have e3 : (homOfSection M le_rfl t).app ⊤ (unitFn ⊤ 1) = t := by
    rw [homOfSection_app, one_smul]
    simp
  rw [e1, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, pullbackStructureIso_inv_one,
    GroundTheory.Arith.SchemeCoh.pullbackUnitApp_naturality, e3]
  rfl

lemma isBasisOn_pull_top (g : T ⟶ Z) (M : Z.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤))
    (hs : IsBasisOn M ⊤ s) :
    IsBasisOn ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ ⊤)
      (fun i => pullSectionOn g M ⊤ (s i)) := by
  have hW : ⊤ ≤ g ⁻¹ᵁ (⊤ : Z.Opens) := fun x _ => trivial
  have := (isBasisOn_iff_isIso M le_rfl s).1 hs
  rw [isBasisOn_iff_isIso _ hW]
  have e : basisHom ((Scheme.Modules.pullback g).obj M) hW (fun i => pullSectionOn g M ⊤ (s i)) =
      (biproduct.mapIso fun _ : Fin n => (pullbackStructureIso g).symm).hom ≫
        ((Scheme.Modules.pullback g).mapBiproduct (fun _ : Fin n => structureModule Z)).inv ≫
          (Scheme.Modules.pullback g).map (basisHom M le_rfl s) := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    rw [basisHom, biproduct.ι_desc, homOfSection_pull]
    simp only [biproduct.mapIso_hom, Iso.symm_hom, biproduct.ι_map_assoc,
      Iso.cancel_iso_inv_left, Functor.mapBiproduct_inv]
    rw [biproduct.ι_desc_assoc, ← Functor.map_comp, basisHom, biproduct.ι_desc]
  rw [e]
  infer_instance

end Pull

section Pull

variable {S T Y Z : Scheme.{u}}

open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)

lemma isBasisOn_pull_of_top (g : T ⟶ Z) (M : Z.Modules) {W : Z.Opens} (hW : ⊤ ≤ W) {n : ℕ}
    (s : Fin n → Γ(M, W)) (hs : IsBasisOn M W s) :
    IsBasisOn ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
      (fun i => pullSectionOn g M W (s i)) := by
  obtain rfl : W = ⊤ := top_le_iff.mp hW
  exact isBasisOn_pull_top g M s hs

lemma pullSectionOn_sum_res (j : Y ⟶ Z) (N : Z.Modules) {O V : Z.Opens} (h : V ≤ O) {n : ℕ}
    (t : Fin n → Γ(N, O)) (r : Fin n → Γ(Z, V)) :
    pullSectionOn j N V (∑ i, r i • (N.presheaf.map (homOfLE h).op).hom (t i)) =
      ∑ i, (j.app V).hom (r i) • (((Scheme.Modules.pullback j).obj N).presheaf.map
        (homOfLE ((Opens.map j.base).monotone h)).op).hom (pullSectionOn j N O (t i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul j N V (r i) _).trans
    (congrArg _ (pullbackUnitApp_res j N (homOfLE h) (t i)))

lemma isBasisOn_pull_iff (j : Y ⟶ Z) [IsOpenImmersion j] (N : Z.Modules) {O : Z.Opens}
    (hO : O ≤ j.opensRange) {n : ℕ} (t : Fin n → Γ(N, O)) :
    IsBasisOn ((Scheme.Modules.pullback j).obj N) (j ⁻¹ᵁ O) (fun i => pullSectionOn j N O (t i)) ↔
      IsBasisOn N O t := by
  have key : ∀ (V : Z.Opens) (h : V ≤ O),
      Function.Bijective (fun r : Fin n → Γ(Y, j ⁻¹ᵁ V) =>
        ∑ i, r i • (((Scheme.Modules.pullback j).obj N).presheaf.map
          (homOfLE ((Opens.map j.base).monotone h)).op).hom (pullSectionOn j N O (t i))) ↔
      Function.Bijective (fun r : Fin n → Γ(Z, V) =>
        ∑ i, r i • (N.presheaf.map (homOfLE h).op).hom (t i)) := by
    intro V h
    have hV : V ≤ j.opensRange := h.trans hO
    have b1 : Function.Bijective (fun (r : Fin n → Γ(Z, V)) (i : Fin n) => (j.app V).hom (r i)) := by
      have := Scheme.Hom.isIso_app j V hV
      exact (Equiv.piCongrRight fun _ =>
        Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso (j.app V))).bijective
    have b2 : Function.Bijective (pullSectionOn j N V) := pullbackUnitApp_bijective j N hV
    have comm : (fun r : Fin n → Γ(Y, j ⁻¹ᵁ V) =>
        ∑ i, r i • (((Scheme.Modules.pullback j).obj N).presheaf.map
          (homOfLE ((Opens.map j.base).monotone h)).op).hom (pullSectionOn j N O (t i))) ∘
          (fun (r : Fin n → Γ(Z, V)) (i : Fin n) => (j.app V).hom (r i)) =
        pullSectionOn j N V ∘
          (fun r : Fin n → Γ(Z, V) => ∑ i, r i • (N.presheaf.map (homOfLE h).op).hom (t i)) := by
      funext r
      exact (pullSectionOn_sum_res j N h t r).symm
    constructor
    · intro hl
      have := hl.comp b1
      rw [comm] at this
      exact (Function.Bijective.of_comp_iff' b2 _).1 this
    · intro hr
      have := b2.comp hr
      rw [← comm] at this
      exact (Function.Bijective.of_comp_iff _ b1).1 this
  constructor
  · intro hb V h
    exact (key V h).1 (hb (j ⁻¹ᵁ V) ((Opens.map j.base).monotone h))
  · intro hb V' h'
    obtain ⟨V, hVO, rfl⟩ : ∃ V, V ≤ O ∧ V' = j ⁻¹ᵁ V :=
      ⟨j ''ᵁ V', (j.image_mono h').trans (j.image_preimage_le O), (j.preimage_image_eq V').symm⟩
    exact (key V hVO).2 (hb V hVO)

lemma isBasisOn_pull_comp (c : S ⟶ Y) (d : Y ⟶ Z) (N : Z.Modules) (O : Z.Opens) {n : ℕ}
    (t : Fin n → Γ(N, O))
    (h : IsBasisOn ((Scheme.Modules.pullback (c ≫ d)).obj N) ((c ≫ d) ⁻¹ᵁ O)
      (fun i => pullSectionOn (c ≫ d) N O (t i))) :
    IsBasisOn ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj N))
      (c ⁻¹ᵁ (d ⁻¹ᵁ O)) (fun i => pullSectionOn c _ (d ⁻¹ᵁ O) (pullSectionOn d N O (t i))) := by
  have h2 := h.of_iso ((Scheme.Modules.pullbackComp c d).app N).symm
  have e : (fun i => pullSectionOn c _ (d ⁻¹ᵁ O) (pullSectionOn d N O (t i))) =
      (fun i => ((((Scheme.Modules.pullbackComp c d).app N).symm.hom.app ((c ≫ d) ⁻¹ᵁ O)).hom
        (pullSectionOn (c ≫ d) N O (t i)))) :=
    funext fun i => (pullbackUnitApp_comp c d N O (t i)).symm
  rw [e]
  exact h2

lemma isBasisOn_of_pull_comp (c : S ⟶ Y) (d : Y ⟶ Z) (N : Z.Modules) (O : Z.Opens) {n : ℕ}
    (t : Fin n → Γ(N, O))
    (h : IsBasisOn ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj N))
      (c ⁻¹ᵁ (d ⁻¹ᵁ O)) (fun i => pullSectionOn c _ (d ⁻¹ᵁ O) (pullSectionOn d N O (t i)))) :
    IsBasisOn ((Scheme.Modules.pullback (c ≫ d)).obj N) ((c ≫ d) ⁻¹ᵁ O)
      (fun i => pullSectionOn (c ≫ d) N O (t i)) := by
  have h2 := h.of_iso ((Scheme.Modules.pullbackComp c d).app N)
  have e : (fun i => pullSectionOn (c ≫ d) N O (t i)) =
      (fun i => ((((Scheme.Modules.pullbackComp c d).app N).hom.app ((c ≫ d) ⁻¹ᵁ O)).hom
        (pullSectionOn c _ (d ⁻¹ᵁ O) (pullSectionOn d N O (t i))))) :=
    funext fun i => (pullbackUnitApp_comp_hom c d N O (t i)).symm
  rw [e]
  exact h2

end Pull

theorem proof : PullbackBasis.Statement.{u} := by
  intro T Z g M U n s hs
  have h1 := (isBasisOn_pull_iff U.ι M (by rw [Scheme.Opens.opensRange_ι]) s).2 hs
  have h2 := isBasisOn_pull_of_top (g ∣_ U) _ (by rw [Scheme.Opens.ι_preimage_self]) _ h1
  have h3 := isBasisOn_of_pull_comp (g ∣_ U) U.ι M U s h2
  rw [morphismRestrict_ι] at h3
  have h4 := isBasisOn_pull_comp (g ⁻¹ᵁ U).ι g M U s h3
  exact (isBasisOn_pull_iff (g ⁻¹ᵁ U).ι _ (by rw [Scheme.Opens.opensRange_ι]) _).1 h4

end PullbackBasis

end

end GroundTheory.Heights₂.Heights.Model
