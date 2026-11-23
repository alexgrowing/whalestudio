import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

namespace UpperTheory.A

theorem generic_map {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) [Etale c] :
    c (genericPoint Y) = genericPoint Z := by
  have ho : IsOpenMap c := c.isOpenMap
  have hd : DenseRange c := by
    have : (Set.range c).Nonempty := Set.range_nonempty _
    exact (ho.isOpen_range.dense this)
  have h1 := (genericPoint_spec Y).image c.continuous
  rw [Set.image_univ] at h1
  have h2 : closure (Set.range c) = Set.univ := hd.closure_range
  rw [h2] at h1
  exact (h1.eq (genericPoint_spec Z))

noncomputable def ffHom {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) [Etale c] :
    Z.functionField ⟶ Y.functionField :=
  Z.presheaf.stalkSpecializes (specializes_of_eq (generic_map c)) ≫ c.stalkMap (genericPoint Y)

theorem germ_ffHom {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) [Etale c]
    (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) :
    Z.presheaf.germ V (genericPoint Z) hV ≫ ffHom c = c.app V ≫ Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV' := by
  rw [ffHom, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.Hom.germ_stalkMap c V (genericPoint Y) hV'

theorem exists_ffMap {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c : Y ⟶ Z)
    (hc : c ≫ p = p') [Etale c] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField]
    (hK : instK = ffAlg p) (hL : instL = ffAlg p') :
    ∃ ψ : Z.functionField →ₐ[ℂ] Y.functionField,
      ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g) := by
  have aK : ∀ r : ℂ, algebraMap ℂ Z.functionField r = (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    intro r; subst hK; rfl
  have aL : ∀ r : ℂ, algebraMap ℂ Y.functionField r = (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom
      (p'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    intro r; subst hL; rfl
  refine ⟨{ (ffHom c).hom with commutes' := fun r => ?_ }, fun V hV hV' g => ?_⟩
  · have h := germ_ffHom c ⊤ trivial trivial
    have h2 := congrArg (fun f => f.hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r))) h
    change (ffHom c).hom (algebraMap ℂ Z.functionField r) = _
    rw [aK, aL, ← hc, Scheme.Hom.comp_appTop]
    exact h2
  · have h := congrArg (fun f => f.hom g) (germ_ffHom c V hV hV')
    exact h

noncomputable def ringOn {Y : Scheme.{0}} [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [instL : Algebra ℂ Y.functionField]
    (hL : instL = ffAlg p') (W : Y.Opens) (hW : genericPoint Y ∈ W) : Subalgebra ℂ Y.functionField where
  carrier := {y | ∃ f : Γ(Y, W), (Y.presheaf.germ W (genericPoint Y) hW).hom f = y}
  mul_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, map_mul _ _ _⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, map_add _ _ _⟩
  algebraMap_mem' := by
    intro r
    subst hL
    refine ⟨(Y.presheaf.map (homOfLE le_top).op).hom (p'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), ?_⟩
    have := TopCat.Presheaf.germ_res Y.presheaf (homOfLE (le_top : W ≤ ⊤)) (genericPoint Y) hW
    exact congrArg (fun f => f.hom (p'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r))) this

def joinCover {Z Y : Scheme.{0}} {ι : Type} (c1 c2 : Y ⟶ Z) (U : ι → Z.Opens) : ι ⊕ₗ ι → Y.Opens :=
  fun i => Sum.elim (fun j => c1 ⁻¹ᵁ U j) (fun j => c2 ⁻¹ᵁ U j) (ofLex i)

theorem generic_mem_inf {Y : Scheme.{0}} [IsIntegral Y] {κ : Type} (V : κ → Y.Opens) (h : ∀ k, genericPoint Y ∈ V k)
    (I : Finset κ) : genericPoint Y ∈ I.inf V := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact ⟨h a, ih⟩

theorem generic_mem_join {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {ι : Type} (c1 c2 : Y ⟶ Z) [Etale c1] [Etale c2]
    (U : ι → Z.Opens) (hU : ∀ i, genericPoint Z ∈ U i) (k : ι ⊕ₗ ι) : genericPoint Y ∈ joinCover c1 c2 U k := by
  rcases h : ofLex k with j | j
  · simp only [joinCover, h, Sum.elim_inl]
    change c1 (genericPoint Y) ∈ U j
    rw [generic_map c1]; exact hU j
  · simp only [joinCover, h, Sum.elim_inr]
    change c2 (genericPoint Y) ∈ U j
    rw [generic_map c2]; exact hU j

theorem isSeparated_of_hom {Z Y : Scheme.{0}} [Z.IsSeparated] (c : Y ⟶ Z) [IsSeparated c] : Y.IsSeparated := by
  constructor
  have e : Limits.terminal.from Y = c ≫ Limits.terminal.from Z := Subsingleton.elim _ _
  rw [e]
  infer_instance

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_proj {Z : Scheme.{0}} (p : Z ⟶ Sp ℂ) (hP : IsProjOver p) : Z.IsSeparated := by
  obtain ⟨N, i, hi, -⟩ := hP
  haveI := hi
  haveI : (PSpace ℂ N).IsSeparated := isSeparated_of_hom (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ))
  exact isSeparated_of_hom i

theorem isAffineOpen_join {Z Y : Scheme.{0}} [Y.IsSeparated] {ι : Type} (c1 c2 : Y ⟶ Z) [IsFinite c1] [IsFinite c2]
    (U : ι → Z.Opens) (hU : ∀ i, IsAffineOpen (U i)) (I : Finset (ι ⊕ₗ ι)) (hI : I.Nonempty) :
    IsAffineOpen (I.inf (joinCover c1 c2 U)) := by
  classical
  have hk : ∀ k, IsAffineOpen (joinCover c1 c2 U k) := by
    intro k
    rcases h : ofLex k with j | j
    · simp only [joinCover, h, Sum.elim_inl]; exact (hU j).preimage c1
    · simp only [joinCover, h, Sum.elim_inr]; exact (hU j).preimage c2
  induction hI using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hk a
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.inf_insert]
    exact (hk a).inf ih

theorem isAffCover_join {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z)
    [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] (hP : IsProjOver p) [instK : Algebra ℂ Z.functionField]
    [instL : Algebra ℂ Y.functionField] (hL : instL = ffAlg p') {ι : Type} (U : ι → Z.Opens)
    (B : Finset ι → Subalgebra ℂ Z.functionField) (hU : IsAffCover p U B) :
    IsAffCover p' (joinCover c1 c2 U) fun I => ringOn p' hL (I.inf (joinCover c1 c2 U))
      (generic_mem_inf _ (generic_mem_join c1 c2 U fun i => by simpa using hU.ne {i}) I) := by
  haveI := isSeparated_of_proj p hP
  haveI : Y.IsSeparated := isSeparated_of_hom c1
  refine ⟨by subst hL; rfl, fun I hI => ?_, ?_, fun I => generic_mem_inf _ (generic_mem_join c1 c2 U fun i => by simpa using hU.ne {i}) I, fun I _ y => Iff.rfl⟩
  · exact isAffineOpen_join c1 c2 U (fun i => by simpa using hU.affine {i} ⟨i, by simp⟩) I hI
  · refine top_le_iff.1 fun x _ => ?_
    have hx : c1 x ∈ (⊤ : Z.Opens) := trivial
    rw [← hU.cover] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨toLex (Sum.inl i), hi⟩

end UpperTheory.A
