import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry

universe w w' u

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)

section Map

variable {P P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}

lemma push_add (φ ψ : P ⟶ P') (n : ℕ) (σ : Cochain P U n) :
    push U (φ + ψ) n σ = push U φ n σ + push U ψ n σ := by
  funext i
  simp [push]

lemma push_mem_cocycles (φ : P ⟶ P') {n : ℕ} {σ : Cochain P U n} (hσ : σ ∈ cocycles P U n) :
    push U φ n σ ∈ cocycles P' U n := by
  rw [mem_cocycles] at hσ ⊢
  rw [← push_d, hσ, map_zero]

lemma push_mem_coboundaries (φ : P ⟶ P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ coboundaries P U n) : push U φ n σ ∈ coboundaries P' U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    rw [coboundaries_succ] at hσ ⊢
    obtain ⟨τ, rfl⟩ := hσ
    exact ⟨push U φ n τ, (push_d U φ n τ).symm⟩

def cocyclesMap (φ : P ⟶ P') (n : ℕ) : cocycles P U n →+ cocycles P' U n :=
  AddMonoidHom.codRestrict ((push U φ n).comp (cocycles P U n).subtype) (cocycles P' U n)
    fun σ => push_mem_cocycles U φ σ.2

def cechHMap (φ : P ⟶ P') (n : ℕ) : cechH P U n →+ cechH P' U n :=
  QuotientAddGroup.map _ _ (cocyclesMap U φ n) fun σ hσ => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact push_mem_coboundaries U φ (AddSubgroup.mem_addSubgroupOf.1 hσ)

lemma cls_congr {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {n : ℕ} {σ σ' : Cochain P U n} (h : σ = σ')
    (hσ : d P U n σ = 0) (hσ' : d P U n σ' = 0) : cls σ hσ = cls σ' hσ' := by
  subst h
  rfl

lemma cechHMap_cls (φ : P ⟶ P') {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) :
    cechHMap U φ n (cls σ hσ) = cls (push U φ n σ) (by rw [← push_d, hσ, map_zero]) := rfl

lemma cechHMap_id (n : ℕ) (x : cechH P U n) : cechHMap U (𝟙 P) n x = x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechHMap_cls]
  exact cls_congr U (push_id U n σ) _ _

lemma cechHMap_comp (φ : P ⟶ P') (ψ : P' ⟶ P'') (n : ℕ) (x : cechH P U n) :
    cechHMap U (φ ≫ ψ) n x = cechHMap U ψ n (cechHMap U φ n x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechHMap_cls, cechHMap_cls, cechHMap_cls]
  exact cls_congr U (push_comp U φ ψ n σ).symm _ _

lemma cechHMap_add (φ ψ : P ⟶ P') (n : ℕ) (x : cechH P U n) :
    cechHMap U (φ + ψ) n x = cechHMap U φ n x + cechHMap U ψ n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechHMap_cls, cechHMap_cls, cechHMap_cls]
  refine (cls_congr U (push_add U φ ψ n σ) _ ?_).trans (cls_add _ _ _ _ _)
  rw [map_add, ← push_d, ← push_d, hσ, map_zero, map_zero, add_zero]

lemma cechHMap_zero (n : ℕ) (x : cechH P U n) : cechHMap U (0 : P ⟶ P') n x = 0 := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechHMap_cls]
  exact (cls_congr U (push_zero' U n σ) _ (map_zero _)).trans cls_zero

variable (P) in

def cechH.endRingHom (n : ℕ) : End P →+* AddMonoid.End (cechH P U n) where
  toFun φ := cechHMap U φ n
  map_one' := by
    ext x
    exact cechHMap_id U n x
  map_mul' φ ψ := by
    ext x
    exact cechHMap_comp U ψ φ n x
  map_zero' := by
    ext x
    exact cechHMap_zero U n x
  map_add' φ ψ := by
    ext x
    exact cechHMap_add U φ ψ n x

end Map

section Delta

variable {F I Q F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {f : F ⟶ I} {g : I ⟶ Q}
  {f' : F' ⟶ I'} {g' : I' ⟶ Q'} {U}
  (hS : IsCechShortExact U f g) (hS' : IsCechShortExact U f' g')
  (α₁ : F ⟶ F') (α₂ : I ⟶ I') (α₃ : Q ⟶ Q') (h₁₂ : f ≫ α₂ = α₁ ≫ f') (h₂₃ : g ≫ α₃ = α₂ ≫ g')
include h₁₂ h₂₃

lemma IsCechShortExact.delta_naturality (n : ℕ) (σ : cocycles Q U n) :
    hS'.delta n (cocyclesMap U α₃ n σ) = cechHMap U α₁ (n + 1) (hS.delta n σ) := by
  obtain ⟨τ, ρ, hρ, hτ, hρτ, hc⟩ := hS.delta_spec n σ
  rw [hc, cechHMap_cls]
  refine hS'.deltaRel_unique (hS'.delta_spec n _) ⟨push U α₂ n τ, push U α₁ (n + 1) ρ, _, ?_, ?_, rfl⟩
  · change push U g' n (push U α₂ n τ) = push U α₃ n σ.1
    rw [push_comp, ← h₂₃, ← push_comp, hτ]
  · rw [push_comp, ← h₁₂, ← push_comp, hρτ, push_d]

lemma IsCechShortExact.deltaEquiv_naturality (hI : CechAcyclic I U) (hI' : CechAcyclic I' U)
    (m : ℕ) (x : cechH Q U (m + 1)) :
    hS'.deltaEquiv hI' m (cechHMap U α₃ (m + 1) x) =
      cechHMap U α₁ (m + 2) (hS.deltaEquiv hI m x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  exact hS.delta_naturality hS' α₁ α₂ α₃ h₁₂ h₂₃ (m + 1) ⟨σ, (mem_cocycles σ).2 hσ⟩

end Delta

section HDelta

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {S S' : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S')

lemma H.δ_naturality (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Sheaf.H.{w'} S.X₃ n₀) :
    H.δ hS' n₀ n₁ h (Sheaf.H.map α.τ₃ n₀ x) = Sheaf.H.map α.τ₁ n₁ (H.δ hS n₀ n₁ h x) := by
  rw [H.δ_apply, H.δ_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_naturality hS hS' α]

lemma hDeltaEquiv_naturality [Injective S.X₂] [Injective S'.X₂] (m : ℕ)
    (x : Sheaf.H.{w'} S.X₃ (m + 1)) :
    hDeltaEquiv hS' m (Sheaf.H.map α.τ₃ (m + 1) x) =
      Sheaf.H.map α.τ₁ (m + 2) (hDeltaEquiv hS m x) :=
  H.δ_naturality hS hS' α (m + 1) (m + 2) rfl x

end HDelta

section Zero

variable {P P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}

lemma globalCocycleEquiv_symm_naturality (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
    (hP' : Presheaf.IsSheaf (Opens.grothendieckTopology X) P') (hU : iSup U = ⊤) (φ : P ⟶ P')
    (σ : cocycles P U 0) :
    (globalCocycleEquiv P' U hP' hU).symm (cocyclesMap U φ 0 σ) =
      φ.app _ ((globalCocycleEquiv P U hP hU).symm σ) := by
  apply (globalCocycleEquiv P' U hP' hU).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  change push U φ 0 σ.1 = (globalCocycle P' U _).1
  rw [← push_globalCocycle]
  congr 2
  exact ((globalCocycleEquiv P U hP hU).apply_symm_apply σ).symm

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

lemma cechHZeroEquivH_naturality {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : G ⟶ G') (hU : iSup U = ⊤) (x : cechH G.obj U 0) :
    cechHZeroEquivH G' U hU (cechHMap U φ.hom 0 x) =
      Sheaf.H.map.{w'} φ 0 (cechHZeroEquivH G U hU x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  simp only [cechHZeroEquivH, cechHZeroEquiv, AddEquiv.trans_apply]
  rw [Sheaf.H.equiv₀_symm_naturality]
  congr 1
  exact globalCocycleEquiv_symm_naturality U G.property G'.property hU φ.hom _

end Zero

section Module

variable {X : Scheme.{u}} {ι : Type w} (U : ι → X.Opens) (A : Type*) [CommRing A]
  [Algebra A Γ(X, ⊤)]

def sheafEndRingHom (G : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) :
    End G →+* End G.obj where
  toFun φ := φ.hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def cechH.actRingHom (F : X.Modules) (n : ℕ) :
    A →+* AddMonoid.End (cechH (modulesAb F).obj U n) :=
  (((cechH.endRingHom U (modulesAb F).obj n).comp (sheafEndRingHom (modulesAb F))).comp
    (smulAbRingHom F)).comp (algebraMap A Γ(X, ⊤))

instance cechH.instModule (F : X.Modules) (n : ℕ) : Module A (cechH (modulesAb F).obj U n) :=
  Module.compHom _ (cechH.actRingHom U A F n)

lemma cechH.smul_def (F : X.Modules) (n : ℕ) (a : A) (x : cechH (modulesAb F).obj U n) :
    a • x = cechHMap U (smulAbRingHom F (algebraMap A Γ(X, ⊤) a)).hom n x := rfl

def cechH.linearMap {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    cechH (modulesAb F).obj U n →ₗ[A] cechH (modulesAb G).obj U n where
  toFun := cechHMap U (modulesAbMap φ).hom n
  map_add' := map_add _
  map_smul' a x := by
    simp only [cechH.smul_def, RingHom.id_apply]
    have h := congrArg (fun f => f.hom) (smulAbRingHom_comp φ (algebraMap A Γ(X, ⊤) a))
    rw [← cechHMap_comp, ← cechHMap_comp]
    exact congrArg (fun f => cechHMap U f n x) h

lemma cechH.linearMap_apply {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (x : cechH (modulesAb F).obj U n) :
    cechH.linearMap U A φ n x = cechHMap U (modulesAbMap φ).hom n x := rfl

end Module

end

end GroundTheory.Arith.SchemeCoh
