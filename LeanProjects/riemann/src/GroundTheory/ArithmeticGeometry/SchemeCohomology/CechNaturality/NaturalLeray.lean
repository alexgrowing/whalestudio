import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry

universe w w' u

variable {X : TopCat.{u}}

section One

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] {ι : Type w}
  (U : ι → Opens X) (hU : iSup U = ⊤)
  {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact U S.f.hom S.g.hom)
  (hI : CechAcyclic S.X₂.obj U)

def cechOneProj : S.X₃.obj.obj (op ⊤) →+ cechH S.X₁.obj U 1 :=
  (hC.delta 0).comp (globalCocycle S.X₃.obj U)

def hOneProj : S.X₃.obj.obj (op ⊤) →+ Sheaf.H.{w'} S.X₁ 1 :=
  (H.δ hS 0 1 rfl).comp (Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm.toAddMonoidHom

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] [Injective S.X₂] in
include hU hI in
lemma cechOneProj_surjective : Function.Surjective (cechOneProj U hC) :=
  (hC.delta_surjective hI 0).comp (globalCocycle_surjective _ U S.X₃.property hU)

lemma hOneProj_surjective : Function.Surjective (hOneProj hS) := by
  intro x
  obtain ⟨y, hy⟩ := H.exact₁ hS rfl x (H.eq_zero_of_injective S.X₂ _)
  exact ⟨Sheaf.H.equiv₀ S.X₃ isTerminalTop y, by simp [hOneProj, hy]⟩

omit [Injective S.X₂] in
include hU in
lemma ker_cechOneProj_eq : (cechOneProj U hC).ker = (hOneProj hS).ker := by
  ext s
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  have e1 : cechOneProj U hC s = 0 ↔ ∃ t, S.g.hom.app (op ⊤) t = s := by
    change hC.delta 0 (globalCocycle S.X₃.obj U s) = 0 ↔ _
    rw [hC.delta_eq_zero_iff]
    constructor
    · rintro ⟨κ, hκ, hgκ⟩
      obtain ⟨t, ht⟩ := globalCocycle_surjective _ U S.X₂.property hU
        ⟨κ, (mem_cocycles κ).2 hκ⟩
      refine ⟨t, globalCocycle_injective _ U S.X₃.property hU (Subtype.ext ?_)⟩
      rw [← push_globalCocycle, ht]
      exact hgκ
    · rintro ⟨t, rfl⟩
      exact ⟨(globalCocycle S.X₂.obj U t).1, (mem_cocycles _).1 (globalCocycle _ U t).2,
        push_globalCocycle U _ t⟩
  have e2 : hOneProj hS s = 0 ↔ ∃ t, S.g.hom.app (op ⊤) t = s := by
    change H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s) = 0 ↔ _
    constructor
    · intro h
      obtain ⟨x, hx⟩ := H.exact₃ hS rfl _ h
      refine ⟨Sheaf.H.equiv₀ S.X₂ isTerminalTop x, ?_⟩
      apply (Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm.injective
      rw [← Sheaf.H.equiv₀_symm_naturality, AddEquiv.symm_apply_apply, hx]
    · rintro ⟨t, rfl⟩
      rw [← Sheaf.H.equiv₀_symm_naturality]
      exact H.δ_map_g hS rfl _
  rw [e1, e2]

def cechHOneEquiv : cechH S.X₁.obj U 1 ≃+ Sheaf.H.{w'} S.X₁ 1 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (cechOneProj_surjective U hU hC hI)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_cechOneProj_eq U hU hS hC)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (hOneProj_surjective hS)))

lemma cechHOneEquiv_cechOneProj (s : S.X₃.obj.obj (op ⊤)) :
    cechHOneEquiv U hU hS hC hI (cechOneProj U hC s) = hOneProj hS s := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (cechOneProj_surjective U hU hC hI)).symm (cechOneProj U hC s) = QuotientAddGroup.mk s := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [cechHOneEquiv, AddEquiv.trans_apply, h]
  rfl

lemma cechHOneEquiv_naturality
    {S' : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom)
    (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S') (x : cechH S.X₁.obj U 1) :
    cechHOneEquiv U hU hS' hC' hI' (cechHMap U α.τ₁.hom 1 x) =
      Sheaf.H.map.{w'} α.τ₁ 1 (cechHOneEquiv U hU hS hC hI x) := by
  obtain ⟨s, rfl⟩ := cechOneProj_surjective U hU hC hI x
  have h₁₂ : S.f.hom ≫ α.τ₂.hom = α.τ₁.hom ≫ S'.f.hom :=
    (congrArg (fun f => f.hom) α.comm₁₂).symm
  have h₂₃ : S.g.hom ≫ α.τ₃.hom = α.τ₂.hom ≫ S'.g.hom :=
    (congrArg (fun f => f.hom) α.comm₂₃).symm
  have hmap : cechHMap U α.τ₁.hom 1 (cechOneProj U hC s) =
      cechOneProj U hC' (α.τ₃.hom.app (op ⊤) s) := by
    change cechHMap U α.τ₁.hom (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj U s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U (α.τ₃.hom.app (op ⊤) s))
    rw [← hC.delta_naturality hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0]
    congr 1
    exact Subtype.ext (push_globalCocycle U α.τ₃.hom s)
  rw [hmap, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm (α.τ₃.hom.app (op ⊤) s)) =
    Sheaf.H.map α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [← Sheaf.H.equiv₀_symm_naturality, H.δ_naturality hS hS' α]

end One

section InjectiveMap

variable {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

def injectiveExtend (φ : F ⟶ G) : Injective.under F ⟶ Injective.under G :=
  haveI : Mono (Injective.ι F) := Injective.ι_mono F
  Injective.factorThru (φ ≫ Injective.ι G) (Injective.ι F)

lemma ι_injectiveExtend (φ : F ⟶ G) :
    Injective.ι F ≫ injectiveExtend φ = φ ≫ Injective.ι G := by
  have : Mono (Injective.ι F) := Injective.ι_mono F
  exact Injective.comp_factorThru _ _

def injectiveSequenceMap (φ : F ⟶ G) : injectiveSequence F ⟶ injectiveSequence G where
  τ₁ := φ
  τ₂ := injectiveExtend φ
  τ₃ := cokernel.map (Injective.ι F) (Injective.ι G) φ (injectiveExtend φ) (ι_injectiveExtend φ)
  comm₁₂ := by
    change φ ≫ Injective.ι G = Injective.ι F ≫ injectiveExtend φ
    exact (ι_injectiveExtend φ).symm
  comm₂₃ := by
    change injectiveExtend φ ≫ cokernel.π (Injective.ι G) =
      cokernel.π (Injective.ι F) ≫ cokernel.map (Injective.ι F) (Injective.ι G) φ
        (injectiveExtend φ) (ι_injectiveExtend φ)
    exact (cokernel.π_desc _ _ _).symm

lemma injectiveSequenceMap_τ₁ (φ : F ⟶ G) : (injectiveSequenceMap φ).τ₁ = φ := rfl

end InjectiveMap

section Step

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] {ι : Type w}
  (U : ι → Opens X) {S S' : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

def cechHEquivStep (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact U S.f.hom S.g.hom)
    (hI : CechAcyclic S.X₂.obj U) (m : ℕ)
    (e : cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1)) :
    cechH S.X₁.obj U (m + 2) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) :=
  ((hC.deltaEquiv hI m).symm.trans e).trans (hDeltaEquiv hS m)

lemma cechHEquivStep_naturality (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact U S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj U)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom)
    (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S') (m : ℕ)
    (e : cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1))
    (e' : cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechHMap U α.τ₃.hom (m + 1) y) = Sheaf.H.map.{w'} α.τ₃ (m + 1) (e y))
    (x : cechH S.X₁.obj U (m + 2)) :
    cechHEquivStep U hS' hC' hI' m e' (cechHMap U α.τ₁.hom (m + 2) x) =
      Sheaf.H.map.{w'} α.τ₁ (m + 2) (cechHEquivStep U hS hC hI m e x) := by
  have h₁₂ : S.f.hom ≫ α.τ₂.hom = α.τ₁.hom ≫ S'.f.hom :=
    (congrArg (fun f => f.hom) α.comm₁₂).symm
  have h₂₃ : S.g.hom ≫ α.τ₃.hom = α.τ₂.hom ≫ S'.g.hom :=
    (congrArg (fun f => f.hom) α.comm₂₃).symm
  obtain ⟨y, rfl⟩ := (hC.deltaEquiv hI m).surjective x
  have hδ : (hC'.deltaEquiv hI' m).symm (cechHMap U α.τ₁.hom (m + 2) (hC.deltaEquiv hI m y)) =
      cechHMap U α.τ₃.hom (m + 1) y := by
    rw [AddEquiv.symm_apply_eq, hC.deltaEquiv_naturality hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃]
  simp only [cechHEquivStep, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, hδ, he]
  exact hDeltaEquiv_naturality hS hS' α m (e y)

end Step

section Leray

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] {ι : Type w}
  {B : Opens X → Prop} {Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop}
  (hC : IsCoverSystem B Good) (U : ι → Opens X) (hU : iSup U = ⊤)
  (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), B (inter U i))

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
lemma injectiveSequence_cechAcyclic (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {κ : Type w} (V : κ → Opens X) : CechAcyclic (injectiveSequence G).X₂.obj V :=
  @cechAcyclic_of_injective X (injectiveSequence G).X₂
    (inferInstanceAs (Injective (Injective.under G))) κ V

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
include hC hUB in
lemma injectiveSequence_isCechShortExact
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : GoodAcyclic B Good G) :
    IsCechShortExact U (injectiveSequence G).f.hom (injectiveSequence G).g.hom :=
  isCechShortExact_of_surjective (injectiveSequence_shortExact G) U
    fun i => surjective_of_goodAcyclic hC (injectiveSequence_shortExact G) hG _ (hUB i)

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
include hC in
lemma injectiveSequence_goodAcyclic (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hG : GoodAcyclic B Good G) : GoodAcyclic B Good (injectiveSequence G).X₃ :=
  goodAcyclic_of_shortExact hC (injectiveSequence_shortExact G) hG
    fun _ V => injectiveSequence_cechAcyclic G V

def cechHEquiv : ∀ (n : ℕ) (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
    GoodAcyclic B Good G → (cechH G.obj U n ≃+ Sheaf.H.{w'} G n)
  | 0, G, _ => cechHZeroEquivH G U hU
  | 1, G, hG => cechHOneEquiv (S := injectiveSequence G) U hU (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hC U hUB G hG) (injectiveSequence_cechAcyclic G U)
  | m + 2, G, hG => cechHEquivStep (S := injectiveSequence G) U (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hC U hUB G hG) (injectiveSequence_cechAcyclic G U) m
      (cechHEquiv (m + 1) _ (injectiveSequence_goodAcyclic hC G hG))

theorem cechHEquiv_naturality : ∀ (n : ℕ) {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hG : GoodAcyclic B Good G) (hG' : GoodAcyclic B Good G') (φ : G ⟶ G') (x : cechH G.obj U n),
    cechHEquiv hC U hU hUB n G' hG' (cechHMap U φ.hom n x) =
      Sheaf.H.map.{w'} φ n (cechHEquiv hC U hU hUB n G hG x)
  | 0, _, _, _, _, φ, x => cechHZeroEquivH_naturality U φ hU x
  | 1, G, G', hG, hG', φ, x =>
      cechHOneEquiv_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U hU
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hC U hUB G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hC U hUB G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) x
  | m + 2, G, G', hG, hG', φ, x =>
      cechHEquivStep_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hC U hUB G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hC U hUB G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) m _ _
        (fun y => cechHEquiv_naturality (m + 1) _ _ (injectiveSequenceMap φ).τ₃ y) x

end Leray

section Scheme

variable {X : Scheme.{u}}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] {ι : Type w}
  (U : ι → X.Opens) (hU : iSup U = ⊤)
  (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))

def cechHAddEquivH (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    cechH (modulesAb F).obj U n ≃+ Sheaf.H.{w'} (modulesAb F) n :=
  cechHEquiv isCoverSystem_isBasicCover U hU
    (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) n (modulesAb F) (goodAcyclic_modulesAb F)

theorem cechHAddEquivH_naturality {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (n : ℕ) (x : cechH (modulesAb F).obj U n) :
    cechHAddEquivH U hU hUaff G n (cechHMap U (modulesAbMap φ).hom n x) =
      Sheaf.H.map.{w'} (modulesAbMap φ) n (cechHAddEquivH U hU hUaff F n x) :=
  cechHEquiv_naturality (X := X.toTopCat) isCoverSystem_isBasicCover U hU
    (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) n (goodAcyclic_modulesAb F) (goodAcyclic_modulesAb G) (modulesAbMap φ) x

variable (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def cechHLinearEquivH (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    cechH (modulesAb F).obj U n ≃ₗ[A] Sheaf.H.{w'} (modulesAb F) n :=
  (cechHAddEquivH U hU hUaff F n).toLinearEquiv fun a x =>
    cechHAddEquivH_naturality U hU hUaff (smulHom F (algebraMap A Γ(X, ⊤) a)) n x

lemma cechHLinearEquivH_apply (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (x : cechH (modulesAb F).obj U n) :
    cechHLinearEquivH U hU hUaff A F n x = cechHAddEquivH U hU hUaff F n x := rfl

theorem cechHLinearEquivH_naturality {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (n : ℕ) (x : cechH (modulesAb F).obj U n) :
    cechHLinearEquivH U hU hUaff A G n (cechH.linearMap U A φ n x) =
      H.linearMap A φ n (cechHLinearEquivH U hU hUaff A F n x) :=
  cechHAddEquivH_naturality U hU hUaff φ n x

end Scheme

section NatIso

variable {X : Scheme.{u}} {ι : Type w}
  [HasExt.{max w u} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (U : ι → X.Opens) (hU : iSup U = ⊤)
  (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def cechModuleFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{max w u} A where
  obj F := ModuleCat.of A (cechH (modulesAb F).obj U n)
  map φ := ModuleCat.ofHom (cechH.linearMap U A φ n)
  map_id F := by
    ext x
    change cechHMap U (modulesAbMap (𝟙 F)).hom n x = x
    rw [modulesAbMap_id]
    exact cechHMap_id U n x
  map_comp φ ψ := by
    ext x
    change cechHMap U (modulesAbMap (φ ≫ ψ)).hom n x = _
    rw [modulesAbMap_comp]
    exact cechHMap_comp U _ _ n x

def isQuasicoherent : ObjectProperty X.Modules := fun F => F.IsQuasicoherent

def cechHNatIso (n : ℕ) :
    isQuasicoherent.ι ⋙ cechModuleFunctor U A n ≅ isQuasicoherent.ι ⋙ H.moduleFunctor A n :=
  NatIso.ofComponents
    (fun F => haveI : F.obj.IsQuasicoherent := F.property
      (cechHLinearEquivH U hU hUaff A F.obj n).toModuleIso)
    (fun {F G} φ => by
      have : F.obj.IsQuasicoherent := F.property
      have : G.obj.IsQuasicoherent := G.property
      ext x
      exact cechHLinearEquivH_naturality U hU hUaff A φ.hom n x)

end NatIso

end

end GroundTheory.Arith.SchemeCoh
