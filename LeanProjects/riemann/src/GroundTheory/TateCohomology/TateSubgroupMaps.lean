import Mathlib
import GroundTheory.TateCohomology.TateUnique
import GroundTheory.TateCohomology.TateTransport
import GroundTheory.TateCohomology.ResCoresZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Delta

lemma tate_whiskerRight_δ {H : Type u} [Group H] [Fintype H] {F F' : Rep.{u} k G ⥤ Rep.{u} k H}
    [F.PreservesZeroMorphisms] [F'.PreservesZeroMorphisms] (σ : F ⟶ F')
    {X : ShortComplex (Rep.{u} k G)} (hX : (X.map F).ShortExact) (hX' : (X.map F').ShortExact)
    (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateCohomologyFunctor (n + 1)).map (σ.app X.X₁) =
      (tateCohomologyFunctor n).map (σ.app X.X₃) ≫ TateCohomology.δ hX' n :=
  TateCohomology.δ_naturality hX hX' (X.mapNatTrans σ) n

lemma sq_comp {C : Type*} [Category C] {a₁ a₂ a₃ b₁ b₂ b₃ : C} {δ₁ : a₁ ⟶ b₁} {δ₂ : a₂ ⟶ b₂}
    {δ₃ : a₃ ⟶ b₃} {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} {g : b₂ ⟶ b₃} {g' : a₂ ⟶ a₃}
    (h₁ : δ₁ ≫ f = f' ≫ δ₂) (h₂ : δ₂ ≫ g = g' ≫ δ₃) : δ₁ ≫ (f ≫ g) = (f' ≫ g') ≫ δ₃ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

lemma sq_sum {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} {ι : Type*} (s : Finset ι) {f : ι → (b₁ ⟶ b₂)} {f' : ι → (a₁ ⟶ a₂)}
    (h : ∀ i ∈ s, δ₁ ≫ f i = f' i ≫ δ₂) : δ₁ ≫ ∑ i ∈ s, f i = (∑ i ∈ s, f' i) ≫ δ₂ := by
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl h

lemma sq_nsmul {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} (m : ℕ) {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} (h : δ₁ ≫ f = f' ≫ δ₂) :
    δ₁ ≫ (m • f) = (m • f') ≫ δ₂ := by
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, h]

variable [Fintype G]

def IsTateDelta {U V : Subgroup G} [Fintype U] [Fintype V]
    (α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n) : Prop :=
  ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
    TateCohomology.δ (shortExact_map_resFunctor U hX) n ≫ (α (n + 1)).app X.X₁ =
      (α n).app X.X₃ ≫ TateCohomology.δ (shortExact_map_resFunctor V hX) n

namespace IsTateDelta

variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]

theorem ext {α β : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) (h0 : α 0 = β 0) : α = β :=
  funext (tate_natTrans_eq_of_eq_zero (resFunctor U.subtype) (resFunctor V.subtype)
    (shortExact_map_resFunctor U) (shortExact_map_resFunctor V)
    (tateAcyclic_res_coindSES_X₂ U) (tateAcyclic_res_indSES_X₂ V) α β hα hβ h0)

omit [Fintype G] in

theorem id : IsTateDelta (fun n => 𝟙 (resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n)) :=
  fun _ _ => (Category.comp_id _).trans (Category.id_comp _).symm

omit [Fintype G] in

theorem comp {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    {β : ∀ n : ℤ, resFunctor V.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) : IsTateDelta (fun n => α n ≫ β n) := by
  intro X hX n
  exact sq_comp (hα hX n) (hβ hX n)

omit [Fintype G] in

theorem sum {ι : Type*} (s : Finset ι)
    {α : ι → ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : ∀ i ∈ s, IsTateDelta (α i)) : IsTateDelta (fun n => ∑ i ∈ s, α i n) := by
  intro X hX n
  rw [NatTrans.app_sum, NatTrans.app_sum]
  exact sq_sum s fun i hi => hα i hi hX n

omit [Fintype G] in

theorem nsmul (m : ℕ)
    {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) : IsTateDelta (fun n => m • α n) := by
  intro X hX n
  rw [NatTrans.app_nsmul, NatTrans.app_nsmul]
  exact sq_nsmul m (hα hX n)

theorem cores_res : IsTateDelta (fun n => tateCores (k := k) U n ≫ tateRes V n) := by
  intro X hX n
  exact sq_comp (tateCores_δ U hX n) (tateRes_δ V hX n)

end IsTateDelta

end Delta

section LE

variable {U W : Subgroup G} (h : W ≤ U)

@[simps]
def resLENatTrans :
    resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype ⋙
        resFunctor ((Subgroup.subgroupOfEquivOfLe h).symm : W →* W.subgroupOf U) ⟶
      resFunctor (k := k) W.subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl

@[simps]
def coresLENatTrans :
    resFunctor W.subtype ⋙ resFunctor (Subgroup.subgroupOfEquivOfLe h : W.subgroupOf U →* W) ⟶
      resFunctor (k := k) U.subtype ⋙ resFunctor (W.subgroupOf U).subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl

variable [Fintype U] [Fintype W]

@[instance_reducible]
noncomputable def fintypeSubgroupOf : Fintype (W.subgroupOf U) :=
  Fintype.ofEquiv W (Subgroup.subgroupOfEquivOfLe h).symm.toEquiv

noncomputable def tateResLE (n : ℤ) :
    resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n :=
  letI := fintypeSubgroupOf h
  Functor.whiskerLeft (resFunctor U.subtype) (tateRes (W.subgroupOf U) n) ≫
    Functor.whiskerLeft (resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype)
      (tateTransport (Subgroup.subgroupOfEquivOfLe h).symm n) ≫
    Functor.whiskerRight (resLENatTrans h) (tateCohomologyFunctor n)

noncomputable def tateCoresLE (n : ℤ) :
    resFunctor W.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor U.subtype ⋙ tateCohomologyFunctor n :=
  letI := fintypeSubgroupOf h
  Functor.whiskerLeft (resFunctor W.subtype) (tateTransport (Subgroup.subgroupOfEquivOfLe h) n) ≫
    Functor.whiskerRight (coresLENatTrans h) (tateCohomologyFunctor n) ≫
    Functor.whiskerLeft (resFunctor U.subtype) (tateCores (W.subgroupOf U) n)

theorem isTateDelta_tateResLE : IsTateDelta (tateResLE (k := k) h) := by
  let _ := fintypeSubgroupOf h
  intro X hX n
  have hU := shortExact_map_resFunctor U hX
  have h1 := tateRes_δ (W.subgroupOf U) hU n
  have h2 := tateTransport_δ (Subgroup.subgroupOfEquivOfLe h).symm
    (shortExact_map_resFunctor (W.subgroupOf U) hU) n
  have h3 := tate_whiskerRight_δ (resLENatTrans (k := k) h)
    (shortExact_map_resFunctor_equiv (Subgroup.subgroupOfEquivOfLe h).symm
      (shortExact_map_resFunctor (W.subgroupOf U) hU))
    (shortExact_map_resFunctor W hX) n
  exact sq_comp h1 (sq_comp h2 h3)

theorem isTateDelta_tateCoresLE : IsTateDelta (tateCoresLE (k := k) h) := by
  let _ := fintypeSubgroupOf h
  intro X hX n
  have hW := shortExact_map_resFunctor W hX
  have hU := shortExact_map_resFunctor U hX
  have h1 := tateTransport_δ (Subgroup.subgroupOfEquivOfLe h) hW n
  have h2 := tate_whiskerRight_δ (coresLENatTrans (k := k) h)
    (shortExact_map_resFunctor_equiv (Subgroup.subgroupOfEquivOfLe h) hW)
    (shortExact_map_resFunctor (W.subgroupOf U) hU) n
  have h3 := tateCores_δ (W.subgroupOf U) hU n
  exact sq_comp h1 (sq_comp h2 h3)

omit [Fintype U] [Fintype W] in

def invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (res W.subtype A).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨w, h w.2⟩⟩

omit [Fintype U] [Fintype W] in
@[simp]
lemma coe_invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (invariantsLE h y : A) = y := rfl

theorem tateResLE_tateZeroClass (A : Rep.{u} k G) (y : (res U.subtype A).ρ.invariants) :
    ((tateResLE h 0).app A).hom (tateZeroClass (res U.subtype A) y) =
      tateZeroClass (res W.subtype A) (invariantsLE h y) := by
  let _ := fintypeSubgroupOf h
  have e1 := tateRes_tateZeroClass (W.subgroupOf U) (res U.subtype A) y
  have e2 := tateTransport_tateZeroClass (Subgroup.subgroupOfEquivOfLe h).symm
    (res (W.subgroupOf U).subtype (res U.subtype A)) (invariantsRes (W.subgroupOf U).subtype y)
  have e3 := tateCohomologyFunctor_map_tateZeroClass ((resLENatTrans (k := k) h).app A)
    (invariantsTransport (Subgroup.subgroupOfEquivOfLe h).symm
      (invariantsRes (W.subgroupOf U).subtype y))
  refine (congrArg (fun z => ((tateCohomologyFunctor 0).map ((resLENatTrans (k := k) h).app A)).hom
    (((tateTransport (Subgroup.subgroupOfEquivOfLe h).symm 0).app
      (res (W.subgroupOf U).subtype (res U.subtype A))).hom z)) e1).trans ?_
  refine (congrArg (fun z => ((tateCohomologyFunctor 0).map ((resLENatTrans (k := k) h).app A)).hom z)
    e2).trans ?_
  exact e3

omit [Fintype U] [Fintype W] in
variable (U) in

def invariantsSubgroupOf {A : Rep.{u} k G} (y : (res W.subtype A).ρ.invariants) :
    (res (W.subgroupOf U).subtype (res U.subtype A)).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨(w : U), w.2⟩⟩

theorem tateCoresLE_tateZeroClass (A : Rep.{u} k G) (y : (res W.subtype A).ρ.invariants) :
    ((tateCoresLE h 0).app A).hom (tateZeroClass (res W.subtype A) y) =
      tateZeroClass (res U.subtype A) (transferInv (W.subgroupOf U) (invariantsSubgroupOf U y)) := by
  let _ := fintypeSubgroupOf h
  have e1 := tateTransport_tateZeroClass (Subgroup.subgroupOfEquivOfLe h) (res W.subtype A) y
  have e2 := tateCohomologyFunctor_map_tateZeroClass ((coresLENatTrans (k := k) h).app A)
    (invariantsTransport (Subgroup.subgroupOfEquivOfLe h) y)
  have e3 := tateCores_tateZeroClass (W.subgroupOf U) (res U.subtype A) (invariantsSubgroupOf U y)
  refine (congrArg (fun z => ((tateCores (W.subgroupOf U) 0).app (res U.subtype A)).hom
    (((tateCohomologyFunctor 0).map ((coresLENatTrans (k := k) h).app A)).hom z)) e1).trans ?_
  refine (congrArg (fun z => ((tateCores (W.subgroupOf U) 0).app (res U.subtype A)).hom z)
    e2).trans ?_
  exact e3

end LE

end GroundTheory.GroupCoh
