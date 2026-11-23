import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Cartan
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechToDerived
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian

universe w w' u

variable {X : TopCat.{u}}

section Groups

variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

def cocycles (n : ℕ) : AddSubgroup (Cochain P U n) := (d P U n).ker

def coboundaries : (n : ℕ) → AddSubgroup (Cochain P U n)
  | 0 => ⊥
  | n + 1 => (d P U n).range

lemma coboundaries_zero : coboundaries P U 0 = ⊥ := rfl

lemma coboundaries_succ (n : ℕ) : coboundaries P U (n + 1) = (d P U n).range := rfl

abbrev cechH (n : ℕ) : Type (max w u) :=
  cocycles P U n ⧸ (coboundaries P U n).addSubgroupOf (cocycles P U n)

variable {P U}

lemma mem_cocycles {n : ℕ} (σ : Cochain P U n) : σ ∈ cocycles P U n ↔ d P U n σ = 0 :=
  AddMonoidHom.mem_ker

def cls {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) : cechH P U n :=
  QuotientAddGroup.mk (⟨σ, (mem_cocycles σ).2 hσ⟩ : cocycles P U n)

lemma cls_eq_zero_iff {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) :
    cls σ hσ = 0 ↔ σ ∈ coboundaries P U n := by
  rw [cls, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

lemma cls_zero {n : ℕ} : cls (0 : Cochain P U n) (map_zero _) = 0 :=
  QuotientAddGroup.mk_zero _

lemma cls_add {n : ℕ} (σ σ' : Cochain P U n) (hσ : d P U n σ = 0) (hσ' : d P U n σ' = 0)
    (h : d P U n (σ + σ') = 0) : cls (σ + σ') h = cls σ hσ + cls σ' hσ' :=
  rfl

lemma cls_eq_cls_iff {n : ℕ} (σ σ' : Cochain P U n) (hσ : d P U n σ = 0)
    (hσ' : d P U n σ' = 0) : cls σ hσ = cls σ' hσ' ↔ σ' - σ ∈ coboundaries P U n := by
  rw [cls, cls, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
  rfl

lemma exists_cls {n : ℕ} (c : cechH P U n) :
    ∃ σ hσ, cls (P := P) (U := U) (n := n) σ hσ = c := by
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact ⟨σ, (mem_cocycles σ).1 hσ, rfl⟩

end Groups

section Connecting

variable {ι : Type w} (U : ι → Opens X) {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}

structure IsCechShortExact (f : F ⟶ I) (g : I ⟶ Q) : Prop where
  zero : f ≫ g = 0
  injective : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i)))
  exact : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
    g.app _ y = 0 → ∃ x, f.app _ x = y
  surjective : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i)))

def DeltaRel (f : F ⟶ I) (g : I ⟶ Q) (n : ℕ) (σ : Cochain Q U n) (c : cechH F U (n + 1)) :
    Prop :=
  ∃ (τ : Cochain I U n) (ρ : Cochain F U (n + 1)) (hρ : d F U (n + 1) ρ = 0),
    push U g n τ = σ ∧ push U f (n + 1) ρ = d I U n τ ∧ c = cls ρ hρ

variable {U} {f : F ⟶ I} {g : I ⟶ Q}

lemma DeltaRel.add {n : ℕ} {σ σ' : Cochain Q U n} {c c' : cechH F U (n + 1)}
    (h : DeltaRel U f g n σ c) (h' : DeltaRel U f g n σ' c') :
    DeltaRel U f g n (σ + σ') (c + c') := by
  obtain ⟨τ, ρ, hρ, hτ, hρτ, rfl⟩ := h
  obtain ⟨τ', ρ', hρ', hτ', hρτ', rfl⟩ := h'
  exact ⟨τ + τ', ρ + ρ', by rw [map_add, hρ, hρ', add_zero], by rw [map_add, hτ, hτ'],
    by rw [map_add, map_add, hρτ, hρτ'], (cls_add _ _ hρ hρ' _).symm⟩

namespace IsCechShortExact

variable (hS : IsCechShortExact U f g)
include hS

lemma push_injective' (n : ℕ) : Function.Injective (push U f n) :=
  push_injective U f n fun i => hS.injective i

lemma push_surjective (n : ℕ) (σ : Cochain Q U n) : ∃ τ, push U g n τ = σ := by
  choose τ hτ using fun i => hS.surjective i (σ i)
  exact ⟨τ, funext hτ⟩

lemma push_exact (n : ℕ) (τ : Cochain I U n) (hτ : push U g n τ = 0) :
    ∃ α, push U f n α = τ := by
  choose α hα using fun i => hS.exact i (τ i) (congrFun hτ i)
  exact ⟨α, funext hα⟩

lemma push_push (n : ℕ) (α : Cochain F U n) : push U g n (push U f n α) = 0 := by
  rw [push_comp, hS.zero, push_zero']

lemma exists_deltaRel {n : ℕ} (σ : Cochain Q U n) (hσ : d Q U n σ = 0) :
    ∃ c, DeltaRel U f g n σ c := by
  obtain ⟨τ, hτ⟩ := hS.push_surjective n σ
  have h0 : push U g (n + 1) (d I U n τ) = 0 := by rw [push_d, hτ, hσ]
  obtain ⟨ρ, hρ⟩ := hS.push_exact (n + 1) _ h0
  have hρc : d F U (n + 1) ρ = 0 := by
    apply hS.push_injective' (n + 2)
    rw [map_zero, push_d, hρ, d_d]
  exact ⟨cls ρ hρc, τ, ρ, hρc, hτ, hρ, rfl⟩

lemma deltaRel_unique {n : ℕ} {σ : Cochain Q U n} {c c' : cechH F U (n + 1)}
    (h : DeltaRel U f g n σ c) (h' : DeltaRel U f g n σ c') : c = c' := by
  obtain ⟨τ, ρ, hρ, hτ, hρτ, rfl⟩ := h
  obtain ⟨τ', ρ', hρ', hτ', hρτ', rfl⟩ := h'
  rw [cls_eq_cls_iff, coboundaries_succ]
  obtain ⟨α, hα⟩ := hS.push_exact n (τ' - τ) (by rw [map_sub, hτ, hτ', sub_self])
  refine AddMonoidHom.mem_range.2 ⟨α, ?_⟩
  apply hS.push_injective' (n + 1)
  rw [push_d, hα, map_sub, map_sub, hρτ, hρτ']

def deltaFun (n : ℕ) (σ : cocycles Q U n) : cechH F U (n + 1) :=
  Classical.choose (hS.exists_deltaRel σ.1 ((mem_cocycles _).1 σ.2))

lemma deltaFun_spec (n : ℕ) (σ : cocycles Q U n) : DeltaRel U f g n σ.1 (hS.deltaFun n σ) :=
  Classical.choose_spec (hS.exists_deltaRel σ.1 ((mem_cocycles _).1 σ.2))

def delta (n : ℕ) : cocycles Q U n →+ cechH F U (n + 1) where
  toFun := hS.deltaFun n
  map_zero' := hS.deltaRel_unique (hS.deltaFun_spec n 0)
    ⟨0, 0, map_zero _, map_zero _, by rw [map_zero, map_zero], cls_zero.symm⟩
  map_add' σ σ' := hS.deltaRel_unique (hS.deltaFun_spec n (σ + σ'))
    ((hS.deltaFun_spec n σ).add (hS.deltaFun_spec n σ'))

lemma delta_spec (n : ℕ) (σ : cocycles Q U n) : DeltaRel U f g n σ.1 (hS.delta n σ) :=
  hS.deltaFun_spec n σ

lemma delta_surjective (hI : CechAcyclic I U) (n : ℕ) : Function.Surjective (hS.delta n) := by
  intro c
  obtain ⟨ρ, hρ, rfl⟩ := exists_cls c
  obtain ⟨τ, hτ⟩ := hI n (push U f (n + 1) ρ) (by rw [← push_d, hρ, map_zero])
  have hσ : d Q U n (push U g n τ) = 0 := by rw [← push_d, hτ, hS.push_push]
  exact ⟨⟨push U g n τ, (mem_cocycles _).2 hσ⟩,
    hS.deltaRel_unique (hS.delta_spec n _) ⟨τ, ρ, hρ, rfl, hτ.symm, rfl⟩⟩

lemma delta_eq_zero_iff (n : ℕ) (σ : cocycles Q U n) :
    hS.delta n σ = 0 ↔ ∃ κ : Cochain I U n, d I U n κ = 0 ∧ push U g n κ = σ := by
  constructor
  · intro h0
    obtain ⟨τ, ρ, hρ, hτ, hρτ, hc⟩ := hS.delta_spec n σ
    rw [h0, eq_comm, cls_eq_zero_iff, coboundaries_succ] at hc
    obtain ⟨β, hβ⟩ := AddMonoidHom.mem_range.1 hc
    refine ⟨τ - push U f n β, ?_, ?_⟩
    · rw [map_sub, ← hρτ, ← hβ, push_d, sub_self]
    · rw [map_sub, hS.push_push, sub_zero, hτ]
  · rintro ⟨κ, hκ, hgκ⟩
    exact hS.deltaRel_unique (hS.delta_spec n σ)
      ⟨κ, 0, map_zero _, hgκ, by rw [map_zero, hκ], cls_zero.symm⟩

lemma ker_delta_succ (hI : CechAcyclic I U) (m : ℕ) :
    (hS.delta (m + 1)).ker =
      (coboundaries Q U (m + 1)).addSubgroupOf (cocycles Q U (m + 1)) := by
  ext σ
  rw [AddMonoidHom.mem_ker, hS.delta_eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    coboundaries_succ]
  constructor
  · rintro ⟨κ, hκ, hgκ⟩
    obtain ⟨θ, hθ⟩ := hI m κ hκ
    exact AddMonoidHom.mem_range.2 ⟨push U g m θ, by rw [← push_d, hθ, hgκ]⟩
  · intro hσ
    obtain ⟨θ, hθ⟩ := AddMonoidHom.mem_range.1 hσ
    obtain ⟨θ', hθ'⟩ := hS.push_surjective m θ
    exact ⟨d I U m θ', d_d I U m θ', by rw [push_d, hθ', hθ]⟩

def deltaEquiv (hI : CechAcyclic I U) (m : ℕ) :
    cechH Q U (m + 1) ≃+ cechH F U (m + 2) :=
  (QuotientAddGroup.quotientAddEquivOfEq (hS.ker_delta_succ hI m).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (hS.delta_surjective hI (m + 1)))

end IsCechShortExact

end Connecting

section Sections

variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

def globalCocycle : P.obj (op ⊤) →+ cocycles P U 0 where
  toFun s := ⟨constCochain P U (fun _ => le_top) s,
    (mem_cocycles _).2 (d_constCochain P U (fun _ => le_top) s)⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

variable {P} in
lemma push_globalCocycle {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P')
    (s : P.obj (op ⊤)) :
    push U φ 0 (globalCocycle P U s).1 = (globalCocycle P' U (φ.app _ s)).1 :=
  funext fun _ => app_res φ _ s

variable (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤)
include hP hU

lemma globalCocycle_surjective : Function.Surjective (globalCocycle P U) := by
  rintro ⟨κ, hκ⟩
  obtain ⟨t, ht⟩ := exists_glue P hP U ⊤ (fun _ => le_top) hU.ge κ ((mem_cocycles κ).1 hκ)
  exact ⟨t, Subtype.ext (funext ht)⟩

lemma globalCocycle_injective : Function.Injective (globalCocycle P U) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) U ⊤
    (fun _ => homOfLE le_top) hU.ge
  intro a
  have h1 := congrFun (congrArg Subtype.val hs) (fun _ : Fin 1 => a)
  have h2 := congrArg (res P (le_inter_const U a)) h1
  change res P (le_inter_const U a) (res P _ s) = res P (le_inter_const U a) 0 at h2
  rw [res_res, map_zero] at h2
  change res P le_top s = res P le_top 0
  rw [map_zero]
  exact h2

def globalCocycleEquiv : P.obj (op ⊤) ≃+ cocycles P U 0 :=
  AddEquiv.ofBijective (globalCocycle P U)
    ⟨globalCocycle_injective P U hP hU, globalCocycle_surjective P U hP hU⟩

def cechHZeroEquiv : cechH P U 0 ≃+ P.obj (op ⊤) :=
  ((QuotientAddGroup.quotientAddEquivOfEq
    (by rw [coboundaries_zero, AddSubgroup.bot_addSubgroupOf])).trans
      QuotientAddGroup.quotientBot).trans (globalCocycleEquiv P U hP hU).symm

end Sections

section Cartan

structure IsCoverSystem (B : Opens X → Prop)
    (Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop) : Prop where
  iSup_eq : ∀ (V : Opens X) {κ : Type u} (U : κ → Opens X), Good V U → iSup U = V
  inter_mem : ∀ (V : Opens X) {κ : Type u} (U : κ → Opens X), Good V U →
    ∀ {n : ℕ} (i : Fin (n + 1) → κ), B (inter U i)
  exists_refinement : ∀ V, B V → ∀ O : V → Opens X, (∀ x, x.1 ∈ O x) →
    ∃ (κ : Type u) (_ : Finite κ) (U : κ → Opens X), Good V U ∧ ∀ a, ∃ x, U a ≤ O x

variable (B : Opens X → Prop) (Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop)

def GoodAcyclic (G : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (κ : Type u) [Finite κ] (U : κ → Opens X), Good V U → CechAcyclic G.obj U

variable {B Good} (hC : IsCoverSystem B Good)
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
include hC hS

theorem surjective_of_goodAcyclic (hF : GoodAcyclic B Good S.X₁) (V : Opens X) (hV : B V) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  have hls := (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hls
  choose O hOV ht hxO using fun x : V => hloc V s x.1 x.2
  choose t ht using ht
  obtain ⟨κ, _, U, hgood, hUO⟩ := hC.exists_refinement V hV O hxO
  choose x hx using hUO
  have hUV : ∀ a, U a ≤ V := fun a => (hx a).trans (hOV (x a))
  have hsup : iSup U = V := hC.iSup_eq V U hgood
  let τ0 : Cochain S.X₂.obj U 0 := fun i =>
    res S.X₂.obj ((inter_le U i 0).trans (hx (i 0))) (t (x (i 0)))
  have hτ0 : push U S.g.hom 0 τ0 = constCochain S.X₃.obj U hUV s := by
    funext i
    simp only [push, τ0, constCochain, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [app_res, ht]
    exact res_res _ _ _ s
  have hdτ0 : push U S.g.hom 1 (d _ U 0 τ0) = 0 := by
    rw [push_d, hτ0, d_constCochain]
  choose ρ hρ using fun j => app_exact_of_shortExact hS _ _ (congrFun hdτ0 j)
  have hρ' : push U S.f.hom 1 ρ = d _ U 0 τ0 := funext hρ
  have hρc : d S.X₁.obj U 1 ρ = 0 := by
    apply push_injective U S.f.hom 2 (fun j => app_injective_of_shortExact hS _)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨β, hβ⟩ := hF V hV κ U hgood 0 ρ hρc
  have hc : d S.X₂.obj U 0 (τ0 - push U S.f.hom 0 β) = 0 := by
    rw [map_sub, ← push_d, hβ, hρ', sub_self]
  obtain ⟨t', ht'⟩ := exists_glue S.X₂.obj S.X₂.property U V hUV hsup.ge _ hc
  refine ⟨t', ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ U V (fun a => homOfLE (hUV a)) hsup.ge
  intro a
  have key : res S.X₃.obj ((inter_le U (fun _ : Fin 1 => a) 0).trans (hUV a))
      (S.g.hom.app _ t') =
      res S.X₃.obj ((inter_le U (fun _ : Fin 1 => a) 0).trans (hUV a)) s := by
    rw [← app_res, ht' (fun _ => a), Pi.sub_apply, map_sub]
    have h1 : S.g.hom.app _ ((push U S.f.hom 0 β) (fun _ => a)) = 0 :=
      app_comp_apply_eq_zero _ _
    rw [h1, sub_zero]
    exact congrFun hτ0 (fun _ => a)
  have := congrArg (res S.X₃.obj (le_inter_const U a)) key
  rw [res_res, res_res] at this
  exact this

theorem goodAcyclic_of_shortExact (hF : GoodAcyclic B Good S.X₁)
    (hI : ∀ (κ : Type u) (U : κ → Opens X), CechAcyclic S.X₂.obj U) :
    GoodAcyclic B Good S.X₃ := by
  intro V hV κ _ U hU
  exact CechAcyclic.of_shortExact' U S.f.hom S.g.hom comp_hom_eq_zero
    (fun i => app_injective_of_shortExact hS _)
    (fun i y hy => app_exact_of_shortExact hS _ y hy)
    (fun i => surjective_of_goodAcyclic hC hS hF _ (hC.inter_mem V U hU i))
    (hF V hV κ U hU) (hI κ U)

end Cartan

section Leray

variable {ι : Type w}

lemma isCechShortExact_of_surjective {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : ι → Opens X)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (S.g.hom.app (op (inter U i)))) :
    IsCechShortExact U S.f.hom S.g.hom :=
  ⟨comp_hom_eq_zero, fun _ => app_injective_of_shortExact hS _,
    fun _ y hy => app_exact_of_shortExact hS _ y hy, hsurj⟩

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

def cechHZeroEquivH (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : ι → Opens X)
    (hU : iSup U = ⊤) : cechH G.obj U 0 ≃+ Sheaf.H.{w'} G 0 :=
  (cechHZeroEquiv G.obj U G.property hU).trans (Sheaf.H.equiv₀ G isTerminalTop).symm

variable {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) [Injective S.X₂]

def hDeltaEquiv (m : ℕ) : Sheaf.H.{w'} S.X₃ (m + 1) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) :=
  AddEquiv.ofBijective (H.δ hS (m + 1) (m + 2) rfl)
    ⟨(injective_iff_map_eq_zero _).2 fun y hy => by
        obtain ⟨x, hx⟩ := H.exact₃ hS rfl y hy
        rw [← hx, H.eq_zero_of_injective S.X₂ x, map_zero],
      fun x => H.exact₁ hS rfl x (H.eq_zero_of_injective S.X₂ _)⟩

include hS in

theorem nonempty_cechH_one_equiv (U : ι → Opens X) (hU : iSup U = ⊤)
    (hC : IsCechShortExact U S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj U) :
    Nonempty (cechH S.X₁.obj U 1 ≃+ Sheaf.H.{w'} S.X₁ 1) := by
  let pC : S.X₃.obj.obj (op ⊤) →+ cechH S.X₁.obj U 1 :=
    (hC.delta 0).comp (globalCocycle S.X₃.obj U)
  let pH : S.X₃.obj.obj (op ⊤) →+ Sheaf.H.{w'} S.X₁ 1 :=
    (H.δ hS 0 1 rfl).comp (Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm.toAddMonoidHom
  have hpC : Function.Surjective pC :=
    (hC.delta_surjective hI 0).comp (globalCocycle_surjective _ U S.X₃.property hU)
  have hpH : Function.Surjective pH := by
    intro x
    obtain ⟨y, hy⟩ := H.exact₁ hS rfl x (H.eq_zero_of_injective S.X₂ _)
    exact ⟨Sheaf.H.equiv₀ S.X₃ isTerminalTop y, by simp [pH, hy]⟩
  have hker : pC.ker = pH.ker := by
    ext s
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    have e1 : pC s = 0 ↔ ∃ t, S.g.hom.app (op ⊤) t = s := by
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
    have e2 : pH s = 0 ↔ ∃ t, S.g.hom.app (op ⊤) t = s := by
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
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective pC hpC).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective pH hpH))⟩

end Leray

section LerayTheorem

variable {ι : Type w} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {B : Opens X → Prop} {Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop}

theorem nonempty_cechH_equiv (hC : IsCoverSystem B Good) (U : ι → Opens X) (hU : iSup U = ⊤)
    (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), B (inter U i)) (n : ℕ)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : GoodAcyclic B Good G) :
    Nonempty (cechH G.obj U n ≃+ Sheaf.H.{w'} G n) := by
  cases n with
  | zero => exact ⟨cechHZeroEquivH G U hU⟩
  | succ n =>
    induction n generalizing G with
    | zero =>
      have hS := injectiveSequence_shortExact G
      have hI : CechAcyclic (injectiveSequence G).X₂.obj U :=
        @cechAcyclic_of_injective X (injectiveSequence G).X₂
          (inferInstanceAs (Injective (Injective.under G))) ι U
      exact nonempty_cechH_one_equiv hS U hU (isCechShortExact_of_surjective hS U
        fun i => surjective_of_goodAcyclic hC hS hG _ (hUB i)) hI
    | succ m ih =>
      have hS := injectiveSequence_shortExact G
      have hI : CechAcyclic (injectiveSequence G).X₂.obj U :=
        @cechAcyclic_of_injective X (injectiveSequence G).X₂
          (inferInstanceAs (Injective (Injective.under G))) ι U
      have hSC := isCechShortExact_of_surjective hS U
        fun i => surjective_of_goodAcyclic hC hS hG _ (hUB i)
      have hQ : GoodAcyclic B Good (injectiveSequence G).X₃ :=
        goodAcyclic_of_shortExact hC hS hG fun κ V =>
          @cechAcyclic_of_injective X (injectiveSequence G).X₂
            (inferInstanceAs (Injective (Injective.under G))) κ V
      obtain ⟨e⟩ := ih _ hQ
      exact ⟨((hSC.deltaEquiv hI m).symm.trans e).trans (hDeltaEquiv hS m)⟩

end LerayTheorem

end

end GroundTheory.Arith.SchemeCoh
