import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe w u v

variable {X : TopCat.{u}} {ι : Type w}

def inter (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) : Opens X := ⨅ a, U (i a)

lemma inter_le_comp (U : ι → Opens X) {m n : ℕ} (i : Fin n → ι) (θ : Fin m → Fin n) :
    inter U i ≤ inter U (i ∘ θ) :=
  le_iInf fun a => iInf_le (fun b => U (i b)) (θ a)

lemma inter_le (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) (a : Fin n) : inter U i ≤ U (i a) :=
  iInf_le (fun b => U (i b)) a

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

abbrev Cochain (n : ℕ) : Type (max w u) := ∀ i : Fin (n + 1) → ι, P.obj (op (inter U i))

def res {V W : Opens X} (h : V ≤ W) : P.obj (op W) →+ P.obj (op V) :=
  (P.map (homOfLE h).op).hom

@[simp] lemma res_res {V W Z : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ Z) (x : P.obj (op Z)) :
    res P h₁ (res P h₂ x) = res P (h₁.trans h₂) x := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] lemma res_refl {V : Opens X} (h : V ≤ V) (x : P.obj (op V)) : res P h x = x := by
  simp only [res]
  have : (homOfLE h).op = 𝟙 (op V) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

def cochainMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : Cochain P U m →+ Cochain P U n where
  toFun σ i := res P (inter_le_comp U i θ) (σ (i ∘ θ))
  map_zero' := by ext i; simp
  map_add' σ τ := by ext i; simp

noncomputable def cechCosimplicial : CosimplicialObject AddCommGrpCat.{max w u} where
  obj n := AddCommGrpCat.of (Cochain P U n.len)
  map θ := AddCommGrpCat.ofHom (cochainMap P U θ.toOrderHom)
  map_id n := by
    ext σ i
    simp only [cochainMap]
    exact res_refl P _ _
  map_comp θ θ' := by
    ext σ i
    simp [cochainMap]
    rfl

lemma hom_finset_sum_apply {M N : AddCommGrpCat.{v}} {α : Type*} (s : Finset α)
    (f : α → (M ⟶ N)) (x : M) : (∑ a ∈ s, f a).hom x = ∑ a ∈ s, (f a).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add, AddMonoidHom.add_apply, ih]

noncomputable def d (n : ℕ) : Cochain P U n →+ Cochain P U (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial P U) n).hom

lemma d_apply (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 2) → ι) :
    d P U n σ i = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      res P (inter_le_comp U i k.succAbove) (σ (i ∘ k.succAbove)) := by
  have h := hom_finset_sum_apply Finset.univ
    (fun k : Fin (n + 2) => ((-1 : ℤ) ^ (k : ℕ)) • (cechCosimplicial P U).δ k) σ
  refine (congrFun h i).trans ((Finset.sum_apply i _ _).trans ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

lemma d_d (n : ℕ) (σ : Cochain P U n) : d P U (n + 1) (d P U n σ) = 0 := by
  have := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cechCosimplicial P U) n
  have h2 := congrArg (fun f => f.hom σ) this
  exact h2

variable {P} in

def push {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) :
    Cochain P U n →+ Cochain P' U n where
  toFun σ i := φ.app _ (σ i)
  map_zero' := by ext i; simp
  map_add' σ τ := by ext i; simp

variable {P} in
lemma app_res {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') {V W : Opens X} (h : V ≤ W)
    (x : P.obj (op W)) : φ.app (op V) (res P h x) = res P' h (φ.app (op W) x) := by
  simp only [res, ← ConcreteCategory.comp_apply, φ.naturality]

variable {P} in
lemma push_d {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) (σ : Cochain P U n) :
    push U φ (n + 1) (d P U n σ) = d P' U n (push U φ n σ) := by
  funext i
  simp only [push, AddMonoidHom.coe_mk, ZeroHom.coe_mk, d_apply, map_sum, map_zsmul, app_res]

variable {P} in
lemma push_comp {P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (ψ : P' ⟶ P'')
    (n : ℕ) (σ : Cochain P U n) : push U ψ n (push U φ n σ) = push U (φ ≫ ψ) n σ := by
  funext i
  simp [push]

variable {P} in
lemma push_id (n : ℕ) (σ : Cochain P U n) : push U (𝟙 P) n σ = σ := by
  funext i
  simp [push]

def CechAcyclic : Prop :=
  ∀ (n : ℕ) (σ : Cochain P U (n + 1)), d P U (n + 1) σ = 0 → ∃ τ, d P U n τ = σ

variable {P} in
lemma push_zero' {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (n : ℕ) (σ : Cochain P U n) :
    push U (0 : P ⟶ P') n σ = 0 := by
  funext i
  simp [push]

variable {P} in
lemma push_injective {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ)
    (h : ∀ i : Fin (n + 1) → ι, Function.Injective (φ.app (op (inter U i)))) :
    Function.Injective (push U φ n) := fun _ _ hστ =>
  funext fun i => h i (congrFun hστ i)

variable {P} in

lemma CechAcyclic.of_retract {G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (ι' : P ⟶ G) (r : G ⟶ P)
    (hr : ι' ≫ r = 𝟙 P) (hG : CechAcyclic G U) : CechAcyclic P U := by
  intro n σ hσ
  obtain ⟨τ, hτ⟩ := hG n (push U ι' (n + 1) σ) (by rw [← push_d, hσ, map_zero])
  refine ⟨push U r n τ, ?_⟩
  rw [← push_d, hτ, push_comp, hr, push_id]

variable {P} in

lemma CechAcyclic.of_shortExact {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q)
    (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin n → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin n → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin n → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by
  intro n σ hσ

  choose τ hτ using fun i => hsurj i (σ i)
  have hτ' : push U g (n + 1) τ = σ := funext hτ

  have h0 : push U g (n + 2) (d I U (n + 1) τ) = 0 := by rw [push_d, hτ', hσ]
  choose ρ hρ using fun j => hex j _ (congrFun h0 j)
  have hρ' : push U f (n + 2) ρ = d I U (n + 1) τ := funext hρ

  have hρc : d F U (n + 2) ρ = 0 := by
    apply push_injective U f (n + 3) (fun j => hinj j)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨α, hα⟩ := hF (n + 1) ρ hρc

  have hc : d I U (n + 1) (τ - push U f (n + 1) α) = 0 := by
    rw [map_sub, ← push_d, hα, hρ', sub_self]
  obtain ⟨β, hβ⟩ := hI n _ hc
  refine ⟨push U g n β, ?_⟩
  rw [← push_d, hβ, map_sub, hτ', push_comp, hfg, push_zero', sub_zero]

def discPresheaf (A : X → AddCommGrpCat.{u}) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (∀ x : W.unop, A x.1)
  map h := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, h.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

variable (A : X → AddCommGrpCat.{u})

def ev {W : Opens X} (x : X) (hx : x ∈ W) : (discPresheaf A).obj (op W) →+ A x :=
  Pi.evalAddMonoidHom (fun y : W => A y.1) ⟨x, hx⟩

lemma ev_res {V W : Opens X} (h : V ≤ W) (s : (discPresheaf A).obj (op W)) (x : X) (hx : x ∈ V) :
    ev A x hx (res (discPresheaf A) h s) = ev A x (h hx) s := rfl

variable {U} in
lemma ev_congr {n : ℕ} (σ : Cochain (discPresheaf A) U n) {j₁ j₂ : Fin (n + 1) → ι}
    (h : j₁ = j₂) (x : X) (h₁ : x ∈ inter U j₁) (h₂ : x ∈ inter U j₂) :
    ev A x h₁ (σ j₁) = ev A x h₂ (σ j₂) := by
  subst h
  rfl

lemma ev_d {n : ℕ} (σ : Cochain (discPresheaf A) U n) (i : Fin (n + 2) → ι) (x : X)
    (hx : x ∈ inter U i) :
    ev A x hx (d (discPresheaf A) U n σ i) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      ev A x (inter_le_comp U i k.succAbove hx) (σ (i ∘ k.succAbove)) := by
  rw [d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, ev_res]

lemma mem_inter_iff {n : ℕ} (i : Fin n → ι) (x : X) : x ∈ inter U i ↔ ∀ a, x ∈ U (i a) := by
  rw [inter, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

attribute [irreducible] inter

lemma cons_comp_succAbove_zero {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext a
  simp

lemma cons_comp_succAbove_succ {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons c (i ∘ k.succAbove) := by
  funext a
  cases a using Fin.cases with
  | zero => simp
  | succ a => simp

noncomputable def chosenIdx (x : X) (h : ∃ a, x ∈ U a) : ι := h.choose

lemma mem_chosenIdx (x : X) (h : ∃ a, x ∈ U a) : x ∈ U (chosenIdx U x h) := h.choose_spec

lemma exists_mem_of_mem_inter {m : ℕ} (j : Fin (m + 1) → ι) {x : X} (hx : x ∈ inter U j) :
    ∃ a, x ∈ U a :=
  ⟨j 0, (mem_inter_iff U j x).1 hx 0⟩

lemma mem_inter_cons {m : ℕ} (j : Fin (m + 1) → ι) {x : X} (hx : x ∈ inter U j) :
    x ∈ inter U (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j :
      Fin (m + 2) → ι) := by
  rw [mem_inter_iff]
  intro a
  cases a using Fin.cases with
  | zero => simpa using mem_chosenIdx U x _
  | succ a => simpa using (mem_inter_iff U j x).1 hx a

noncomputable def homotopy {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) :
    Cochain (discPresheaf A) U n :=
  fun j y => ev A y.1 (mem_inter_cons U j y.2)
    (σ (Fin.cons (chosenIdx U y.1 (exists_mem_of_mem_inter U j y.2)) j))

lemma ev_homotopy {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) (j : Fin (n + 1) → ι)
    (x : X) (hx : x ∈ inter U j) :
    ev A x hx (homotopy U A σ j) = ev A x (mem_inter_cons U j hx)
      (σ (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j)) := rfl

theorem cechAcyclic_discPresheaf : CechAcyclic (discPresheaf A) U := by
  intro n σ hσ
  refine ⟨homotopy U A σ, funext fun i => funext fun y => ?_⟩
  obtain ⟨x, hx⟩ := y
  have hJ := mem_inter_cons U i hx
  have hcoc : ev A x hJ (d (discPresheaf A) U (n + 1) σ
      (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U i hx)) i)) = 0 := by
    rw [hσ]
    rfl
  rw [ev_d, Fin.sum_univ_succ] at hcoc
  change ev A x hx (d (discPresheaf A) U n (homotopy U A σ) i) = ev A x hx (σ i)
  rw [ev_d]
  rw [Fin.val_zero, pow_zero, one_smul,
    ev_congr A σ (cons_comp_succAbove_zero _ i) x _ hx] at hcoc
  rw [eq_neg_of_add_eq_zero_left hcoc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg, ev_homotopy]
  exact congrArg _ (ev_congr A σ (cons_comp_succAbove_succ _ i k).symm x _ _)

end GroundTheory.Arith.SchemeCoh
