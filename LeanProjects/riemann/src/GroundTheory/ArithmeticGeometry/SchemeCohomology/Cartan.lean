import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InjectiveCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

section

variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

lemma res_congr {n : ℕ} (σ : Cochain P U n) {j₁ j₂ : Fin (n + 1) → ι} (h : j₁ = j₂)
    {V : Opens X} (h₁ : V ≤ inter U j₁) (h₂ : V ≤ inter U j₂) :
    res P h₁ (σ j₁) = res P h₂ (σ j₂) := by
  subst h
  rfl

lemma le_inter_const {n : ℕ} (a : ι) : U a ≤ inter U (fun _ : Fin n => a) := by
  intro x hx
  rw [mem_inter_iff]
  exact fun _ => hx

lemma inter_succ {n : ℕ} (i : Fin (n + 2) → ι) :
    inter U i = U (i 0) ⊓ inter U (i ∘ Fin.succ) := by
  ext x
  simp only [SetLike.mem_coe, Opens.mem_inf, mem_inter_iff, Fin.forall_fin_succ, Function.comp]

lemma d_zero_apply (σ : Cochain P U 0) (i : Fin 2 → ι) :
    d P U 0 σ i = res P (inter_le_comp U i (0 : Fin 2).succAbove) (σ (i ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U i (1 : Fin 2).succAbove) (σ (i ∘ (1 : Fin 2).succAbove)) := by
  rw [d_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

def constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) : Cochain P U 0 :=
  fun i => res P ((inter_le U i 0).trans (hUV (i 0))) s

lemma d_constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) :
    d P U 0 (constCochain P U hUV s) = 0 := by
  funext i
  rw [d_zero_apply]
  simp only [constCochain, res_res, sub_self]
  rfl

end

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)

include hP in

lemma exists_glue {ι : Type w} (U : ι → Opens X) (V : Opens X) (hUV : ∀ a, U a ≤ V)
    (hV : V ≤ iSup U) (τ : Cochain P U 0) (hτ : d P U 0 τ = 0) :
    ∃ t : P.obj (op V), ∀ i : Fin 1 → ι,
      res P ((inter_le U i 0).trans (hUV (i 0))) t = τ i := by
  let sf : ∀ j, P.obj (op (U j)) := fun j => res P (le_inter_const U j) (τ (fun _ => j))
  have compat : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    have h := congrFun hτ ![i, j]
    rw [d_zero_apply] at h
    have hle : U i ⊓ U j ≤ inter U ![i, j] := by
      intro x hx
      rw [mem_inter_iff]
      intro a
      fin_cases a
      · exact hx.1
      · exact hx.2
    rw [Pi.zero_apply] at h
    have h' := congrArg (res P hle) h
    rw [map_sub, res_res, res_res, map_zero, sub_eq_zero] at h'
    have e0 : (![i, j] ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => j := by
      funext a; fin_cases a; rfl
    have e1 : (![i, j] ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => i := by
      funext a; fin_cases a; rfl
    rw [res_congr P U τ e0 _ ((inf_le_right).trans (le_inter_const U j)),
      res_congr P U τ e1 _ ((inf_le_left).trans (le_inter_const U i))] at h'
    change res P inf_le_left (sf i) = res P inf_le_right (sf j)
    simp only [sf, res_res]
    exact h'.symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    U V (fun a => homOfLE (hUV a)) hV sf compat
  refine ⟨t, fun i => ?_⟩
  have hi : (fun _ : Fin 1 => i 0) = i := funext fun a => by rw [Subsingleton.elim a 0]
  have ht' : res P (hUV (i 0)) t = sf (i 0) := ht (i 0)
  rw [← res_res P (inter_le U i 0) (hUV (i 0)), ht']
  simp only [sf, res_res]
  exact (res_congr P U τ hi _ le_rfl).trans (res_refl _ _ _)

variable {P} in

lemma CechAcyclic.of_shortExact' {ι : Type w} (U : ι → Opens X)
    {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q) (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i))))
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

section

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

include hS in
lemma app_injective_of_shortExact (W : (Opens X)ᵒᵖ) : Function.Injective (S.f.hom.app W) := by
  have : Mono S.f := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this W)

include hS in
lemma app_exact_of_shortExact (W : Opens X) (y : S.X₂.obj.obj (op W))
    (hy : S.g.hom.app (op W) y = 0) : ∃ x, S.f.hom.app (op W) x = y :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.1 hS.2 y hy

set_option backward.isDefEq.respectTransparency false in
lemma comp_hom_eq_zero : S.f.hom ≫ S.g.hom = 0 := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, S.zero]
  rfl

lemma app_comp_apply_eq_zero (W : (Opens X)ᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, comp_hom_eq_zero]
  rfl

end

variable (B : Opens X → Prop)

def CechCondition (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), (∀ a, B (U a)) → iSup U = V →
    CechAcyclic F.obj U

variable {B}

lemma inter_mem (hinf : ∀ V W, B V → B W → B (V ⊓ W)) {ι : Type w} (U : ι → Opens X)
    (hU : ∀ a, B (U a)) {n : ℕ} (i : Fin (n + 1) → ι) : B (inter U i) := by
  induction n with
  | zero =>
    have : inter U i = U (i 0) := le_antisymm (inter_le U i 0) (by
      intro x hx
      rw [mem_inter_iff]
      intro a
      rwa [Fin.fin_one_eq_zero a])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [inter_succ]
    exact hinf _ _ (hU _) (ih _)

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

end GroundTheory.Arith.SchemeCoh
