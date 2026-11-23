import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecTens

section Lin

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]

theorem dec_comp {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop} (hc : IsLinCat N Hom) {A B P : Type} [Fintype A] [Fintype B]
    [Fintype P] (e : P ≃ A × B) {X : O} {Z : A → O} {S : A → B → O}
    {j : ∀ a, N (Z a) →ₗ[ℂ] N X} {q : ∀ a, N X →ₗ[ℂ] N (Z a)} (h : IsDec Hom X Z j q)
    {io : ∀ a b, N (S a b) →ₗ[ℂ] N (Z a)} {pr : ∀ a b, N (Z a) →ₗ[ℂ] N (S a b)}
    (h2 : ∀ a, IsDec Hom (Z a) (S a) (io a) (pr a)) :
    IsDec Hom X (fun p => S (e p).1 (e p).2) (fun p => j (e p).1 ∘ₗ io (e p).1 (e p).2)
      (fun p => pr (e p).1 (e p).2 ∘ₗ q (e p).1) where
  io_hom p := hc.comp _ _ _ _ _ ((h2 _).io_hom _) (h.io_hom _)
  pr_hom p := hc.comp _ _ _ _ _ (h.pr_hom _) ((h2 _).pr_hom _)
  sum := by
    rw [Equiv.sum_comp e (fun p : A × B => (j p.1 ∘ₗ io p.1 p.2) ∘ₗ (pr p.1 p.2 ∘ₗ q p.1)),
      Fintype.sum_prod_type, ← h.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ext x
    have := congrArg (fun f => j a (f (q a x))) (h2 a).sum
    simpa [map_sum] using this
  pr_io p := by
    ext x
    have h1 := LinearMap.congr_fun (h.pr_io (e p).1) (io (e p).1 (e p).2 x)
    have h3 := LinearMap.congr_fun ((h2 (e p).1).pr_io (e p).2) x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h3 ⊢
    rw [h1, h3]
  pr_io_ne p p' hne := by
    have hne' : e p ≠ e p' := fun hh => hne (e.injective hh)
    generalize e p = s at hne'
    generalize e p' = s' at hne'
    obtain ⟨a, b⟩ := s
    obtain ⟨a', b'⟩ := s'
    ext x
    by_cases ha : a = a'
    · subst ha
      have hb : b ≠ b' := fun hh => hne' (by rw [hh])
      have h1 := LinearMap.congr_fun (h.pr_io a) (io a b' x)
      have h3 := LinearMap.congr_fun ((h2 a).pr_io_ne b b' hb) x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h3 ⊢
      rw [h1, h3]
    · have h1 := LinearMap.congr_fun (h.pr_io_ne a a' ha) (io a' b' x)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 ⊢
      rw [h1, map_zero]

end Lin

variable {k r : ℕ}

theorem mAct_reindex {ι ι' V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (e : ι' → ι) :
    (mAct ((1 : Matrix ι ι ℂ).submatrix e id) : (ι → V) →ₗ[ℂ] (ι' → V)) = LinearMap.funLeft ℂ V e := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct, LinearMap.funLeft_apply, Matrix.one_apply]

theorem hom_reindex (hM : MatHom) (F F' : FRep k r) (U : URep k r) (e : F'.ι ≃ F.ι)
    (h : ∀ g, F'.ρ g = (F.ρ g).submatrix e e) :
    IsHom (F, U) (F', U) (LinearMap.funLeft ℂ U.R.smSub e) := by
  have := hM k r F F' U ((1 : Matrix F.ι F.ι ℂ).submatrix e id) (fun g _ => by
    rw [h g, Matrix.submatrix_mul_equiv, Matrix.mul_one]
    have := Matrix.submatrix_mul_equiv (1 : Matrix F.ι F.ι ℂ) (F.ρ g) e (Equiv.refl _) id
    simpa using this)
  rwa [mAct_reindex] at this

theorem hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) :
    cas Y ∘ₗ f = f ∘ₗ cas X := by
  refine LinearMap.ext fun x => ?_
  have h := fun Z y => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) y
  simp only [LinearMap.comp_apply] at h
  simp only [cas, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h]

theorem dec1 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F, U)} {pr : ∀ a, M (F, U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F', T a))
      (fun a => on1 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.snd : Unit × F'.ι → F'.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F'.ι => ((), c)) ∘ₗ on1 (pr a)) where
  io_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
    (hom_reindex hM F' ((triv k r).tens F') (T a) (Equiv.punitProd _) (fun g => by
      ext c d; simp))
    (hT k r _ _ F' _ _ _ (h.io_hom a)).1
  pr_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
    (hT k r _ _ F' _ _ _ (h.pr_hom a)).1
    (hom_reindex hM ((triv k r).tens F') F' (T a) (Equiv.punitProd _).symm (fun g => by
      ext c d; simp))
  sum := by
    refine LinearMap.ext fun x => funext fun p => ?_
    have := congrFun (LinearMap.congr_fun h.sum (fun c => x (c, p.2))) p.1
    rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
    exact this
  pr_io a := by
    refine LinearMap.ext fun x => funext fun c => ?_
    exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
  pr_io_ne a a' hne := by
    refine LinearMap.ext fun x => funext fun c => ?_
    exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()

theorem dec2 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F', U)} {pr : ∀ a, M (F', U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F', U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F, T a))
      (fun a => on2 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.fst : F.ι × Unit → F.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F.ι => (c, ())) ∘ₗ on2 (pr a)) where
  io_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
    (hom_reindex hM F (F.tens (triv k r)) (T a) (Equiv.prodPUnit _) (fun g => by
      ext c d; simp))
    (hT k r _ _ F _ _ _ (h.io_hom a)).2
  pr_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
    (hT k r _ _ F _ _ _ (h.pr_hom a)).2
    (hom_reindex hM (F.tens (triv k r)) F (T a) (Equiv.prodPUnit _).symm (fun g => by
      ext c d; simp))
  sum := by
    refine LinearMap.ext fun x => funext fun p => ?_
    have := congrFun (LinearMap.congr_fun h.sum (fun c => x (p.1, c))) p.2
    rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
    exact this
  pr_io a := by
    refine LinearMap.ext fun x => funext fun c => ?_
    exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
  pr_io_ne a a' hne := by
    refine LinearMap.ext fun x => funext fun c => ?_
    exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()

theorem decTens : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  intro hC hM hT hL hO k r F F' U hF hF'
  refine ⟨fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_, fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_⟩
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.refl (A × B)) (S := fun a b => one (S (a, b)))
      (dec1 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.1)) (Y := (F, U)) (hO k r) hF (h.io_hom p.1)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.1 p.2 x s.2)) s.1
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.prodComm A B) (S := fun b a => one (S (a, b)))
      (dec2 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.2)) (Y := (F', U)) (hO k r) hF' (h.io_hom p.2)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.2 p.1 x s.1)) s.2

end GlobalTheory.CompanionTheory.ZuckDecTens

end
