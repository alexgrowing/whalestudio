import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.PolAdjoint (pullOver_one)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem cup_add_cup {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : CatCoh.H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a, rfl⟩ := CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := CatCoh.H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add]
  refine CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp a, Z1.comp b, map_mul, map_neg]
  ring

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}

section Def

variable (κ : DividedPowers I) (t : S ⟶ Sp R) (A B : Over S) [GrpObj A] [GrpObj B]

def IsCorrForm (P : LB (A ⊗ B).left) (φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R) : Prop :=
  ∃ (n : ℕ) (a : Fin n → prim κ t A) (b : Fin n → prim κ t B),
    IsChern κ ((A ⊗ B).hom ≫ t) P
      (∑ k, cup _ (pullOver κ t (fst A B) (a k).1) (pullOver κ t (snd A B) (b k).1)) ∧
    ∀ x y, φ x y = ∑ k, x (a k) * y (b k)

structure CupSquare : Prop where
  allPrim : AllPrim κ t A
  span : ∀ z : Cris.H2 κ (A.hom ≫ t), ∃ (n : ℕ) (a b : Fin n → Cris.H1 κ (A.hom ≫ t)), z = ∑ k, cup _ (a k) (b k)
  wedge : ∀ X Y : Cris.H1 κ (A.hom ≫ t) →ₗ[R] R,
    ∃ Λ : Cris.H2 κ (A.hom ≫ t) →ₗ[R] R, ∀ c d, Λ (cup _ c d) = X c * Y d - X d * Y c

def tensorForm {n : ℕ} (a : Fin n → prim κ t A) (b : Fin n → prim κ t B) :
    Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R :=
  ∑ k, (LinearMap.mul R R).compl₁₂ (Module.Dual.eval R _ (a k)) (Module.Dual.eval R _ (b k))

theorem tensorForm_apply {n : ℕ} (a : Fin n → prim κ t A) (b : Fin n → prim κ t B) (x : Crys κ t A)
    (y : Crys κ t B) : tensorForm κ t A B a b x y = ∑ k, x (a k) * y (b k) := by
  simp [tensorForm, LinearMap.sum_apply]

instance isMonHom_one : IsMonHom (1 : A ⟶ B) := inferInstanceAs (IsMonHom (toUnit A ≫ η[B]))

abbrev inl : A ⟶ A ⊗ B := lift (𝟙 A) 1

abbrev inr : B ⟶ A ⊗ B := lift 1 (𝟙 B)

end Def

variable {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

theorem push_one : push κ t (1 : A ⟶ B) = 0 :=
  LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ by
    rw [push_apply, show primPull κ t (1 : A ⟶ B) c = 0 from Subtype.ext (pullOver_one c), map_zero]
    rfl

theorem push_push {C : Over S} [GrpObj C] (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) [IsMonHom f] [IsMonHom g]
    [IsMonHom h] (e : f ≫ g = h) (x : Crys κ t A) : push κ t g (push κ t f x) = push κ t h x := by
  rw [← push_congr κ t e, push_comp]
  rfl

theorem prim_prod (c : prim κ t (A ⊗ B)) : c.1 = pullOver κ t (fst A B) (primPull κ t (inl A B) c).1 +
    pullOver κ t (snd A B) (primPull κ t (inr A B) c).1 := by
  have e : (fst A B ≫ inl A B) * (snd A B ≫ inr A B) = 𝟙 _ := by ext <;> simp [MonObj.mul_comp]
  have h := c.2 _ (fst A B ≫ inl A B) (snd A B ≫ inr A B)
  rw [e, ← pullOver_pullOver, ← pullOver_pullOver] at h
  exact (IsMor.pullCohomologyOne_id _ c.1).symm.trans h

theorem grpMor_prod {σ : R →+* R'} {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : GrpMor κ t A κ' t' A' σ b f) (n : GrpMor κ t B κ' t' B' σ b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    GrpMor κ t (A ⊗ B) κ' t' (A' ⊗ B') σ b h where
  dp := m.dp
  base := m.base
  w := by rw [← Over.w (fst A B), ← Category.assoc, h₁, Category.assoc, m.w, ← Category.assoc, Over.w]
  mul T x y x₀ y₀ hx hy := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change (x₀ * y₀).left ≫ (fst A B).left = ((x * y).left ≫ h) ≫ (fst A B).left
      rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, MonObj.mul_comp,
        MonObj.mul_comp]
      refine m.mul T _ _ _ _ ?_ ?_ <;> simp only [Over.comp_left, hx, hy, Category.assoc, h₁]
    · change (x₀ * y₀).left ≫ (snd A B).left = ((x * y).left ≫ h) ≫ (snd A B).left
      rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, MonObj.mul_comp,
        MonObj.mul_comp]
      refine n.mul T _ _ _ _ ?_ ?_ <;> simp only [Over.comp_left, hx, hy, Category.assoc, h₂]

theorem IsCorrForm.pull {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (hP : P.IsLB) {σ : R →+* R'} {b : S' ⟶ S} {f : A'.left ⟶ A.left}
    {g : B'.left ⟶ B.left} (m : GrpMor κ t A κ' t' A' σ b f) (n : GrpMor κ t B κ' t' B' σ b g)
    {h : (A' ⊗ B').left ⟶ (A ⊗ B).left} (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f)
    (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) {P' : LB (A' ⊗ B').left} (hP' : P'.IsLB)
    (e : LBIso (P.pull h) P') :
    ∃ φ', IsCorrForm κ' t' A' B' P' φ' ∧
      ∀ x x' y y', m.Corr x x' → n.Corr y y' → φ' x' y' = σ (φ x y) := by
  obtain ⟨N, a, c, hc, hφ⟩ := H
  have k := grpMor_prod m n h₁ h₂
  refine ⟨tensorForm κ' t' A' B' (fun i ↦ m.pull (a i)) fun i ↦ n.pull (c i),
    ⟨N, _, _, (isChern_existsUnique_and_iso R' _ κ' _ _).2 _ _ (pull_isLB hP h) hP' e _ ?_,
      tensorForm_apply _ _ _ _ _ _⟩, fun x x' y y' hx hy ↦ ?_⟩
  · have := isChern_pull k.isMor hc
    rw [map_sum] at this
    convert this using 2 with i
    rw [IsMor.pullCohomologyTwo_cup]
    congr 1
    · congr 1
      exact (IsMor.pullback1_comp _ _ (m.comp (homMor κ' t' (fst A' B'))).isMor (fun _ ↦ rfl) rfl _).trans
        (IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) h₁ _).symm
    · exact (IsMor.pullback1_comp _ _ (n.comp (homMor κ' t' (snd A' B'))).isMor (fun _ ↦ rfl) rfl _).trans
        (IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) h₂ _).symm
  · simp only [tensorForm_apply, hφ, map_sum, map_mul, hx _, hy _]

theorem IsCorrForm.unique (C : CupSquare κ t (A ⊗ B)) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    {φ φ' : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R} (H : IsCorrForm κ t A B P φ) (H' : IsCorrForm κ t A B P φ') :
    φ = φ' := by
  refine LinearMap.ext₂ fun x y ↦ ?_
  let E : prim κ t (A ⊗ B) ≃ₗ[R] Cris.H1 κ ((A ⊗ B).hom ≫ t) := LinearEquiv.ofTop _ C.allPrim
  obtain ⟨Λ, hΛ⟩ := C.wedge (push κ t (inl A B) x ∘ₗ E.symm.toLinearMap) (push κ t (inr A B) y ∘ₗ E.symm.toLinearMap)
  have key : ∀ (a : prim κ t A) (b : prim κ t B),
      Λ (cup _ (pullOver κ t (fst A B) a.1) (pullOver κ t (snd A B) b.1)) = x a * y b := fun a b ↦ by
    have e₁ : E.symm (pullOver κ t (fst A B) a.1) = primPull κ t (fst A B) a := Subtype.ext rfl
    have e₂ : E.symm (pullOver κ t (snd A B) b.1) = primPull κ t (snd A B) b := Subtype.ext rfl
    simp only [hΛ, LinearMap.comp_apply, LinearEquiv.coe_coe, e₁, e₂, ← push_apply]
    rw [push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_snd _ _), push_id,
      push_id, push_one]
    simp
  obtain ⟨n, a, b, hc, hφ⟩ := H
  obtain ⟨n', a', b', hc', hφ'⟩ := H'
  have e := congrArg Λ (((isChern_existsUnique_and_iso R _ κ _ _).1 _ hP).unique hc hc')
  simpa only [map_sum, key, ← hφ, ← hφ'] using e

theorem eq_zero_of_triv {X : Scheme.{0}} {s : X ⟶ Sp R} {L : LB X} (hL : L.IsLB) (h : Triv L) {z : Cris.H2 κ s}
    (hz : IsChern κ s L z) : z = 0 :=
  have C := isChern_existsUnique_and_iso R _ κ _ s
  (C.1 _ hL).unique hz (C.2 _ _ (LB.isLB_triv X) hL ((CechPic.iso_triv_iff L).2 h) _
    (isChern_zero _ _ _ fun _ _ ↦ rfl))

theorem crystallinePull2_sum_cup {X Y : Over S} (f : Y ⟶ X)
    (m : IsMor κ (X.hom ≫ t) κ (Y.hom ≫ t) (RingHom.id R) f.left) {n : ℕ}
    (a b : Fin n → Cris.H1 κ (X.hom ≫ t)) :
    m.pull2 (∑ k, cup _ (a k) (b k)) = ∑ k, cup _ (pullOver κ t f (a k)) (pullOver κ t f (b k)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ IsMor.pullCohomologyTwo_cup _ _ _

theorem exists_isCorrForm (C : CupSquare κ t (A ⊗ B)) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) :
    ∃ φ, IsCorrForm κ t A B P φ := by
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso R _ κ _ ((A ⊗ B).hom ≫ t)).1 _ hP
  obtain ⟨n, u, v, rfl⟩ := C.span z
  have hm : ∀ c, c ∈ prim κ t (A ⊗ B) := fun c ↦ C.allPrim ▸ trivial
  let l : Cris.H1 κ ((A ⊗ B).hom ≫ t) → prim κ t A := fun c ↦ primPull κ t (inl A B) ⟨c, hm c⟩
  let r : Cris.H1 κ ((A ⊗ B).hom ≫ t) → prim κ t B := fun c ↦ primPull κ t (inr A B) ⟨c, hm c⟩
  have d : ∀ c, c = pullOver κ t (fst A B) (l c).1 + pullOver κ t (snd A B) (r c).1 := fun c ↦ prim_prod ⟨c, hm c⟩
  have z₁ : ∑ k, cup _ (pullOver κ t (fst A B) (l (u k)).1) (pullOver κ t (fst A B) (l (v k)).1) = 0 := by
    have e := eq_zero_of_triv (pull_isLB hP _) h₂ (isChern_pull (homMor κ t (inl A B)).isMor hz)
    rw [crystallinePull2_sum_cup] at e
    rw [← crystallinePull2_sum_cup _ (homMor κ t (fst A B)).isMor]
    exact (congrArg _ e).trans (map_zero _)
  have z₂ : ∑ k, cup _ (pullOver κ t (snd A B) (r (u k)).1) (pullOver κ t (snd A B) (r (v k)).1) = 0 := by
    have e := eq_zero_of_triv (pull_isLB hP _) h₁ (isChern_pull (homMor κ t (inr A B)).isMor hz)
    rw [crystallinePull2_sum_cup] at e
    rw [← crystallinePull2_sum_cup _ (homMor κ t (snd A B)).isMor]
    exact (congrArg _ e).trans (map_zero _)
  refine ⟨_, n + n, Fin.append (fun k ↦ l (u k)) fun k ↦ -l (v k), Fin.append (fun k ↦ r (v k)) fun k ↦ r (u k),
    ?_, tensorForm_apply _ _ _ _ _ _⟩
  convert hz using 1
  rw [Fin.sum_univ_add, ← add_zero (_ + _), ← add_zero (0 : Cris.H2 κ _)]
  nth_rw 1 [← z₁, ← z₂]
  simp only [Fin.append_left, Fin.append_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  conv_rhs => rw [d (u k), d (v k)]
  simp only [Submodule.coe_neg, map_neg, LinearMap.neg_apply, map_add, LinearMap.add_apply]
  rw [neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  abel

theorem IsCorrForm.adjoint {A₁ B₁ : Over S} [GrpObj A₁] [GrpObj B₁] (C : CupSquare κ t (A ⊗ B₁))
    {P : LB (A ⊗ B).left} {P₁ : LB (A₁ ⊗ B₁).left} (hP : P.IsLB) (hP₁ : P₁.IsLB)
    {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R} {φ₁ : Crys κ t A₁ →ₗ[R] Crys κ t B₁ →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (H₁ : IsCorrForm κ t A₁ B₁ P₁ φ₁) (u : A ⟶ A₁) (v : B₁ ⟶ B) [IsMonHom u]
    [IsMonHom v] (e : LBIso (ev P (fst A B₁) (snd A B₁ ≫ v)) (ev P₁ (fst A B₁ ≫ u) (snd A B₁)))
    (x : Crys κ t A) (y : Crys κ t B₁) : φ x (push κ t v y) = φ₁ (push κ t u x) y := by
  obtain ⟨χ, hχ, k⟩ := H.pull hP (homMor κ t (𝟙 A)) (homMor κ t v) (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id]) (pull_isLB hP₁ _) e
  obtain ⟨χ₁, hχ₁, k₁⟩ := H₁.pull hP₁ (homMor κ t u) (homMor κ t (𝟙 B₁))
    (h := (lift (fst A B₁ ≫ u) (snd A B₁)).left) (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id]) (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (pull_isLB hP₁ _) (ChernExists.lbIso_refl (pull_isLB hP₁ _))
  obtain rfl := hχ.unique C (pull_isLB hP₁ _) hχ₁
  have e₁ := k (push κ t (𝟙 A) x) x (push κ t v y) y (fun _ ↦ rfl) fun _ ↦ rfl
  have e₂ := k₁ (push κ t u x) x (push κ t (𝟙 B₁) y) y (fun _ ↦ rfl) fun _ ↦ rfl
  have e₃ : φ (push κ t (𝟙 A) x) (push κ t v y) = φ₁ (push κ t u x) (push κ t (𝟙 B₁) y) := e₁.symm.trans e₂
  rwa [push_id, push_id] at e₃

theorem IsCorrForm.isPolForm {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) : ∃ ψ, IsPolForm κ t (A ⊗ B) P ψ ∧ ∀ X Y, ψ X Y =
      φ (push κ t (fst A B) X) (push κ t (snd A B) Y) - φ (push κ t (fst A B) Y) (push κ t (snd A B) X) := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  refine ⟨_, ⟨n, fun k ↦ primPull κ t (fst A B) (a k), fun k ↦ primPull κ t (snd A B) (b k), hc, rfl⟩,
    fun X Y ↦ ?_⟩
  rw [wedgeForm_apply, hφ, hφ, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg₂ (· - ·) rfl (mul_comm _ _)

theorem isCorrForm_lam [IsCommMonObj A] {L : LB A.left} {ψ : LinearMap.BilinForm R (Crys κ t A)}
    (H : IsPolForm κ t A L ψ) : IsCorrForm κ t A A (abelian₂ A L) ψ := by
  obtain ⟨n, a, b, hc, rfl⟩ := H
  refine ⟨n + n, Fin.append a fun k ↦ -b k, Fin.append b a, ?_, fun x y ↦ ?_⟩
  · refine (congrArg (IsChern κ _ _) ?_).mpr (PolAdjoint.isChern_cube hc (fst A A) (snd A A))
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, ← Finset.sum_add_distrib, Submodule.coe_neg,
      map_neg, LinearMap.neg_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  · simp only [wedgeForm_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right, map_neg, neg_mul,
      sub_eq_add_neg, Finset.sum_add_distrib]

theorem CupSquare.of_bijective {J : Ideal R} {κ₁ : DividedPowers J} {u : S' ⟶ Sp R} (C : CupSquare κ t A)
    {b : S' ⟶ S} {f : A'.left ⟶ A.left} (m : GrpMor κ t A κ₁ u A' (RingHom.id R) b f)
    (h₁ : Function.Bijective m.isMor.pull1) (h₂ : Function.Bijective m.isMor.pull2) : CupSquare κ₁ u A' := by
  refine ⟨eq_top_iff.2 fun c _ ↦ ?_, fun z ↦ ?_, fun X Y ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := h₁.2 c
    exact m.pullback_mem_primitive (C.allPrim ▸ trivial)
  · obtain ⟨z, rfl⟩ := h₂.2 z
    obtain ⟨n, a, c, rfl⟩ := C.span z
    exact ⟨n, _, _, (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ IsMor.pullCohomologyTwo_cup _ _ _)⟩
  · obtain ⟨Λ, hΛ⟩ := C.wedge (X ∘ₗ m.isMor.pull1) (Y ∘ₗ m.isMor.pull1)
    refine ⟨Λ ∘ₗ (LinearEquiv.ofBijective _ h₂).symm.toLinearMap, fun c d ↦ ?_⟩
    obtain ⟨c, rfl⟩ := h₁.2 c
    obtain ⟨d, rfl⟩ := h₁.2 d
    rw [← IsMor.pullCohomologyTwo_cup]
    exact (congrArg Λ ((LinearEquiv.ofBijective _ h₂).symm_apply_apply _)).trans (hΛ c d)

theorem exists_prod_pullback {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) : ∃ h : (A' ⊗ B').left ⟶ (A ⊗ B).left,
      h ≫ (fst A B).left = (fst A' B').left ≫ f ∧ h ≫ (snd A B).left = (snd A' B').left ≫ g :=
  ⟨Limits.pullback.lift ((fst A' B').left ≫ f) ((snd A' B').left ≫ g) (by
      rw [Category.assoc, Category.assoc, m.1.w, n.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
    Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩

omit [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] in

theorem isPullback_prod {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsPullback f A'.hom A.hom b) (n : IsPullback g B'.hom B.hom b) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsPullback h (A' ⊗ B').hom (A ⊗ B).hom b := by
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A' B').left (snd A' B').left A'.hom B'.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← n.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert n
  rwa [Over.w, Over.w] at r

section Abelian

open GlobalTheory.Published

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g g' : ℕ}

omit [GrpObj A] [GrpObj B] in

theorem smooth_prod (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom) :
    SmoothOfRelativeDimension (g' + g) (A ⊗ B).hom := by
  have : SmoothOfRelativeDimension g' (Limits.pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip hg'
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g' g _ _

theorem cupSquare_of_free (H : AbelianDeRham.Free) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : CupSquare (dp0 R) (𝟙 _) A := by
  obtain ⟨h0, -, -, -, e, he⟩ := H R A g hA hg
  refine ⟨h0, fun z ↦ ?_, PolAdjoint.exists_wedge_functional H hA hg⟩
  obtain ⟨n, a, b, hab⟩ := PolExists.exists_sum_wedge (e.symm z)
  exact ⟨n, a, b, by rw [← e.apply_symm_apply z, ← hab, map_sum]; exact Finset.sum_congr rfl fun k _ ↦ he _ _⟩

theorem IsCorrForm.perfect (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hB : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g' B.hom) {P : LB (A ⊗ B).left}
    (hP : IsPerfect A B P) {φ : HdR A →ₗ[R] HdR B →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A B P φ) :
    φ.IsPerfPair ∧ (∀ x, x ∈ Fil A ↔ ∀ y ∈ Fil B, φ x y = 0) ∧ ∀ y, y ∈ Fil B ↔ ∀ x ∈ Fil A, φ x y = 0 := by
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have gAB := smooth_prod hg hg'
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, perf⟩ := H.2.2.2.2 R _ _ hAB gAB P hP.isLB ψ hψ
  have perf := perf hP.kTriv
  obtain ⟨_, _, hrk⟩ := AbelianDeRham.Free.prim H.1 hAB gAB
  obtain ⟨-, ⟨N, hN⟩, _, _, hF⟩ := H.2.1 R _ _ hAB gAB
  have lag := PolExistsRing.mem_of_annihilates_dual ψ (PrimitiveSubmodule (A ⊗ B)) N hN _ hrk hF iso
  have a₁ : ∀ x, push (dp0 R) (𝟙 _) (fst A B) (push (dp0 R) (𝟙 _) (inl A B) x) = x := fun x ↦ by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : ∀ x, push (dp0 R) (𝟙 _) (snd A B) (push (dp0 R) (𝟙 _) (inl A B) x) = 0 := fun x ↦ by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : ∀ y, push (dp0 R) (𝟙 _) (fst A B) (push (dp0 R) (𝟙 _) (inr A B) y) = 0 := fun x ↦ by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : ∀ y, push (dp0 R) (𝟙 _) (snd A B) (push (dp0 R) (𝟙 _) (inr A B) y) = y := fun x ↦ by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have l : ∀ x Y, ψ (push (dp0 R) (𝟙 _) (inl A B) x) Y = φ x (push (dp0 R) (𝟙 _) (snd A B) Y) := fun x Y ↦ by
    rw [e, a₁, a₂, map_zero, sub_zero]
  have r : ∀ X y, ψ X (push (dp0 R) (𝟙 _) (inr A B) y) = φ (push (dp0 R) (𝟙 _) (fst A B) X) y := fun X y ↦ by
    rw [e, b₁, b₂, map_zero, LinearMap.zero_apply, sub_zero]
  refine ⟨⟨⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun k ↦ ?_⟩,
    ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_, fun k ↦ ?_⟩⟩,
    fun x ↦ ⟨fun hx y hy ↦ ?_, fun hx ↦ ?_⟩, fun y ↦ ⟨fun hy x hx ↦ ?_, fun hy ↦ ?_⟩⟩
  · rw [← a₁ x, (injective_iff_map_eq_zero _).1 perf.bijective_left.1 (push (dp0 R) (𝟙 _) (inl A B) x)
      (LinearMap.ext fun Y ↦ by rw [l, hx]; rfl), map_zero]
  · obtain ⟨X, hX⟩ := perf.bijective_left.2 (k ∘ₗ push (dp0 R) (𝟙 _) (snd A B))
    exact ⟨_, LinearMap.ext fun y ↦ by rw [← r, hX, LinearMap.comp_apply, b₂]⟩
  · rw [← b₂ y, (injective_iff_map_eq_zero _).1 perf.bijective_right.1 (push (dp0 R) (𝟙 _) (inr A B) y)
      (LinearMap.ext fun X ↦ (r X y).trans (LinearMap.congr_fun hy _)), map_zero]
  · obtain ⟨Y, hY⟩ := perf.bijective_right.2 (k ∘ₗ push (dp0 R) (𝟙 _) (fst A B))
    exact ⟨_, LinearMap.ext fun x ↦ (l x Y).symm.trans ((LinearMap.congr_fun hY _).trans (congrArg k (a₁ x)))⟩
  · rw [← b₂ y, ← l]
    exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)
  · rw [← a₁ x]
    exact push_mem_Fil _ (lag _ fun Y hY ↦ (l x Y).trans (hx _ (push_mem_Fil _ hY)))
  · rw [← b₂ y, ← l]
    exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)
  · rw [← b₂ y]
    refine push_mem_Fil _ (lag _ fun X hX ↦ ?_)
    rw [e, b₁, b₂, map_zero, LinearMap.zero_apply, hy _ (push_mem_Fil _ hX), sub_zero]

end Abelian

end GlobalTheory.AbDual
