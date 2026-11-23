import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEqOneComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Tate

variable {p : ℕ} {M : Type} [CommGroup M]

theorem lev_sum {J : Type} (s : Finset J) (t : J → Tate p M) (n : ℕ) :
    (∑ a ∈ s, t a).lev n = ∏ a ∈ s, (t a).lev n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem lev_nsmul (N : ℕ) (t : Tate p M) (n : ℕ) : (N • t).lev n = t.lev n ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem tate_map_bijective [Fact p.Prime] {M' : Type} [CommGroup M'] {f : M →* M'} (hf : Function.Injective f)
    (h : ∀ (n : ℕ) (y : M'), y ^ p ^ n = 1 → ∃ x, f x = y) : Function.Bijective (Tate.map p f) := by
  refine ⟨Tate.map_injective hf, fun t => ?_⟩
  choose s hs using fun n => h n _ (t.lev_pow n)
  exact ⟨Tate.mk s fun n => ⟨hf (by rw [map_pow, hs, t.lev_pow, map_one]), hf (by rw [map_pow, hs, hs, t.lev_succ])⟩,
    Tate.ext hs⟩

end Tate

section Algebraic

variable {R Ω C : Type} [CommRing R] [Field Ω] [Field C] (α : R →+* Ω) (κ : Ω →+* C) {β : R →+* C}
  (hβ : κ.comp α = β)

def extPt : (Over.mk (spMap β) : Over (Sp R)) ⟶ Over.mk (spMap α) :=
  Over.homMk (spMap κ) (by subst hβ; exact (Spec.map_comp _ _).symm)

theorem extPt_injective (G : Over (Sp R)) : Function.Injective fun x : Over.mk (spMap α) ⟶ G => extPt α κ hβ ≫ x := by
  haveI : Epi (spMap κ) := by
    letI := κ.toAlgebra
    haveI : Flat (spMap κ) := (Flat.SpecMap_iff).2 (inferInstanceAs (Module.Flat Ω C))
    exact Flat.epi_of_flat_of_surjective _
  exact fun x y h => Over.OverMorphism.ext ((cancel_epi (spMap κ)).1 (congrArg (·.left) h))

theorem exists_extPt_eq [IsNoetherianRing R] [IsAlgClosed Ω] [IsAlgClosed C] [CharZero C] (B : Out.PolAV (Sp R)) {n : ℕ}
    (hn : 1 ≤ n) (y : Over.mk (spMap β) ⟶ B.A) (hy : y ^ n = 1) :
    ∃ x : Over.mk (spMap α) ⟶ B.A, x ^ n = 1 ∧ extPt α κ hβ ≫ x = y := by
  haveI : CharZero Ω := κ.charZero
  have h := (GlobalTheory.firstFiveLaws.1.mulN (Sp R) B n hn).2.2.2.2
  have h1 := h Ω (spMap α) (Nat.cast_ne_zero.2 (by omega))
  have h2 := h C (spMap β) (Nat.cast_ne_zero.2 (by omega))
  haveI : Finite {x : Over.mk (spMap β) ⟶ B.A // x ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  let F : {x : Over.mk (spMap α) ⟶ B.A // x ^ n = 1} → {x : Over.mk (spMap β) ⟶ B.A // x ^ n = 1} := fun x =>
    ⟨extPt α κ hβ ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hF : Function.Injective F := fun x y e => Subtype.ext (extPt_injective α κ hβ _ (congrArg Subtype.val e))
  obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (h2.trans h1.symm).le).2 ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end Algebraic

theorem lamEq_polPull {S S' : Scheme.{0}} (s : S' ⟶ S) {X Y A B : Out.PolAV S} {f₁ : X.A ⟶ A.A} {f₂ : Y.A ⟶ A.A}
    {g₁ : X.A ⟶ B.A} {g₂ : Y.A ⟶ B.A} (h : LamEq A.L f₁ f₂ B.L g₁ g₂) :
    LamEq (X := (StrictPull.polPull X s).A) (Y := (StrictPull.polPull Y s).A) (StrictPull.polPull A s).L
      ((Over.pullback s).map f₁) ((Over.pullback s).map f₂)
      (StrictPull.polPull B s).L ((Over.pullback s).map g₁) ((Over.pullback s).map g₂) :=
  lamEq_baseChange _ _ s X.A Y.A A.A B.A _ _ (StrictPull.polPull A s).A (StrictPull.polPull B s).A
    (pullback.fst X.A.hom s) (pullback.fst Y.A.hom s) _ _ pullback.condition pullback.condition
    (isGrpPullback_pullback A.A s) (isGrpPullback_pullback B.A s) _ _ _ _ A.isLB B.isLB (StrictPull.polPull A s).isLB
    (StrictPull.polPull B s).isLB (PolBaseChange.lbIso_refl (StrictPull.polPull A s).isLB)
    (PolBaseChange.lbIso_refl (StrictPull.polPull B s).isLB) _ _ _ _ _ _ _ _ (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) h

theorem exists_pushEquiv₂ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h' : IsGrpPullback G'' G' f' φ') (h : IsGrpPullback G' G f φ) (g : S'' ⟶ S) (hg : g = f' ≫ f) :
    ∃ e : ((Over.mk (𝟙 S'') : Over S'') ⟶ G'') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ' ≫ φ := by
  obtain ⟨e₁, h₁⟩ := LiePull.exists_pushEquiv h' (Over.mk (𝟙 _)) f' (Category.id_comp _).symm
  obtain ⟨e₂, h₂⟩ := LiePull.exists_pushEquiv h (Over.mk f') g hg
  exact ⟨e₁.trans e₂, fun x => (h₂ _).trans ((congrArg (· ≫ _) (h₁ x)).trans (Category.assoc _ _ _))⟩

theorem exists_pushEquiv_polPull {S S' S'' : Scheme.{0}} (B : Out.PolAV S) (f : S' ⟶ S) (f' : S'' ⟶ S') (g : S'' ⟶ S)
    (hg : g = f' ≫ f) :
    ∃ e : ((Over.mk (𝟙 S'') : Over S'') ⟶ (StrictPull.polPull (StrictPull.polPull B f) f').A) ≃* (Over.mk g ⟶ B.A),
      ∀ x, (e x).left = x.left ≫ pullback.fst (StrictPull.polPull B f).A.hom f' ≫ pullback.fst B.A.hom f :=
  exists_pushEquiv₂ (G' := (StrictPull.polPull B f).A) (isGrpPullback_pullback (StrictPull.polPull B f).A f')
    (isGrpPullback_pullback B.A f) g hg

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

def toBase : (goodPoint hv ε j B o).A.A.left ⟶ B.A.left :=
  (goodPoint hv ε j B o).gen ≫ pullback.fst B.A.hom (spMap j)

theorem homC_toBase (f : B.A ⟶ B'.A) :
    (homC hv ε j o o' f).left ≫ toBase hv ε j o' = toBase hv ε j o ≫ f.left := by
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  have h3 : (homO hv ε j o o' f).left ≫ pullback.fst B'.A.hom (spMap j) = pullback.fst B.A.hom (spMap j) ≫ f.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h3).trans (Category.assoc _ _ _).symm)))

theorem exists_ptsEquiv : ∃ e : ChTor.Pts (goodPoint hv ε j B o).A.A ≃*
    (Over.mk (spMap ((algebraMap O C).comp j)) ⟶ B.A), ∀ x, (e x).left = x.left ≫ toBase hv ε j o :=
  exists_pushEquiv_polPull B (spMap j) (spMap (algebraMap O C)) _ (Spec.map_comp (CommRingCat.ofHom j) _)

def ptsEquiv : ChTor.Pts (goodPoint hv ε j B o).A.A ≃* (Over.mk (spMap ((algebraMap O C).comp j)) ⟶ B.A) :=
  (exists_ptsEquiv hv ε j o).choose

theorem ptsEquiv_left (x : ChTor.Pts (goodPoint hv ε j B o).A.A) :
    (ptsEquiv hv ε j o x).left = x.left ≫ toBase hv ε j o := (exists_ptsEquiv hv ε j o).choose_spec x

theorem ptsEquiv_homC (f : B.A ⟶ B'.A) (x : ChTor.Pts (goodPoint hv ε j B o).A.A) :
    ptsEquiv hv ε j o' (x ≫ homC hv ε j o o' f) = ptsEquiv hv ε j o x ≫ f :=
  Over.OverMorphism.ext (by
    rw [ptsEquiv_left, Over.comp_left, Over.comp_left, ptsEquiv_left, Category.assoc, homC_toBase, Category.assoc])

variable [IsAlgClosed C] [CharZero C]

theorem exists_tateEquiv [IsNoetherianRing R] {Ω : Type} [Field Ω] [IsAlgClosed Ω] (α : R →+* Ω) (κ : Ω →+* C)
    (h : κ.comp α = (algebraMap O C).comp j) :
    ∃ e : ∀ (B : Out.PolAV (Sp R)) (o : B.OAct Λ), Tate p (Over.mk (spMap α) ⟶ B.A) ≃ₗ[ℤ_[p]] (goodPoint hv ε j B o).T,
      ∀ (B B' : Out.PolAV (Sp R)) (o : B.OAct Λ) (o' : B'.OAct Λ) (f : B.A ⟶ B'.A) [IsMonHom f] (t),
        e B' o' (Tate.map p (IndepPoint.ptsHom f _) t) = homT hv ε j o o' f (e B o t) := by
  let F := fun (B : Out.PolAV (Sp R)) (o : B.OAct Λ) =>
    (ptsEquiv hv ε j o).symm.toMonoidHom.comp (preHom (G := B.A) (extPt α κ h))
  have hF : ∀ B o, Function.Bijective (Tate.map p (F B o)) := fun B o =>
    tate_map_bijective ((ptsEquiv hv ε j o).symm.injective.comp (extPt_injective α κ h _)) fun n y hy => by
      obtain ⟨x, -, hx⟩ := exists_extPt_eq α κ h B (one_le_ppow p n) (ptsEquiv hv ε j o y)
        (by rw [← map_pow, hy, map_one])
      exact ⟨x, (ptsEquiv hv ε j o).symm_apply_eq.2 hx⟩
  refine ⟨fun B o => LinearEquiv.ofBijective _ (hF B o), fun B B' o o' f _ t => Tate.ext fun n => ?_⟩
  refine (ptsEquiv hv ε j o').symm_apply_eq.2 ?_
  rw [lev_homT, ptsEquiv_homC]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) ((ptsEquiv hv ε j o).apply_symm_apply _).symm)

theorem pairT_homT_of_lamEq {X Y A B : Out.PolAV (Sp R)} (oX : X.OAct Λ) (oY : Y.OAct Λ) (oA : A.OAct Λ)
    (oB : B.OAct Λ) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) [IsMonHom f₁] [IsMonHom f₂]
    [IsMonHom g₁] [IsMonHom g₂] (h : LamEq A.L f₁ f₂ B.L g₁ g₂) (s : (goodPoint hv ε j X oX).T)
    (t : (goodPoint hv ε j Y oY).T) :
    pairT (goodPoint hv ε j A oA).A ε (homT hv ε j oX oA f₁ s) (homT hv ε j oY oA f₂ t) =
      pairT (goodPoint hv ε j B oB).A ε (homT hv ε j oX oB g₁ s) (homT hv ε j oY oB g₂ t) := by
  have hW := weilEq_of_lamEq GlobalTheory.firstFiveLaws.1 C (goodPoint hv ε j X oX).A (goodPoint hv ε j Y oY).A
    (goodPoint hv ε j A oA).A (goodPoint hv ε j B oB).A (homC hv ε j oX oA f₁) (homC hv ε j oY oA f₂)
    (homC hv ε j oX oB g₁) (homC hv ε j oY oB g₂) inferInstance inferInstance inferInstance inferInstance
    (lamEq_polPull _ (lamEq_polPull _ h))
  refine congrArg ε.equiv.symm (Tate.ext fun n => ?_)
  have hn := one_le_ppow p n
  exact (weilIs_iff hn ((homT hv ε j oX oB g₁ s).lev_pow n) ((homT hv ε j oY oB g₂ t).lev_pow n) _).1
    ((hW _ _ _ _ hn (s.lev_pow n) (t.lev_pow n)).1
      ((weilIs_iff hn ((homT hv ε j oX oA f₁ s).lev_pow n) ((homT hv ε j oY oA f₂ t).lev_pow n) _).2 rfl))

omit [IsAlgClosed C] [CharZero C] in
theorem homT_one [IsMonHom (1 : B.A ⟶ B'.A)] : homT hv ε j o o' 1 = 0 :=
  LinearMap.ext fun t => Tate.ext fun n => (ptsEquiv hv ε j o').injective (by
    rw [lev_homT, ptsEquiv_homC, MonObj.comp_one, LinearMap.zero_apply, Tate.lev_zero, map_one])

omit [IsAlgClosed C] [CharZero C] in

theorem ptsEquiv_lev_sum {A A' : Out.PolAV (Sp R)} (oA : A.OAct Λ) (oA' : A'.OAct Λ) {m m' : ℕ}
    (φ : Fin m → (A.A ⟶ B.A)) (φ' : Fin m' → (A'.A ⟶ B.A)) [∀ k, IsMonHom (φ k)] [∀ k, IsMonHom (φ' k)]
    (s : Fin m → (goodPoint hv ε j A oA).T) (s' : Fin m' → (goodPoint hv ε j A' oA').T) (n : ℕ) :
    ptsEquiv hv ε j o ((∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)).lev n) =
      (∏ k, ptsEquiv hv ε j oA ((s k).lev n) ≫ φ k) * ∏ k, ptsEquiv hv ε j oA' ((s' k).lev n) ≫ φ' k := by
  simp only [Tate.lev_add, lev_sum, map_mul, map_prod, lev_homT, ptsEquiv_homC]

omit [IsAlgClosed C] [CharZero C] in

theorem homT_inverse {A A' : Out.PolAV (Sp R)} (oA : A.OAct Λ) (oA' : A'.OAct Λ) {m m' N : ℕ}
    (φ : Fin m → (A.A ⟶ B.A)) (φ' : Fin m' → (A'.A ⟶ B.A)) [∀ k, IsMonHom (φ k)] [∀ k, IsMonHom (φ' k)]
    (ψ : Fin m → (B.A ⟶ A.A)) (ψ' : Fin m' → (B.A ⟶ A'.A)) [∀ k, IsMonHom (ψ k)] [∀ k, IsMonHom (ψ' k)]
    (h1 : ∀ (T : Over (Sp R)) (x : T ⟶ B.A), (∏ k, x ≫ ψ k ≫ φ k) * (∏ k, x ≫ ψ' k ≫ φ' k) = x ^ N)
    (h2 : ∀ (T : Over (Sp R)) (a : Fin m → (T ⟶ A.A)) (a' : Fin m' → (T ⟶ A'.A)),
      (∀ l, ((∏ k, a k ≫ φ k) * ∏ k, a' k ≫ φ' k) ≫ ψ l = a l ^ N) ∧
      ∀ l, ((∏ k, a k ≫ φ k) * ∏ k, a' k ≫ φ' k) ≫ ψ' l = a' l ^ N) :
    (∀ t, ∑ k, homT hv ε j oA o (φ k) (homT hv ε j o oA (ψ k) t) +
      ∑ k, homT hv ε j oA' o (φ' k) (homT hv ε j o oA' (ψ' k) t) = N • t) ∧
    ∀ (s : Fin m → (goodPoint hv ε j A oA).T) (s' : Fin m' → (goodPoint hv ε j A' oA').T),
      (∀ l, homT hv ε j o oA (ψ l) (∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)) =
        N • s l) ∧
      ∀ l, homT hv ε j o oA' (ψ' l) (∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)) =
        N • s' l := by
  refine ⟨fun t => Tate.ext fun n => (ptsEquiv hv ε j o).injective ?_, fun s s' =>
    ⟨fun l => Tate.ext fun n => (ptsEquiv hv ε j oA).injective ?_,
      fun l => Tate.ext fun n => (ptsEquiv hv ε j oA').injective ?_⟩⟩
  · rw [ptsEquiv_lev_sum, lev_nsmul, map_pow, ← h1]
    simp only [lev_homT, ptsEquiv_homC, Category.assoc]
  · rw [lev_homT, ptsEquiv_homC, lev_nsmul, map_pow, ptsEquiv_lev_sum, (h2 _ _ _).1]
  · rw [lev_homT, ptsEquiv_homC, lev_nsmul, map_pow, ptsEquiv_lev_sum, (h2 _ _ _).2]

end Good

section Points

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [IsAlgClosed C] [CharZero C]

theorem pairV_baseChange [Algebra ℤ_[p] C] {X Y A B : Point p v O Λ} {f₁ : X.T →ₗ[ℤ_[p]] A.T} {f₂ : Y.T →ₗ[ℤ_[p]] A.T}
    {g₁ : X.T →ₗ[ℤ_[p]] B.T} {g₂ : Y.T →ₗ[ℤ_[p]] B.T}
    (h : ∀ s t, pairT A.A A.eps (f₁ s) (f₂ t) = pairT B.A B.eps (g₁ s) (g₂ t)) (x : X.V) (y : Y.V) :
    A.pairV (f₁.baseChange C x) (f₂.baseChange C y) = B.pairV (g₁.baseChange C x) (g₂.baseChange C y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (h s t)

theorem eq_zero_of_actT {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (hg : 0 < P.A.g)
    {a : 𝓞 E} (h : ∀ t, P.actT a t = 0) : a = 0 := by
  by_contra ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  haveI : Nontrivial P.T := Module.nontrivial_of_finrank_pos (R := ℤ_[p]) (by rw [P.hodgeTateLatticePoint_finrank_tateModule]; omega)
  obtain ⟨t, ht⟩ := exists_ne (0 : P.T)
  have e := congrArg (P.actT b) (h t)
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, hb, map_natCast, Module.End.natCast_apply,
    ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_eq_zero] at e
  exact ht (e.resolve_left (Nat.cast_ne_zero.2 hn))

variable {A A' B : Point p v O Λ} {m m' : ℕ} (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (φ' : Fin m' → (A'.T →ₗ[ℤ_[p]] B.T))
  {N : ℕ} (hN : 0 < N) (ψ : Fin m → (B.T →ₗ[ℤ_[p]] A.T)) (ψ' : Fin m' → (B.T →ₗ[ℤ_[p]] A'.T))

omit [IsAlgClosed C] in
include hN in

theorem bijective_of_inverse [Algebra ℤ_[p] C] (h1 : ∀ t, ∑ k, φ k (ψ k t) + ∑ k, φ' k (ψ' k t) = N • t)
    (h2 : ∀ (s : Fin m → A.T) (s' : Fin m' → A'.T), (∀ l, ψ l (∑ k, φ k (s k) + ∑ k, φ' k (s' k)) = N • s l) ∧
      ∀ l, ψ' l (∑ k, φ k (s k) + ∑ k, φ' k (s' k)) = N • s' l) :
    Function.Bijective fun z : (Fin m → A.V) × (Fin m' → A'.V) =>
      ∑ k, (φ k).baseChange C (z.1 k) + ∑ k, (φ' k).baseChange C (z.2 k) := by
  classical
  have hC : (N : C) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have a1 : ∀ l k x, (ψ l).baseChange C ((φ k).baseChange C x) = if k = l then (N : C) • x else 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; split_ifs <;> simp
    | tmul c t =>
      have := (h2 (Pi.single k t) 0).1 l
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, Nat.cast_smul_eq_nsmul]
      split_ifs with h
      · rw [h, Pi.single_eq_same, TensorProduct.tmul_smul]
      · simp [Ne.symm h]
  have a2 : ∀ l k x, (ψ l).baseChange C ((φ' k).baseChange C x) = 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul c t =>
      have := (h2 0 (Pi.single k t)).1 l
      rw [Finset.sum_eq_single k (f := fun b => φ' b _) (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add, smul_zero] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, TensorProduct.tmul_zero]
  have a3 : ∀ l k x, (ψ' l).baseChange C ((φ k).baseChange C x) = 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul c t =>
      have := (h2 (Pi.single k t) 0).2 l
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero, smul_zero] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, TensorProduct.tmul_zero]
  have a4 : ∀ l k x, (ψ' l).baseChange C ((φ' k).baseChange C x) = if k = l then (N : C) • x else 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; split_ifs <;> simp
    | tmul c t =>
      have := (h2 0 (Pi.single k t)).2 l
      rw [Finset.sum_eq_single k (f := fun b => φ' b _) (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, Nat.cast_smul_eq_nsmul]
      split_ifs with h
      · rw [h, Pi.single_eq_same, TensorProduct.tmul_smul]
      · simp [Ne.symm h]
  have a5 : ∀ x : B.V, ∑ k, (φ k).baseChange C ((ψ k).baseChange C x) +
      ∑ k, (φ' k).baseChange C ((ψ' k).baseChange C x) = (N : C) • x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, smul_add, ← hx, ← hy]; abel
    | tmul c t =>
      simp only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_add, h1]
      rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul]
  refine ⟨fun z z' h => Prod.ext (funext fun l => ?_) (funext fun l => ?_), fun x => ?_⟩
  · have := congrArg ((ψ l).baseChange C) h
    simp only [map_add, map_sum, a1, a2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact smul_right_injective _ hC (add_right_cancel this)
  · have := congrArg ((ψ' l).baseChange C) h
    simp only [map_add, map_sum, a3, a4, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact smul_right_injective _ hC (add_left_cancel this)
  · refine ⟨(fun k => (ψ k).baseChange C ((N : C)⁻¹ • x), fun k => (ψ' k).baseChange C ((N : C)⁻¹ • x)), ?_⟩
    exact (a5 _).trans (smul_inv_smul₀ hC x)

include hN in

theorem det_ne_zero_of_inverse {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {A A' B : Point p v O (𝓞 E)}
    (hg : 0 < A.A.g) (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (φ' : Fin m' → (A'.T →ₗ[ℤ_[p]] B.T))
    (g : Matrix (Fin m) (Fin m) (𝓞 E))
    (hφ : ∀ a b s t, pairT B.A B.eps (φ a s) (φ b t) = pairT A.A A.eps (A.actT (g a b) s) t)
    (hφ' : ∀ a b s t, pairT B.A B.eps (φ a s) (φ' b t) = 0)
    (h1 : ∀ t, ∃ (s : Fin m → A.T) (s' : Fin m' → A'.T), ∑ k, φ k (s k) + ∑ k, φ' k (s' k) = N • t)
    (h2 : ∀ s : Fin m → A.T, ∑ k, φ k (s k) = 0 → s = 0) : g.det ≠ 0 := fun h0 => by
  obtain ⟨w, hw, hwg⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine hw (funext fun a => eq_zero_of_actT A hg fun t => congrFun (h2 (fun k => A.actT (w k) t) ?_) a)
  refine (injective_iff_map_eq_zero _).1 B.pairT_bijective.1 _ (LinearMap.ext fun y => ?_)
  obtain ⟨s, s', hs⟩ := h1 y
  refine (smul_eq_zero_iff_right hN.ne').1 ?_
  rw [← map_nsmul, ← hs]
  simp only [map_add, map_sum, LinearMap.sum_apply, hφ, hφ', Finset.sum_const_zero, add_zero]
  refine Finset.sum_eq_zero fun b _ => ?_
  have e : ∑ k, g k b * w k = 0 := by simpa [Matrix.vecMul, dotProduct, mul_comm] using congrFun hwg b
  simp only [← Module.End.mul_apply, ← map_mul]
  rw [← LinearMap.sum_apply, ← map_sum, ← LinearMap.sum_apply, ← map_sum, e]
  simp

theorem star_gram {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {A B : Point p v O (𝓞 E)}
    (hg : 0 < A.A.g) (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (g : Matrix (Fin m) (Fin m) (𝓞 E))
    (hφ : ∀ a b s t, pairT B.A B.eps (φ a s) (φ b t) = pairT A.A A.eps (A.actT (g a b) s) t) (a b : Fin m) :
    star (g b a) = g a b := by
  refine sub_eq_zero.1 (eq_zero_of_actT A hg fun s => ?_)
  refine (injective_iff_map_eq_zero _).1 A.pairT_bijective.1 _ (LinearMap.ext fun t => ?_)
  have e : pairT A.A A.eps (A.actT (star (g b a)) s) t = pairT A.A A.eps s (A.actT (star (star (g b a))) t) :=
    pairT_act A.oA A.eps _ s t
  rw [map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, ← hφ, e, star_star,
    ← (isAlt_pairT A.A A.eps).neg_eq, ← hφ, (isAlt_pairT B.A B.eps).neg_eq, sub_self, LinearMap.zero_apply]

end Points

end GlobalTheory.GramAt
