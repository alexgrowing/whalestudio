import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubringStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published
  GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NoethLiftObj

section Linear

open Module

variable {S R S₀ R₀ : Type} [CommRing S] [CommRing R] [CommRing S₀] [CommRing R₀]
  {P P' P₀ P₀' : Type*} [AddCommGroup P] [Module S P] [AddCommGroup P'] [Module R P']
  [AddCommGroup P₀] [Module S₀ P₀] [AddCommGroup P₀'] [Module R₀ P₀']

theorem exists_frame [Module.Finite S P] [Module.Projective S P] :
    ∃ (n : ℕ) (p : Fin n → P) (l : Fin n → Dual S P), ∀ c, ∑ i, l i c • p i = c := by
  obtain ⟨n, f, g, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective S P
  refine ⟨n, fun i ↦ f (Pi.single i 1), fun i ↦ LinearMap.proj i ∘ₗ g, fun c ↦ ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := S) c, ← h, LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have : (fun j ↦ if i = j then (1 : S) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [this]
  rfl

theorem cor_of_span {σ : S →+* R} {Λ : Type*} {v : Λ → P} (hv : Submodule.span S (Set.range v) = ⊤)
    (f : P →ₛₗ[σ] P') {x : Dual S P} {x' : Dual R P'} (h : ∀ c, x' (f (v c)) = σ (x (v c))) (c : P) :
    x' (f c) = σ (x c) := by
  have hc : c ∈ Submodule.span S (Set.range v) := hv ▸ Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem _ hc => obtain ⟨c, rfl⟩ := hc; exact h c
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [LinearMap.map_smulₛₗ, ha]

theorem frame_bc {σ : S →+* R} {n : ℕ} {p : Fin n → P} {l : Fin n → Dual S P}
    (hp : ∀ c, ∑ i, l i c • p i = c) (f : P →ₛₗ[σ] P') (hf : Submodule.span R (Set.range f) = ⊤)
    {l' : Fin n → Dual R P'} (hl : ∀ i c, l' i (f c) = σ (l i c)) (c : P') :
    ∑ i, l' i c • f (p i) = c := by
  have hc : c ∈ Submodule.span R (Set.range f) := hf ▸ Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem _ hc =>
    obtain ⟨c, rfl⟩ := hc
    conv_rhs => rw [← hp c, map_sum]
    simp [hl, LinearMap.map_smulₛₗ]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, add_smul, Finset.sum_add_distrib, ha, hb]
  | smul r a _ ha => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ha]

theorem dual_frame {n : ℕ} {p : Fin n → P} {l : Fin n → Dual S P}
    (hp : ∀ c, ∑ i, l i c • p i = c) (x : Dual S P) : ∑ i, x (p i) • l i = x := by
  ext c
  conv_rhs => rw [← hp c, map_sum]
  simp [mul_comm]

theorem exists_descent {τ : S →+* S₀} {σ₁ : S₀ →+* R} {σ : S →+* R} (hσ : ∀ a, σ₁ (τ a) = σ a)
    {n : ℕ} {p : Fin n → P} {l : Fin n → Dual S P} (hp : ∀ c, ∑ i, l i c • p i = c)
    (f : P →ₛₗ[σ] P') (hf : Submodule.span R (Set.range f) = ⊤)
    {l' : Fin n → Dual R P'} (hl : ∀ i c, l' i (f c) = σ (l i c))
    (e : Dual R P' →ₗ[R] Dual R P') (b : Fin n → Fin n → S₀) (hb : ∀ i j, σ₁ (b i j) = e (l' i) (f (p j)))
    (f₀ : P →ₛₗ[τ] P₀) (h₀ : Submodule.span S₀ (Set.range f₀) = ⊤)
    (h₀' : ∀ x : Dual S P, ∃ x' : Dual S₀ P₀, ∀ c, x' (f₀ c) = τ (x c))
    (f₁ : P₀ →ₛₗ[σ₁] P') (hc : ∀ c, f₁ (f₀ c) = f c) :
    ∃ e₁ : Dual S₀ P₀ →ₗ[S₀] Dual S₀ P₀, ∀ (x : Dual S₀ P₀) (x' : Dual R P'),
      (∀ c, x' (f₁ c) = σ₁ (x c)) → ∀ c, e x' (f₁ c) = σ₁ (e₁ x c) := by
  choose l₁ hl₁ using fun i ↦ h₀' (l i)
  have k : ∀ i c, l' i (f₁ c) = σ₁ (l₁ i c) := fun i ↦
    cor_of_span h₀ f₁ fun c ↦ by rw [hc, hl, hl₁, hσ]
  have fr := frame_bc hp f hf hl
  refine ⟨∑ i, (LinearMap.applyₗ (f₀ (p i))).smulRight (∑ j, b i j • l₁ j), fun x x' hx c ↦ ?_⟩
  conv_lhs => rw [← dual_frame fr x', ← fr (f₁ c)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.applyₗ_apply_apply, smul_eq_mul, map_mul, hb, k, ← hx, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

theorem red_descent [Module.Projective S P] [Module.Finite R P'] [Module.Projective R P']
    {σ : S →+* R} {π₁ : S →+* S₀} {π : R →+* R₀} {ρ : S₀ →+* R₀} (hρ : Function.Injective ρ)
    (hπ₁ : Function.Surjective π₁) (hsq : ∀ a, ρ (π₁ a) = π (σ a))
    (f : P →ₛₗ[σ] P') (r₁ : P →ₛₗ[π₁] P₀) (r : P' →ₛₗ[π] P₀') (f₀ : P₀ →ₛₗ[ρ] P₀')
    (hc : ∀ c, r (f c) = f₀ (r₁ c))
    (hf : Submodule.span R (Set.range f) = ⊤) (hr₁ : Submodule.span S₀ (Set.range r₁) = ⊤)
    (ef : ∀ x : Dual S P, ∃ x' : Dual R P', ∀ c, x' (f c) = σ (x c))
    (er : ∀ x : Dual R P', ∃ x' : Dual R₀ P₀', ∀ c, x' (r c) = π (x c))
    (ef₀ : ∀ x : Dual S₀ P₀, ∃ x' : Dual R₀ P₀', ∀ c, x' (f₀ c) = ρ (x c))
    (e : Dual R P' →ₗ[R] Dual R P') (he : ∀ x, e (e x) = e x) (e₁ : Dual S P →ₗ[S] Dual S P)
    (hee : ∀ (x : Dual S P) (x' : Dual R P'), (∀ c, x' (f c) = σ (x c)) → ∀ c, e x' (f c) = σ (e₁ x c))
    (W₀ : Submodule S₀ P₀) (W : Submodule R₀ P₀') (hW : W = Submodule.span R₀ (f₀ '' W₀))
    (H : ∀ y, y ∈ W.dualAnnihilator ↔ ∃ x ∈ LinearMap.range e, ∀ c, y (r c) = π (x c)) (y : Dual S₀ P₀) :
    y ∈ W₀.dualAnnihilator ↔ ∃ x ∈ LinearMap.range e₁, ∀ c, y (r₁ c) = π₁ (x c) := by
  constructor
  · intro hy
    obtain ⟨y', hy'⟩ := ef₀ y
    have m : y' ∈ W.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator, hW]
      intro c hc
      refine (Submodule.span_le (p := LinearMap.ker y')).2 (fun c hc ↦ ?_) hc
      obtain ⟨c, hc, rfl⟩ := hc
      exact (hy' c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hy c hc, map_zero])
    obtain ⟨_, ⟨w, rfl⟩, hx'⟩ := (H y').1 m
    letI : Algebra S S₀ := π₁.toAlgebra
    let t : P →ₗ[S] S₀ :=
      { toFun c := y (r₁ c)
        map_add' := by simp
        map_smul' a c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap S S₀) t hπ₁
    have hx : ∀ c, π₁ (x c) = y (r₁ c) := fun c ↦ LinearMap.congr_fun hx c
    obtain ⟨x', hxx⟩ := ef x
    have k : ∀ c, y' (r c) = π (x' c) := cor_of_span hf r fun c ↦ by rw [hc, hy', ← hx, hsq, hxx]
    obtain ⟨n, p, l, hp⟩ := exists_frame (S := R) (P := P')
    have z : ∀ c, π (e (x' - e w) c) = 0 := fun c ↦ by
      rw [← dual_frame hp (x' - e w)]
      simp [← k, ← hx']
    refine ⟨_, ⟨x, rfl⟩, fun c ↦ hρ ?_⟩
    have := z (f c)
    rw [map_sub, he, LinearMap.sub_apply, map_sub, sub_eq_zero] at this
    rw [hsq, ← hee x x' hxx, this, ← hx', hc, hy']
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    obtain ⟨x', hxx⟩ := ef x
    obtain ⟨y', hy'⟩ := er (e x')
    have m := (H y').2 ⟨_, ⟨x', rfl⟩, hy'⟩
    have k : ∀ c, y' (f₀ c) = ρ (y c) := cor_of_span hr₁ f₀ fun c ↦ by
      rw [← hc, hy', hee x x' hxx, hx, hsq]
    refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hρ ?_
    rw [← k, map_zero]
    exact (Submodule.mem_dualAnnihilator _).1 m _ (hW ▸ Submodule.subset_span ⟨c, hc, rfl⟩)

theorem ann_bc {Q Q' : Type*} [AddCommGroup Q] [Module S Q] [AddCommGroup Q'] [Module R Q']
    [Module.Finite S P] [Module.Projective S P] {σ : S →+* R} (θ : Q ≃ₗ[S] P)
    (f : P →ₛₗ[σ] P') (g : Q →ₛₗ[σ] Q') (hf : Submodule.span R (Set.range f) = ⊤)
    (ef : ∀ x : Dual S P, ∃ x' : Dual R P', ∀ c, x' (f c) = σ (x c))
    (e : Dual R P' →ₗ[R] Dual R P') (e₁ : Dual S P →ₗ[S] Dual S P)
    (hee : ∀ (x : Dual S P) (x' : Dual R P'), (∀ c, x' (f c) = σ (x c)) → ∀ c, e x' (f c) = σ (e₁ x c))
    (W N : Submodule S Q) (hN : IsCompl W N) (W' : Submodule R Q') (hW : W' = Submodule.span R (g '' W))
    (H : ∀ x : Dual S P, x ∈ LinearMap.range e₁ ↔ ∀ c ∈ W, x (θ c) = 0)
    (u : Dual R Q') (v : Dual R P') (huv : ∀ c, u (g c) = v (f (θ c))) :
    u ∈ W'.dualAnnihilator ↔ v ∈ LinearMap.range e := by
  obtain ⟨n, p, l, hp⟩ := exists_frame (S := S) (P := P)
  constructor
  · intro hu
    let q : P →ₗ[S] P := θ.toLinearMap ∘ₗ Submodule.projection _ _ hN.symm ∘ₗ θ.symm.toLinearMap
    have m : ∀ i, l i ∘ₗ q ∈ LinearMap.range e₁ := fun i ↦ (H _).2 fun c hc ↦ by
      simp [q, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc]
    choose a ha using m
    choose a' ha' using fun i ↦ ef (a i)
    refine ⟨∑ i, v (f (p i)) • a' i, LinearMap.ext_on_range hf fun c ↦ ?_⟩
    obtain ⟨c, rfl⟩ := θ.surjective c
    have z : v (f (θ (Submodule.projection _ _ hN c))) = 0 := by
      rw [← huv]
      exact (Submodule.mem_dualAnnihilator _).1 hu _
        (hW ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    have : v (f (θ c)) = v (f (q (θ c))) := by
      conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add, map_add, map_add, z,
        zero_add]
      simp [q]
    rw [this, ← hp (q (θ c))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hee _ _ (ha' _), ha,
      LinearMap.map_smulₛₗ, smul_eq_mul, LinearMap.comp_apply, mul_comm]
  · rintro ⟨w, rfl⟩
    choose l' hl using fun i ↦ ef (l i)
    rw [Submodule.mem_dualAnnihilator, hW]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker u)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    change u (g c) = 0
    rw [huv, ← dual_frame (frame_bc hp f hf hl) w]
    simp [hee _ _ (hl _), (H _).1 ⟨_, rfl⟩ c hc]

end Linear

open scoped CategoryTheory.Obj in

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    {f : S' ⟶ S} {k : S'' ⟶ S'} {t : S'' ⟶ S} {φ : G''.left ⟶ G.left} (h : IsGrpPullback G'' G t φ)
    (e : k ≫ f = t) {g : ℕ} (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) :
    ∃ (G' : Over S') (_ : GrpObj G') (ψ : G'.left ⟶ G.left) (χ : G''.left ⟶ G'.left),
      IsGrpPullback G' G f ψ ∧ IsGrpPullback G'' G' k χ ∧ χ ≫ ψ = φ ∧ IsAbelianScheme G' ∧
        SmoothOfRelativeDimension g G'.hom := by
  subst e
  have p := isGrpPullback_pullback G f
  have e₁ := p.1.lift_fst φ (G''.hom ≫ k) (by rw [h.1.w, Category.assoc])
  exact ⟨_, inferInstance, _, _, p, p.cancel (by rw [e₁]; exact h) (p.1.lift_snd _ _ _), e₁,
    PolPull.isAbelianScheme_of_isGrpPullback hG p,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback p.1 hg⟩

theorem bc_facts (P : AbelianDeRham) {S R : Type} [CommRing S] [CommRing R] {σ : S →+* R} {g : ℕ}
    {B : Over (Sp S)} [GrpObj B] {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (spMap σ) φ) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom) :
    Submodule.span R (Set.range (redMor h).pull) = ⊤ ∧
      (∀ x : HdR B, ∃ x' : HdR A, ∀ c, x' ((redMor h).pull c) = σ (x c)) ∧
      PrimitiveSubmodule A = Submodule.span R ((redMor h).pull '' (PrimitiveSubmodule B)) := by
  letI : Algebra S R := σ.toAlgebra
  obtain ⟨h₁, h₂⟩ := P.2.2.1 S B g hB hg R A φ h
  refine ⟨top_le_iff.1 fun c _ ↦ ?_, h₁.exists, h₂⟩
  obtain ⟨z, rfl⟩ := h₁.2 c
  induction z with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem exists_noeth_model (P : AbelianDeRham) {R : Type} [CommRing R] {g : ℕ} (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (e : HdR A →ₗ[R] HdR A) :
    ∃ (S : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (σ : S →+* R) (B : Over (Sp S)) (_ : GrpObj B)
      (φ : A.left ⟶ B.left) (h : IsGrpPullback A B (spMap σ) φ) (e₁ : HdR B →ₗ[S] HdR B),
      Function.Injective σ ∧ IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧
      ∀ (x : HdR B) (x' : HdR A), (∀ c, x' ((redMor h).pull c) = σ (x c)) →
        ∀ c, e x' ((redMor h).pull c) = σ (e₁ x c) := by
  obtain ⟨S, B, _, φ, -, hS, hB, hgB, h⟩ := GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring R g A ∅ hA hg
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  obtain ⟨hf, hp, -⟩ := P.1.prim hB hgB
  obtain ⟨n, p, l, hpl⟩ := exists_frame (S := S) (P := primDR B)
  obtain ⟨b₁, b₂, -⟩ := bc_facts P h hB hgB
  choose l' hl using fun i ↦ b₂ (l i)
  let a : Fin n × Fin n → R := fun ij ↦ e (l' ij.1) ((redMor h).pull (p ij.2))
  let T := Algebra.adjoin S (Set.range a)
  haveI : Algebra.FiniteType S T := Algebra.FiniteType.adjoin_of_finite (Set.finite_range a)
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  obtain ⟨C, _, ψ, χ, h₀, h₁, hc, hC, hgC⟩ := exists_factor (f := spMap (algebraMap S T))
    (k := spMap T.val.toRingHom) h (Cris.spMap_comp _ _).symm hB hgB
  obtain ⟨c₁, c₂, -⟩ := bc_facts P h₀ hB hgB
  obtain ⟨e₁, he₁⟩ := exists_descent (τ := algebraMap S T) (σ₁ := T.val.toRingHom) (fun _ ↦ rfl) hpl _ b₁ hl e
    (fun i j ↦ ⟨a (i, j), Algebra.subset_adjoin ⟨_, rfl⟩⟩) (fun _ _ ↦ rfl) _ c₁ c₂ (redMor h₁).pull
    (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) hc)
  exact ⟨T, inferInstance, inferInstance, _, C, inferInstance, χ, h₁, e₁, Subtype.val_injective, hC, hgC, he₁⟩

theorem liftObj_of_noetherian (P : AbelianDeRham)
    (H : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π)
    (R : Type) [CommRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) : LiftObj (divided₂ hI) π := by
  intro g A₀ _ A' _ i' h' hA hg F ⟨⟨N, hN⟩, hF⟩
  obtain ⟨e, he, rfl⟩ : ∃ e : HdR A' →ₗ[R] HdR A', (∀ x, e (e x) = e x) ∧ F = LinearMap.range e :=
    ⟨Submodule.projection _ _ hN, fun x ↦ Submodule.projection_apply_left hN
      ⟨_, Submodule.projection_apply_mem hN x⟩, (Submodule.range_projection hN).symm⟩
  obtain ⟨S, _, _, σ, B, _, φ, h, e₁, hσ, hB, hgB, hee⟩ := exists_noeth_model P A' hA hg e
  let J : Ideal S := RingHom.ker (π.comp σ)
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ hk ▸ ha
  have hJ : J ^ 2 = 0 := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have := Ideal.mul_mem_mul (hJI a ha) (hJI b hb)
    rw [← pow_two, hI, Ideal.zero_eq_bot, Ideal.mem_bot, ← map_mul] at this
    exact hσ (this.trans (map_zero σ).symm)
  let π₁ : S →+* S ⧸ J := Ideal.Quotient.mk J
  let ρ : S ⧸ J →+* R₀ := RingHom.kerLift (π.comp σ)
  have hρ : Function.Injective ρ := RingHom.kerLift_injective _
  have hsq : ∀ a, ρ (π₁ a) = π (σ a) := fun _ ↦ rfl
  have sq : spMap ρ ≫ spMap π₁ = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]; rfl
  obtain ⟨B₀, _, j, ψ, k, k₀, hj, hB₀, hgB₀⟩ := exists_factor (h'.comp h) sq hB hgB
  obtain ⟨b₁, b₂, -⟩ := bc_facts P h hB hgB
  obtain ⟨hf, hp, -⟩ := P.1.prim hB hgB
  have adm : IsAdmissible k (LinearMap.range e₁) := by
    obtain ⟨hf', hp', -⟩ := P.1.prim hA hg
    obtain ⟨-, c₂, c₃⟩ := bc_facts P k₀ hB₀ hgB₀
    refine ⟨⟨LinearMap.ker e₁, LinearMap.IsIdempotentElem.isCompl (LinearMap.ext fun x ↦ ?_)⟩,
      red_descent hρ Ideal.Quotient.mk_surjective hsq (redMor h).pull (redMor k).pull (redMor h').pull
        (redMor k₀).pull (fun c ↦ ?_) b₁ (bc_facts P k hB hgB).1 b₂ (bc_facts P h' hA hg).2.1 c₂ e he e₁ hee
        _ _ c₃ hF⟩
    · obtain ⟨x', hx⟩ := b₂ x
      refine LinearMap.ext fun c ↦ hσ ?_
      rw [← hee x x' hx, ← he]
      exact (hee _ _ (hee x x' hx) c).symm
    · exact (GrpMor.pull_pull _ _ ((redMor h).comp (redMor h')) (fun _ ↦ rfl) rfl c).trans
        (GrpMor.pull_pull _ _ _ hsq hj c).symm
  obtain ⟨C, _, l, hl, hC, hgC, hfil⟩ := (H S J hJ (S ⧸ J) π₁ Ideal.Quotient.mk_surjective
    Ideal.mk_ker).1 g B₀ B j k hB hgB _ adm
  obtain ⟨A, _, χ, i, n, hi, hχ, hA₁, hg₁⟩ := exists_factor (k₀.comp hl) sq.symm hC hgC
  refine ⟨A, inferInstance, i, hi, hA₁, hg₁, Submodule.ext fun d ↦ ?_⟩
  let α := LinearEquiv.ofBijective _ (P.2.2.2.1 S C g hC hgC J _ (isDPNilpotent_squareZero hJ) _ π₁
    Ideal.Quotient.mk_surjective Ideal.mk_ker B₀ l hl)
  let β := LinearEquiv.ofBijective _ (P.2.2.2.1 S B g hB hgB J _ (isDPNilpotent_squareZero hJ) _ π₁
    Ideal.Quotient.mk_surjective Ideal.mk_ker B₀ j k)
  have m : GrpMor (divided₂ hJ) (spMap π₁) B₀ (divided₂ hI) (spMap π) A₀ σ (spMap ρ) ψ :=
    GrpMor.of_isGrpPullback (isDPMorphism_sqDP hJ hI σ hJI) sq k₀
  obtain ⟨-, ⟨M, hM⟩, -⟩ := P.2.1 S C g hC hgC
  refine ann_bc (α.trans β.symm) (redMor h).pull (redMor n).pull b₁ b₂ e e₁ hee _ M hM _
    (bc_facts P n hC hgC).2.2 (fun x ↦ ?_) (crysToDR _ hi d) (crysToDR _ h' d) fun c ↦ ?_
  · have := SetLike.ext_iff.1 hfil (x ∘ₗ β.symm.toLinearMap)
    have e₂ : crysToDR (divided₂ hJ) k (x ∘ₗ β.symm.toLinearMap) = x :=
      LinearMap.ext fun c ↦ congrArg x (β.symm_apply_apply c)
    rw [Submodule.mem_comap (f := crysToDR (divided₂ hJ) k), e₂] at this
    exact this.symm.trans (Submodule.mem_dualAnnihilator _)
  · have e₂ : (liftMor (divided₂ hJ) k).pull (β.symm (α c)) = (liftMor (divided₂ hJ) hl).pull c :=
      β.apply_symm_apply _
    refine congrArg d ?_
    exact (GrpMor.pull_pull (redMor n) (liftMor _ hi) ((liftMor (divided₂ hJ) hl).comp m) (fun _ ↦ rfl)
      hχ c).trans ((GrpMor.pull_pull (liftMor (divided₂ hJ) hl) m _ (fun _ ↦ rfl) rfl c).symm.trans
        ((congrArg m.pull e₂.symm).trans ((GrpMor.pull_pull (liftMor (divided₂ hJ) k) m
          ((liftMor (divided₂ hJ) k).comp m) (fun _ ↦ rfl) rfl _).trans
            (GrpMor.pull_pull (redMor h) (liftMor _ h') _ (fun _ ↦ rfl) hj.symm _).symm)))

end GlobalTheory.NoethLiftObj
