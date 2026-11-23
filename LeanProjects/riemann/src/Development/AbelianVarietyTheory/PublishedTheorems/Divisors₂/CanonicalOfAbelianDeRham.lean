import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R}

theorem redMor {π : R →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R₀) (𝟙 _) A₀ π (spMap π) i :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) h

def IsAdmissible {π : R →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) (F : Submodule R (HdR A)) : Prop :=
  (∃ N : Submodule R (HdR A), IsCompl F N) ∧
    ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ x ∈ F, (redMor h).Corr x y

variable (κ : DividedPowers I) (π : R →+* R₀)

def Canonical : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    Function.Bijective (liftMor κ h).pull ∧ IsAdmissible h (Fil A)

def LiftObj : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom →
    ∀ F : Submodule R (HdR A'), IsAdmissible h' F →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left)
        (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A ∧
        SmoothOfRelativeDimension g A.hom ∧ liftFil κ h = F.comap (crysToDR κ h')

def LiftHom : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (k : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k) →
    ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j

def At : Prop := Canonical κ π ∧ LiftObj κ π ∧ LiftHom κ π

end GrothendieckMessing

def GrothendieckMessing : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R], IsNilpotent (p : R) →
    ∀ (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
      GrothendieckMessing.At κ π

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I}
  {π : R →+* R₀} {g g' : ℕ} {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀]
  {A A' B : Over (Sp R)} [GrpObj A] [GrpObj A'] [GrpObj B]
  {i : A₀.left ⟶ A.left} {i' : A₀.left ⟶ A'.left} {j : B₀.left ⟶ B.left}

theorem Canonical.crysToDR_bijective (H : Canonical κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (crysToDR κ h) :=
  (LinearEquiv.ofBijective _ (H g A₀ A i h hA hg).1).dualMap.bijective

theorem LiftHom.exists_iff (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (k : IsGrpPullback B₀ B (spMap π) j) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] :
    (∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j) ↔
      ∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k :=
  ⟨fun ⟨f, _, e⟩ _ hd ↦ push_mem_liftFil κ h k f₀ f e hd,
    fun e ↦ (H g A₀ A i h hA hg g' B₀ B j k hB hg' f₀ e).exists⟩

theorem LiftHom.unique (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (k : IsGrpPullback B₀ B (spMap π) j) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] {f f' : A ⟶ B}
    [IsMonHom f] [IsMonHom f'] (e : i ≫ f.left = f₀.left ≫ j) (e' : i ≫ f'.left = f₀.left ≫ j) :
    f = f' :=
  (H g A₀ A i h hA hg g' B₀ B j k hB hg' f₀ fun _ hd ↦ push_mem_liftFil κ h k f₀ f e hd).unique
    ⟨inferInstance, e⟩ ⟨inferInstance, e'⟩

theorem LiftHom.exists_iso_iff (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (h' : IsGrpPullback A₀ A' (spMap π) i') (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g' A'.hom) :
    (∃ e : A ≅ A', IsMonHom e.hom ∧ i ≫ e.hom.left = i') ↔ liftFil κ h = liftFil κ h' := by
  have hid : ∀ d : Crys κ (spMap π) A₀, push κ (spMap π) (𝟙 A₀) d = d := fun d ↦ by
    rw [push_id]; rfl
  constructor
  · rintro ⟨e, _, he⟩
    have he' : i' ≫ e.inv.left = i := by
      rw [← he, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]
    refine le_antisymm (fun d hd ↦ ?_) fun d hd ↦ ?_
    · exact hid d ▸ push_mem_liftFil κ h h' (𝟙 A₀) e.hom (by simpa using he) hd
    · exact hid d ▸ push_mem_liftFil κ h' h (𝟙 A₀) e.inv (by simpa using he') hd
  · intro e
    obtain ⟨f, _, ef⟩ := (H.exists_iff h hA hg h' hA' hg' (𝟙 A₀)).2 fun d hd ↦ by
      rw [hid, ← e]; exact hd
    obtain ⟨f', _, ef'⟩ := (H.exists_iff h' hA' hg' h hA hg (𝟙 A₀)).2 fun d hd ↦ by
      rw [hid, e]; exact hd
    rw [Over.id_left, Category.id_comp] at ef ef'
    refine ⟨⟨f, f', H.unique h hA hg h hA hg (𝟙 A₀) ?_ (by simp),
      H.unique h' hA' hg' h' hA' hg' (𝟙 A₀) ?_ (by simp)⟩, inferInstance, ef⟩
    · rw [Over.comp_left, ← Category.assoc, ef, ef', Over.id_left, Category.id_comp]
    · rw [Over.comp_left, ← Category.assoc, ef', ef, Over.id_left, Category.id_comp]

theorem crysRedMor (κ : DividedPowers I) (hI : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ (dp0 R₀) (𝟙 _) A₀ π (𝟙 _) (Over.Hom.left (𝟙 A₀)) := by
  refine GrpMor.of_hom ?_ (Category.id_comp _).symm (𝟙 A₀)
  have z : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hI ▸ ha)
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ z a ha, fun n hn a ha ↦ ?_⟩
  rw [z a ha, z _ (κ.dpow_mem hn ha), dpow_eval_zero _ hn]

theorem corr_crysToDR_iff (hI : RingHom.ker π = I) (h : IsGrpPullback A₀ A (spMap π) i)
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (y : HdR A₀) :
    (redMor h).Corr (crysToDR κ h d) y ↔ (crysRedMor κ hI A₀).Corr d y := by
  have e : ∀ c, (crysRedMor κ hI A₀).pull ((liftMor κ h).pull c) = (redMor h).pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by simp) c
  refine ⟨fun H c ↦ ?_, fun H c ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := hs c
    rw [e]; exact H c
  · rw [← e]; exact H _

theorem canonical_of_abelianDeRham (P : AbelianDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Canonical κ π := by
  intro g A₀ _ A _ i h hA hg
  obtain ⟨PF, PH, PB, PR, -⟩ := P
  letI : Algebra R R₀ := π.toAlgebra
  obtain ⟨-, ⟨N, hN⟩, -⟩ := PH R A g hA hg
  have hF : PrimitiveSubmodule A₀ = Submodule.span R₀ ((redMor h).pull '' (PrimitiveSubmodule A)) :=
    (PB R A g hA hg R₀ A₀ i h).2
  have := (PF.prim hA hg).2.1
  refine ⟨PR R A g hA hg I κ hκ R₀ π hπ hI A₀ i h, ⟨N.dualAnnihilator, ?_, ?_⟩, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, Fil, ← Submodule.dualAnnihilator_sup_eq, hN.sup_eq_top,
      Submodule.dualAnnihilator_top]
  · refine codisjoint_iff_le_sup.2 fun x _ ↦ Submodule.mem_sup.2
      ⟨x ∘ₗ Submodule.projection _ _ hN.symm, ?_, x ∘ₗ Submodule.projection _ _ hN, ?_, ?_⟩
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero]
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN).2 hc, map_zero]
    · ext c
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add, add_comm,
        Submodule.projection_add_projection_eq_self hN]
  · intro hy
    let l : primDR A →ₗ[R] R₀ :=
      { toFun c := y ((redMor h).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨x ∘ₗ Submodule.projection _ _ hN.symm, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero], fun c ↦ ?_⟩
    have z : l (Submodule.projection _ _ hN c) = 0 := (Submodule.mem_dualAnnihilator _).1 hy _
      (hF ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    change l c = π (x _)
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add, z, zero_add, ← hx]
    rfl
  · rintro ⟨x, hx, e⟩
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker y)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero])

theorem at_dualNumber (H : GrothendieckMessing) {p : ℕ} (hp : p.Prime) (hR : IsNilpotent (p : R)) :
    At (epsDP R) (TrivSqZeroExt.fstHom R R R).toRingHom :=
  H p hp _ (by simpa using hR.map (algebraMap R (DualNumber R))) _ _ (isDPNilpotent_squareZero _) R _
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl

end GrothendieckMessing

end GlobalTheory.Published
