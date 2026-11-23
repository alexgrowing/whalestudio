import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltrationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

section Step

variable {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I J : Ideal R} {I₁ : Ideal R₁}
  {κ : DividedPowers I} {π : R →+* R₀} {hJ : J ^ 2 = 0} {ρ : R →+* R₁} {κ₁ : DividedPowers I₁}
  {π₁ : R₁ →+* R₀}

theorem IsStep.spMap_eq (st : IsStep κ π hJ ρ κ₁ π₁) : spMap π = spMap π₁ ≫ spMap ρ := by
  rw [← st.comp, Cris.spMap_comp]

theorem IsStep.idMor (st : IsStep κ π hJ ρ κ₁ π₁) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) :=
  GrpMor.of_hom st.dp st.spMap_eq (𝟙 A₀)

def redSub (hρ : Function.Surjective ρ) {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A]
    {i₂ : A₁.left ⟶ A.left} (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (F : Submodule R (HdR A)) :
    Submodule R₁ (HdR A₁) where
  carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
  add_mem' := by
    rintro y y' ⟨x, hx, e⟩ ⟨x', hx', e'⟩
    exact ⟨x + x', F.add_mem hx hx', fun c ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, e, e', map_add]⟩
  zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
  smul_mem' := by
    rintro r₁ y ⟨x, hx, e⟩
    obtain ⟨r, rfl⟩ := hρ r₁
    exact ⟨r • x, F.smul_mem r hx, fun c ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, e, map_mul]⟩

theorem mem_liftFil_iff (P : AbelianDeRham) (st : IsStep κ π hJ ρ κ₁ π₁) {g : ℕ} {A₀ : Over (Sp R₀)}
    [GrpObj A₀] {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A] {i₁ : A₀.left ⟶ A₁.left}
    {i₂ : A₁.left ⟶ A.left} {i : A₀.left ⟶ A.left} (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁)
    (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i) (ei : i₁ ≫ i₂ = i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    d₁ ∈ liftFil κ₁ h₁ ↔ ∃ d ∈ liftFil κ h, (st.idMor A₀).Corr d d₁ := by
  have T := GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
    (st.idMor A₀) (Fil A) (redSub st.surj h₂ (Fil A)) (fun _ ↦ Iff.rfl)
  have e : Fil A₁ = redSub st.surj h₂ (Fil A) := Submodule.ext T.2
  rw [liftFil, Submodule.mem_comap, e, T.1 d₁]
  exact Iff.rfl

theorem dualMap_push {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀] {A₁ B₁ : Over (Sp R₁)} [GrpObj A₁]
    [GrpObj B₁] {i₁ : A₀.left ⟶ A₁.left} {j₁ : B₀.left ⟶ B₁.left}
    (NA : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁)
    (NB : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) B₀ (RingHom.id R) (spMap π₁) j₁)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) [IsMonHom f₀] [IsMonHom f₁] (e : i₁ ≫ f₁.left = f₀.left ≫ j₁)
    (d : Crys κ (spMap π) A₀) :
    (NB.pull : prim (divided₂ hJ) (spMap ρ) B₁ →ₗ[R] prim κ (spMap π) B₀).dualMap (push κ (spMap π) f₀ d) =
      push (divided₂ hJ) (spMap ρ) f₁
        ((NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  refine LinearMap.ext fun c ↦ ?_
  have m := (homMor (divided₂ hJ) (spMap ρ) f₁).comp NA
  have e1 : (homMor κ (spMap π) f₀).pull (NB.pull c) = m.pull c :=
    GrpMor.pull_pull NB (homMor κ (spMap π) f₀) m (fun _ ↦ rfl) e.symm c
  have e2 : NA.pull ((homMor (divided₂ hJ) (spMap ρ) f₁).pull c) = m.pull c :=
    GrpMor.pull_pull (homMor (divided₂ hJ) (spMap ρ) f₁) NA m (fun _ ↦ rfl) rfl c
  exact congrArg d (e1.trans e2.symm)

end Step

theorem liftHom_of_isStep : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftHom (divided₂ hJ) ρ → LiftHom κ₁ π₁ → LiftHom κ π := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st H₂ H₁
  intro g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have hc : spMap (π₁.comp ρ) = spMap π := by rw [st.comp]
  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, ei, hA₁, hgA⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A i (by rw [hc]; exact h) hA hg
  obtain ⟨B₁, _, j₁, j₂, k₁, k₂, ej, hB₁, hgB⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g' B₀ B j (by rw [hc]; exact k) hB hg'

  have hf₁ : ∀ d₁ ∈ liftFil κ₁ h₁, push κ₁ (spMap π₁) f₀ d₁ ∈ liftFil κ₁ k₁ := by
    intro d₁ hd₁
    obtain ⟨d, hd, e⟩ := (mem_liftFil_iff P st h₁ h₂ h ei hA hg d₁).1 hd₁
    exact (mem_liftFil_iff P st k₁ k₂ k ej hB hg' _).2
      ⟨_, hf d hd, GrpMor.Corr.push (st.idMor B₀) f₀ f₀ (by simp) e⟩
  obtain ⟨f₁, ⟨_, ef₁⟩, uf₁⟩ := H₁ g A₀ A₁ i₁ h₁ hA₁ hgA g' B₀ B₁ j₁ k₁ hB₁ hgB f₀ hf₁

  obtain ⟨NA, bA, cA⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
  obtain ⟨NB, -, cB⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g' B₀ B₁ B j₁ j₂ j k₁ k₂ k ej hB hg'
  have sA : Function.Surjective
      (NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap :=
    (LinearEquiv.ofBijective _ bA).dualMap.surjective
  have hf₂ : ∀ e ∈ liftFil (divided₂ hJ) h₂, push (divided₂ hJ) (spMap ρ) f₁ e ∈ liftFil (divided₂ hJ) k₂ := by
    intro e he
    obtain ⟨d, rfl⟩ := sA e
    have hd : d ∈ liftFil κ h := by
      rw [liftFil, Submodule.mem_comap, cA]; exact he
    have hk := hf d hd
    rw [liftFil, Submodule.mem_comap, cB] at hk
    rw [liftFil, Submodule.mem_comap, ← dualMap_push NA NB f₀ f₁ ef₁ d]
    exact hk
  obtain ⟨f, ⟨_, ef⟩, uf⟩ := H₂ g A₁ A i₂ h₂ hA hg g' B₁ B j₂ k₂ hB hg' f₁ hf₂
  refine ⟨f, ⟨inferInstance, ?_⟩, ?_⟩
  · rw [← ei, ← ej, Category.assoc, ef, ← Category.assoc, ef₁, Category.assoc]
  · rintro f' ⟨_, ef'⟩
    let f₁' : A₁ ⟶ B₁ := Over.homMk (k₂.1.lift (i₂ ≫ f'.left) A₁.hom
      (by rw [Category.assoc, Over.w f', h₂.1.w])) (k₂.1.lift_snd _ _ _)
    have e₁ : f₁'.left ≫ j₂ = i₂ ≫ f'.left := k₂.1.lift_fst _ _ _
    haveI := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback h₂ k₂ f' f₁' e₁
    have e₂ : i₁ ≫ f₁'.left = f₀.left ≫ j₁ := by
      refine k₂.1.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, ← Category.assoc, ei, ef', Category.assoc, ej]
      · rw [Category.assoc, Category.assoc, Over.w f₁', h₁.1.w, k₁.1.w, ← Category.assoc, Over.w f₀]
    have e₃ : f₁' = f₁ := uf₁ f₁' ⟨inferInstance, e₂⟩
    exact uf f' ⟨inferInstance, by rw [← e₁, e₃]⟩

end GlobalTheory.SqLift
