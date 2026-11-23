import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.PullDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem corr_of_val_genMap (hφ : Function.Injective φ) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {ψ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')}
    (h : ∀ (z : (TK R').left) (J : ((TK R').left ⟶ X) → L.ι), Good L z J →
      val t (genMap hφ) z J = val t' (genMap hφ) z J) : LB.Gen.Corr L ψ ε ψ' ε' t t' :=
  corr_of_val_field_extension _ _ (fracMap hφ) X L hL K K' ψ ε ψ' ε' t t' h

theorem psiEven_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.PsiEven) :
    D.PsiEven := by
  intro χ
  obtain ⟨x, rfl⟩ := hD.xe.surjective χ
  refine corr_of_val_genMap hφ D.P.isLB fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) z
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have cW : (𝟙 _ ≫ D'.xK x) ≫ proj hD = genMap hφ ≫ D.xK (hD.xe x) := by
    rw [Category.id_comp]; exact cPoint_proj hD _ hh x
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  have e := val_corr hJ' (h x) (𝟙 (TK R').left)
  rw [val_mul hJ', val_pull hJ'] at e
  have a₁ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' (-x)
  have a₂ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' x
  have a₃ : val D.sym (genMap hφ ≫ D.xK (hD.xe x)) z J =
      om hD.w z J J' ((𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left) * (om hD.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ *
        val D'.sym (𝟙 _ ≫ D'.xK x) z J' :=
    (congrArg (fun q => val D.sym q z J) cW.symm).trans (PsiEvenPull.sym_pull hG hD _ z hJ hJ')
  rw [c', map_neg] at a₁
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) a₁ ((val_pull hJ _ _ _).trans a₃))
    (Eq.trans ?_ a₂.symm))
  rw [← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

set_option maxHeartbeats 1000000 in
theorem tauBimult_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.TauBimult) :
    D.TauBimult := by
  intro χ χ' ν
  obtain ⟨a, rfl⟩ := hD.xe.surjective χ
  obtain ⟨a', rfl⟩ := hD.xe.surjective χ'
  obtain ⟨b, rfl⟩ := hD.xe.surjective ν
  refine corr_of_val_genMap hφ D.P.isLB fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) y
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have gp := pull_grp hD
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk (genMap hφ) hh.symm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ proj hD = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => om hD.w (Z := (TK R').left) y J J' x.left
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' (T := TK R') y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => om hD.w (Z := (TK R').left) y J J' q)) rfl)
  let τ : D.X → D.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D.tau a b) (genMap hφ) y J
  let τ' : D'.X → D'.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D'.tau a b) (𝟙 (TK R').left) y J'
  have vτ : ∀ a b, τ (hD.xe a) (hD.xe b) =
      (Ω (cP D' _ a * cP D' _ b))⁻¹ * Ω (cP D' _ a) * Ω (cP D' _ b) * (Ω 1)⁻¹ * τ' a b := fun a b => by
    have e := tau_val hD (Z := (TK R').left) _ _ sq hJ hJ' a b
    simp only [Category.id_comp] at e
    rw [← cPoint_add]
    exact e
  have e : τ' (a + a') b * th D' (T := TK R') y J' (cP D' _ a) (cP D' _ a') (cP D' _ b) = τ' a b * τ' a' b := by
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_)
      ((val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (h a a' b) (𝟙 (TK R').left)).trans (val_mul hJ' _ _ _)))
    refine Eq.trans ?_ (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have key : τ (hD.xe a + hD.xe a') (hD.xe b) * θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      τ (hD.xe a) (hD.xe b) * τ (hD.xe a') (hD.xe b) := by
    rw [← βc, ← βc, ← βc, cub, ← map_add, vτ, vτ, vτ, cPoint_add]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) key
  refine (val_cub D.cub κ hJ (cP D _ (hD.xe a)) (cP D _ (hD.xe a')) (cP D _ (hD.xe b))).trans ?_
  rw [comp_cP, comp_cP, comp_cP]

end GlobalTheory.PullDescent

namespace GlobalTheory

theorem psiEven_tauBimult_of_isPullDeg_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) :=
  fun hG _ _ _ _ _ _ _ hφ _ _ hD => ⟨PullDescent.psiEven_desc hG hφ hD, PullDescent.tauBimult_desc hG hφ hD⟩

end GlobalTheory
