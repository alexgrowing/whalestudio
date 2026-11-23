import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_stalkHom_fromSpecStalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_uMem_injective : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X), Function.Injective ev ∧ Nonempty (UMem X₁ z₁ act V ev X t δ) := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth X₁ z₁ act hact
  obtain ⟨hdom, hfr, hic, hnoeth⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : CharZero (X₁.M.Z.presheaf.stalk z₁) := (X₁.M.stalkHom z₁).charZero
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (X₁.M.Z.presheaf.stalk z₁) (maximalIdeal _)
  haveI : IsLocalHom φ₀ := ((IsLocalRing.local_hom_TFAE φ₀).out 0 4).2 hmax
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hchar⟩
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : X₁.Ω₁ →+* FractionRing V₀ := IsFractionRing.lift (A := X₁.M.Z.presheaf.stalk z₁) hg₀
  have hemb : ∀ r, emb (X₁.M.stalkHom z₁ r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := X₁.M.Z.presheaf.stalk z₁) hg₀ r
  have hpt : jK V₀ ≫ spMap φ₀ ≫ X₁.M.Z.fromSpecStalk z₁ = spMap emb ≫ X₁.M.pt := by
    rw [← spMap_stalkHom_fromSpecStalk, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    ext r
    exact (hemb r).symm
  let y₀ : Sp (FractionRing V₀) ⟶ F.X := spMap emb ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u
  have hy₀ : y₀ ≫ i = jK V₀ ≫ spMap φ₀ ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π := by
    simp only [y₀, Category.assoc]
    rw [← X₁.comp, ← Category.assoc (jK V₀), ← Category.assoc (jK V₀ ≫ spMap φ₀), Category.assoc (jK V₀), hpt,
      Category.assoc]
  obtain ⟨T, f, fK, hf, hfl, hff, hfK, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ (zetaAway n) F V₀ hB hdvr y₀
  haveI := hfl
  let ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V := f.comp φ₀
  have hev : Function.Injective ev := hf.comp hinj₀
  have hkey : jK T.V ≫ spMap ev = spMap fK ≫ jK V₀ ≫ spMap φ₀ := by
    rw [show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl,
      show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_comp_spMap, spMap_comp_spMap,
      spMap_comp_spMap]
    congr 1
    ext a
    simp only [RingHom.comp_apply]
    exact (hfK _).symm
  have hpt' : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ = spMap fK ≫ spMap emb ≫ X₁.M.pt := by
    rw [← Category.assoc, hkey, Category.assoc, Category.assoc, hpt]
  have hreg : RegAt X₁ z₁ ev := by
    intro a _
    rw [hpt']
    change a ∈ X₁.M.O (X₁.M.pt ((spMap fK ≫ spMap emb) (closedPoint (FractionRing T.V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  have hcomm : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i := by
    rw [hTy, Category.assoc, hy₀, ← Category.assoc (jK T.V), hkey]
    simp only [Category.assoc]
  obtain ⟨hmono, hnn, -, -⟩ := GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ (zetaAway n) F T
  have hCN : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact T.V
    (Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β] (fun k => by fin_cases k; exact T.irr.ne_zero)
    (fun k a b => by fin_cases k; exact T.symm a b) (fun k a => by fin_cases k; exact hnn a) hmono T.V (RingHom.id _)
    hCN Function.injective_id (RingHom.Finite.id T.V) T.D (AddEquiv.refl _) (Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂
    T.semi T.cart T.sq T.lb ev inferInstance hreg hcomm
  exact ⟨T.V, inferInstance, inferInstance, inferInstance, ev, _, inferInstance, 1, _, _, hev, ⟨𝔪⟩⟩
end GlobalTheory.Poinc.Sep
