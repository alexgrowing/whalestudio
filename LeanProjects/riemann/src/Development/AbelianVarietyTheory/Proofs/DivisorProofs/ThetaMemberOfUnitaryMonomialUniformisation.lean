import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingValuePointLiesOverUnitaryModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUniformisationGenericFibreIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateActionUniformisationCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryUniformisationBaseChangeInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

theorem member_of_monomial_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (m : ℕ) (s : Fin m → V) (β : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre s β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁) (r : Fin m → V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → (∀ k, r k ^ 2 = ρ (s k)) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ y ≫ C.i → ∃ (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev (Fin 1 → P.D.toPre.X) (mono !![(1 : ℤ)] r β) (fun a mu => a • mu)) (p : IsPullDeg ρ P.D.toPre 𝔪.D.toPre), ∀ mu, p.xe (𝔪.e₈ mu) = mu 0 := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ act u π hL z₁ V _ _ _ hV t y P hG m s β hmono V₁ _ _ _ ρ fK r hV₁ hinj hloc hfK hr ev hev hreg hpt
  obtain ⟨t₁, P₁, p, hG₁, hlin, hpsi⟩ := GlobalTheory.T.exists_unitaryUniformisation_baseChange_injective E H Dw l Xo c V hV t y P hG V₁ ρ fK hV₁ hinj hloc hfK
  obtain ⟨yK, x', hyK, hx', hx'u⟩ := GlobalTheory.T.thetaRing_valuePoint_lies_over_unitaryModuli E H Dw hpq l Xo c C X₁ act u π hL z₁ V₁ ev (spMap fK ≫ y) hreg
    (hpt.trans (Category.assoc _ _ _).symm)
  obtain ⟨φ, hcart, hwl, hact⟩ := GlobalTheory.T.unitaryUniformisation_genericFibre_isPullback E H Dw hpq l Xo c C X₁ act u π hL V₁ hV₁ t₁ P₁ yK x' hx'
    (by rw [hx'u]; exact hG₁)
  obtain ⟨wl, hwl⟩ := hwl
  let e₈ : (Fin 1 → P.D.toPre.X) ≃+ P₁.D.toPre.X := (AddEquiv.piUnique fun _ : Fin 1 => P.D.toPre.X).trans p.xe.symm
  have he₈ : ∀ mu, p.xe (e₈ mu) = mu 0 := fun mu => by simp [e₈]
  refine ⟨{
    cn := hV₁
    loc := hev
    reg := hreg
    yK := yK
    yK_eq := hyK
    D := P₁.D
    e₈ := e₈
    G := t₁.G
    semi := t₁.semi
    A := P₁.A
    U := P₁.U
    φ := φ
    cart := hcart
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ?_ }, p, he₈⟩
  · obtain ⟨En, hEn, hh⟩ := GlobalTheory.T.conjugateAction_uniformisation_characters E H V₁ hV₁ t₁ P₁ a
    refine ⟨En, by rw [hEn]; exact hact a, fun mu => ?_⟩
    rw [hh]
    apply p.xe.injective
    rw [hlin, he₈, he₈]
    rfl
  · obtain ⟨u₀, n, hn, hc⟩ := hmono (mu 0)
    rw [← he₈ mu] at hc
    obtain ⟨w, hw⟩ := hpsi _ _ hc
    refine ⟨w * Units.map ρ.toMonoidHom u₀, ?_⟩
    have hmo : mono !![(1 : ℤ)] r β mu = ρ (∏ i, s i ^ n i) := by
      simp only [mono, qW, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val', one_mul, map_prod, map_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hn i, ← hr i, ← pow_mul]
      congr 1
      omega
    rw [hmo]
    have hu : (↑(w * Units.map ρ.toMonoidHom u₀) : V₁) * ρ (∏ i, s i ^ n i) = ↑w * ρ (↑u₀ * ∏ i, s i ^ n i) := by
      rw [map_mul, Units.val_mul, Units.coe_map, _root_.mul_assoc]; rfl
    rw [hu]
    exact hw

end GlobalTheory.USep
