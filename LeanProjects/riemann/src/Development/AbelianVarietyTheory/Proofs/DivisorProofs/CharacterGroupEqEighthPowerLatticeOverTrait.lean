import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelOpenAbelianEighthPowerWithBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerTraitLatticeEquivLocalExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PeriodsEighth

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ M.Z) (D : DegPre R) (m : Fin 8 → Fin 8 → (D.X →+ D.X)) (T : Trait F) (ψ : R →+* T.V), ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∀ (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Sp (FractionRing T.V))) (U' : Unif (maximalIdeal T.V) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ι : D.X ≃+ D'.toPre.X), IsSemiAbelian G' → IsGrpPullback G' FinalForm.G (spMap ψ ≫ ξ) gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → CoordMap D D'.toPre ψ ι.toAddMonoidHom → (∀ a b, ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ (f a b).left ∧ ∀ m', EndChar U' f' m' → ∀ y, ι (m a b y) = m' (ι y)) → ∃ ρT : D.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ _ S ρ u c pr hsh M U₀ EE FinalForm hov V v hv f hf R _ _ _ ξ D m T ψ hT G' _ _ D' A' U'
    gm ι hG hpb hL hco hm
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  obtain ⟨ξ₀, h1, h2⟩ := hT
  obtain ⟨c', pr', hs', hmat⟩ := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hsh M U₀ EE FinalForm hov V v hv).2 T.V hBV G' hG
    D' A' U' (spMap ψ ≫ ξ) gm hpb hL ξ₀ h1
  have e0 : spMap (RingHom.id (FractionRing T.V)) ≫ T.y = ξ₀ ≫ v := by
    have : spMap (RingHom.id (FractionRing T.V)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, ← h2, Category.comp_id]
  have key : ∀ y₀ : Sp (FractionRing T.V) ⟶ F.X, spMap (RingHom.id (FractionRing T.V)) ≫ T.y = y₀ →
      ∀ c'' pr'', SharpBy F W A' y₀ c'' pr'' → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (T.ϖ ^ (qW W T.β (e y)).toNat)) ∧
      ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f →
        MatEnd pr'' a b f₁ → (Over.pullback (jK T.V)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m →
        ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro _ rfl c'' pr'' hs''
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n o ζ F W hW T T.V hBV inferInstance G' hG D' A' U' (RingHom.id _) (RingHom.id _)
      inferInstance (fun _ => rfl) c'' pr'' hs''
  obtain ⟨e, he1, he2⟩ := key _ e0 c' pr' hs'
  refine ⟨ι.trans e, fun y r hr => ?_, fun a b y => ?_⟩
  · obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D'.toPre (ι y)).2
      (GlobalTheory.PeriodFormCompare.psiIn_top D' _)
    obtain ⟨h0, ha⟩ := he1 _ _ hr'
    exact ⟨h0, (hco y r r' hr hr').trans ha⟩
  · obtain ⟨f', hfm, hf', hmm⟩ := hm a b
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom T.V hBV G' hG D' A' U' f' hfm
    obtain ⟨f₁, hf₁, hgen⟩ := hmat a b (f a b) f' (hf a b) hf'
    have := he2 a b f' f₁ m' hfm hf₁ hgen hm' (ι y)
    rw [← hmm m' hm' y] at this
    exact this

end GlobalTheory.Poinc.Eq8.PeriodsEighth
