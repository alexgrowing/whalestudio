import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerBaseChangeMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLabStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointWithTermsLabelClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.Poinc.Sep.div_lam_and_lam_mem_HH : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ ∧ ∀ a ∈ X₁.S.HH X₁.M z₁, 𝔗.lam a ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀ V _ _ _ ev X _ m t δ 𝔪
  refine ⟨GlobalTheory.T.dividingLabel_stays_dividing_deeper_model g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀ V ev X m t δ 𝔪, ?_⟩
  intro a ha
  obtain ⟨V', _, _, _, io, ev₂, hcn', hinj, hfin, -, -, hext⟩ := GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hTI
    X₁ z₁ act hact 𝔗 z₂ hz₂ V ev 𝔪.cn 𝔪.loc 𝔪.reg
  obtain ⟨u, hT, -, -⟩ := GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hx₀ V ev X m t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val
    Subtype.range_coe
  obtain ⟨eps, hbc⟩ := GlobalTheory.T.exists_thetaSetupTower_baseChange_member g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀
  obtain ⟨𝔪₂, hterms, -⟩ := hbc V ev X m t δ 𝔪 _ Subtype.val _ hT V' io hcn' hinj hfin
  let zt : 𝔗.X₂.M.Z.presheaf.stalk z₂ := (𝔗.X₂.M.stalkEquiv z₂).symm
    ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, (𝔗.X₂.M.O z₂).algebraMap_mem _⟩
  have hzt : 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ :=
    congrArg Subtype.val ((𝔗.X₂.M.stalkEquiv z₂).apply_symm_apply _)
  have hyy := GlobalTheory.T.torsionPoint_with_terms_labelClass_zero g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) V' ev₂ X m (fun k => io (t k)) δ (𝔪₂ ev₂ hext) _ _ _
    (hterms ev₂ hext zt hzt) ⟨a, ha⟩
  obtain ⟨x₂, hx₂⟩ := 𝔗.X₂.div z₂
  exact (GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ x₂ hx₂ V' ev₂ X m (fun k => io (t k)) δ (𝔪₂ ev₂ hext) (𝔗.lam a)).2 hyy
