import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatioStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorIdent

theorem squareGroup_hom_ext_projections {S : Scheme.{0}} (H : Over S) {X : Scheme.{0}} (a b : X ⟶ (G2 H).left)
    (h1 : a ≫ (fst H H).left = b ≫ (fst H H).left) (h2 : a ≫ (snd H H).left = b ≫ (snd H H).left) : a = b :=
  pullback.hom_ext h1 h2

theorem samePol_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → ∀ (A₉ : PolAV (Sp (FractionRing R₉))) (D₉' : DegData R₉ (maximalIdeal R₉)) (U₉ : Unif (maximalIdeal R₉) D₉' A₉ G₉), U₉.LG = P₉.L → ∃ D₉ : DegData R₉ (maximalIdeal R₉), Nonempty (IsPullDeg ρ₉ D.toPre D₉.toPre) ∧ SamePol D₉.toPre D₉'.toPre := by
  intro R _ _ _ hB D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉
    hfin hpb₉ hsq₉ hsa₉ hlam₉ A₉ D₉' U₉ hLG
  obtain ⟨hadm, hinj, hfinite⟩ := hfin
  haveI : CharZero R := hB.2
  have hloc : IsLocalHom ρ₉ := RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hfinite) hinj
  have hB₉ : Base R₉ := ⟨hadm, charZero_of_injective_ringHom hinj⟩
  obtain ⟨D₁, D₁', F₁, A₁', G₁', _, _, U₁', oA₁, oG₁, G₁, _, _, β, β₂, inc₁, pr₁, hpd, hsa₁', hlin₁, hsa₁, hinc₁, hpr₁,
      hip₁, hpi₁, hpb₁, hsq₁, hlb₁⟩ :=
    GlobalTheory.T.idempotentFactor_uniformised_groups_baseChange R hB.1 D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ hadm hinj hloc
  obtain ⟨e, he, hβ⟩ := grpPullback_iso hpb₉ hpb₁
  have hei : IsMonHom e.inv := inferInstance
  let m : G2 G₉ ⟶ G2 G₁ := lift (fst G₉ G₉ ≫ e.hom) (snd G₉ G₉ ≫ e.hom)
  have hm : β₉₂ = m.left ≫ β₂ := by
    apply squareGroup_hom_ext_projections G
    · rw [hsq₉.1, Category.assoc, hsq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc, hβ]
    · rw [hsq₉.2, Category.assoc, hsq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc, hβ]
  have hℓ : (lift (fst G₉ G₉ ≫ e.hom ≫ inc₁) (snd G₉ G₉ ≫ (e.hom ≫ inc₁) ≫ oG₁.act F₁.f) : G2 G₉ ⟶ G2 G₁').left =
      m.left ≫ (lift (fst G₁ G₁ ≫ inc₁) (snd G₁ G₁ ≫ inc₁ ≫ oG₁.act F₁.f) : G2 G₁ ⟶ G2 G₁').left := by
    rw [← Over.comp_left]
    congr 1
    simp [m]
  have hL' : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hL₁ : (abelian₂ G₁' U₁'.LG.L).IsLB := LB.isLB_linComb U₁'.LG.isLB _ _
  have h1 : LBIso (abelian₂ G₉ U₉.LG.L) ((abelian₂ G' U'.LG.L).pull
      (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
    rw [hLG]; exact hlam₉
  have h2 := GlobalTheory.GenSpread.lbIso_pull_pull hL'
    (a := (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ rfl
  have h3 := GlobalTheory.GenSpread.lbIso_pull_comp m.left hℓ hm hlb₁
  have hLam : LBIso (abelian₂ G₉ U₉.LG.L) ((abelian₂ G₁' U₁'.LG.L).pull
      (lift (fst G₉ G₉ ≫ e.hom ≫ inc₁) (snd G₉ G₉ ≫ (e.hom ≫ inc₁) ≫ oG₁.act F₁.f) : G2 G₉ ⟶ G2 G₁').left) :=
    LBIso.trans (LB.isLB_linComb U₉.LG.isLB _ _) (pull_isLB (pull_isLB hL' _) _) (pull_isLB hL₁ _)
      (LBIso.trans (LB.isLB_linComb U₉.LG.isLB _ _) (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) h1 h2)
      (LBIso.symm h3)
  have hsame : SamePol D₁.toPre D₉'.toPre :=
    GlobalTheory.T.samePolarisedData_of_idempotentFactor_uniformisation R₉ hB₉ D₁ D₁' F₁ A₁' G₁' hsa₁' U₁' oA₁ oG₁ hlin₁ G₉ hsa₉ (e.hom ≫ inc₁) (pr₁ ≫ e.inv)
      inferInstance inferInstance
      (by rw [Category.assoc, ← Category.assoc inc₁, hip₁, Category.id_comp, Iso.hom_inv_id])
      (by rw [Category.assoc, ← Category.assoc e.inv, Iso.inv_hom_id, Category.id_comp, hpi₁]) D₉' A₉ U₉ hLam
  exact ⟨D₁, hpd, hsame⟩

end GlobalTheory.Mum.FactorIdent
