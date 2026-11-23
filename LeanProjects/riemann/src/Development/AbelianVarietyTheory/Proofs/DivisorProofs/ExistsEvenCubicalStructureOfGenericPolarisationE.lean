import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenPackage

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'}

theorem jK_sq (hρ : Function.Injective ρ) : jK R' ≫ spMap ρ =
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem exists_genericMap (hρ : Function.Injective ρ) {G : Over (Sp R)} {G₁ : Over (Sp R')} {β : G₁.left ⟶ G.left}
    (w : β ≫ G.hom = G₁.hom ≫ spMap ρ) : ∃ κ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R),
      κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β := by
  refine ⟨pullback.lift _ (pullback.snd _ _ ≫
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, jK_sq hρ]

theorem isGrpPullback_generic (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ := by
  have hsq := jK_sq hρ
  have hmono : Mono (jK R) := EvenDesc.mono_jK R
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  exact (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w

theorem exists_square_extLam (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] [IsCommMonObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left) (hL : L.IsLB) (hExt : ExtLam G L PP) :
    ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ExtLam G₁ (L.pull κ₁) (PP.pull β₂) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨β₂, hsqβ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G G₁ β hβ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨β₂, hsqβ, pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have hN := pull_isLB hL κ₁
  have H1 := Hκ L (L.pull κ₁) _ PP g₂ hL hN hExt.1 (GlobalTheory.PolBaseChange.lbIso_refl hN) (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_generic_pol (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (hgen : IsMonHom gen.hom) :
    ∃ (A' : PolAV (Sp (FractionRing R'))) (gen' : (Over.pullback (jK R')).obj G₁ ≅ A'.A), IsMonHom gen'.hom ∧
      LBIso (A'.L.pull gen'.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  obtain ⟨A', gA, pA, -, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _
    (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) gA :=
    ⟨pA, fun T x y x₀ y₀ hx hy => by
      have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
      have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
      rw [e₁, e₂, ← mA]; rfl⟩
  have tA' : LBIso (A.L.pull gA) A'.L := tA
  obtain ⟨e, he, hee⟩ := grpPullback_iso ((hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl) gpA
  refine ⟨A', e, he, ?_⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso tA'.symm e.hom.left hee.symm)
    (GlobalTheory.GenSpread.lbIso_pull_pull A.isLB κ₁ rfl)

end GlobalTheory.Mum.EvenPackage

set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.EvenPackage in

theorem GlobalTheory.Mum.exists_even_package_of_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW
    R₃ _ _ _ ρ₃ G₃ _ _ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃ hL₃ hL₃g
  have hR₃ : Base R₃ := by
    haveI := hR.2
    exact ⟨hρ₃.1, charZero_of_injective_ringHom hρ₃.2.1⟩
  have hG₃ : IsSemiAbelian G₃ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ₃ hG
  obtain ⟨R₉, i1, i2, i3, ρ₄, G₉, i4, i5, β₄, X, i6, i7, i8, hρ₄, hβ₄, hTQ⟩ :=
    exists_finExt_tq_closedFibre R₃ hR₃ G₃ hG₃
  have hρ : FinExt (ρ₄.comp ρ₃) := ⟨hρ₄.1, hρ₄.2.1.comp hρ₃.2.1, hρ₄.2.2.comp hρ₃.2.2⟩
  have hβ : IsGrpPullback G₉ G (spMap (ρ₄.comp ρ₃)) (β₄ ≫ β₃) :=
    (hβ₄.comp hβ₃).congr (TraitExt.spMap_comp _ _) rfl
  have hG₉ : IsSemiAbelian G₉ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ hG
  obtain ⟨κ₄, hκ₄⟩ := exists_genericMap hρ₄.2.1 hβ₄.1.w
  have hκ₉ : (κ₄ ≫ κ₃) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₄ ≫ β₃ := by
    rw [Category.assoc, hκ₃, ← Category.assoc, hκ₄, Category.assoc]
  have hN : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have hL₉ : (L₃.pull β₄).IsLB := pull_isLB hL₃ _
  have hL₉g : LBIso ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) ((A.L.pull gen.hom.left).pull (κ₄ ≫ κ₃)) :=
    LBIso.trans (pull_isLB hL₉ _) (pull_isLB hL₃ _) (pull_isLB hN _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hL₃ (pullback.fst G₉.hom (jK R₉)) rfl).symm
      (GlobalTheory.GenSpread.lbIso_pull_comp κ₄ hκ₄.symm rfl hL₃g)
  obtain ⟨A₉, gen₉, hgen₉, hA₉⟩ := exists_generic_pol hρ.2.1 hβ hκ₉ A gen hgen
  have hA₉' : LBIso (A₉.L.pull gen₉.hom.left) ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) :=
    LBIso.trans (pull_isLB A₉.isLB _) (pull_isLB hN _) (pull_isLB hL₉ _) hA₉ hL₉g.symm
  have hprop : IsProper (pullback.snd G₉.hom (jK R₉)) := by
    have hi : IsIso gen₉.hom.left := ((Over.forget _).mapIso gen₉).isIso_hom
    have := A₉.isAb.proper
    have hw : pullback.snd G₉.hom (jK R₉) = gen₉.hom.left ≫ A₉.A.hom := (Over.w gen₉.hom).symm
    rw [hw]; infer_instance
  have hsym := GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen₉.hom hgen₉ _ _ A₉.isLB (pull_isLB hL₉ _) A₉.sym hA₉'
  haveI : IsNoetherianRing R₉ := hρ.1.1
  haveI : IsIntegrallyClosed R₉ := hρ.1.2.2.1
  obtain ⟨P, hP⟩ := GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R₉ G₉ hG₉ hprop _ hL₉ hsym
  obtain ⟨β₂, hsq, hE⟩ := exists_square_extLam hρ.2.1 hβ hκ₉ _ PP hN hPP
  refine ⟨R₉, i1, i2, i3, ρ₄.comp ρ₃, G₉, i4, i5, β₄ ≫ β₃, β₂, P, A₉, gen₉, hρ, hβ, hsq, hG₉, ?_, ?_, hgen₉, ?_⟩
  · rw [hP]
    exact lbIso_lam_of_extLam R₉ G₉ hG₉ _ _ _ hL₉ (pull_isLB hN _) hL₉g.symm hE
  · refine evenOn_of_trait_unif R hR G hG A gen hgen W φ GW βW DW AW UW κ hW hφi hφl hGW hκ hUW R₉ _ G₉ _ _ P hρ hβ hκ₉
      ?_ X hTQ
    rw [hP]; exact hL₉g
  · rw [hP]; exact hA₉'

end
