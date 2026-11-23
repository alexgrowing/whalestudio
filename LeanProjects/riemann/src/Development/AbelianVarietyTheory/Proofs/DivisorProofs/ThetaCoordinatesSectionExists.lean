import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionOverCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionEqOfGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedSectionGenericValueNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaSectionsRatioCoordinatesOverlapStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : Γ(X, U)) :
    resG X h₂ (resG X h₁ f) = resG X (h₂.trans h₁) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem chart_sec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G))
    (hn : Geo.Tor.IsNormalScheme M.Z) (ho : Odd m) (h3 : 3 ≤ m) (hu : IsUnit (m : k)) (hp : PolFib t.G t.PP.L g M.pt)
    (hg : IsGenSec t.G t.PP.L _ θ) (hl : ThList t.G t.PP.L t.PP.rig m M.pt θ pt c) (hc : PCrd (M.pt ≫ h) c)
    (a : Fin (n + 1)) : ∃ s : LocSec t.G t.PP.L (h ⁻¹ᵁ chart k n a), IsLocSec s ∧
      ((((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)) ∧
      FibNz s (h ⁻¹ᵁ chart k n a)) := by
  by_cases hne : ((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty
  · have hloc := GlobalTheory.T.exists_localSection_thetaQuotient_projChart E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc a
    choose N hzN hNle s hs hgs hfs using hloc
    let κ := {z : M.Z // z ∈ h ⁻¹ᵁ chart k n a}
    have hsup : (⨆ z : κ, N z.1 z.2) = h ⁻¹ᵁ chart k n a :=
      le_antisymm (iSup_le fun z => hNle z.1 z.2) fun z hz =>
        TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzN z hz⟩
    obtain ⟨s', hs', hres⟩ := GlobalTheory.T.exists_glued_lineBundleSection_over_cover M.Z t.G t.PP.L (h ⁻¹ᵁ chart k n a) κ (fun z => N z.1 z.2) (fun z => s z.1 z.2)
      (fun z => hNle z.1 z.2) hsup (fun z => hs z.1 z.2) (fun z z' i =>
        GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen _ _ _ _ _ (hgs z.1 z.2) (hgs z'.1 z'.2) i)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.glued_section_generic_value_nonvanishing M.Z t.G t.PP.L Ω M.pt _ κ (fun z => N z.1 z.2) (fun z => s z.1 z.2) s' _
      (fun z => hNle z.1 z.2) hsup hres (fun z => hgs z.1 z.2) (fun z => hfs z.1 z.2)
    exact ⟨s', hs', fun _ => h1 ⟨⟨hne.some, hne.some_mem⟩⟩, h2⟩
  · refine ⟨0, isLocSec_zero, fun h' => absurd h' hne, fun K _ _ x hx => absurd ?_ hne⟩
    exact ⟨_, hx ⟨IsLocalRing.closedPoint K, rfl⟩⟩

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem app_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U) (x : Γ(X, U)) :
    (f.app V).hom (resG X e x) = resG Y (fun _ hy => e hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ((f.app U).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) : valF y V (resG X e f) = valF y U f := by
  unfold valF
  rw [dif_pos hV, dif_pos (hV.trans fun x hx => show y x ∈ U from e (show y x ∈ V from hx))]
  congr 1
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl

theorem val_res' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := rfl

theorem val_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    ((pullU f U u : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = (f.app U).hom (u : Γ(X, U)) := rfl
end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

set_option maxHeartbeats 2000000 in

theorem pull_theta_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n), Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt → HasTh t.G t.PP.L t.PP.rig m M.pt c → PCrd (M.pt ≫ h) c → ∃ σ : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).Sec, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), ∃ (y : Sp K ⟶ t.G.left) (j : _), y ≫ t.G.hom = x ∧ Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U j ∧ valF y _ (σ.f j) ≠ 0 := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h hn ho h3 hu hp hth hc
  obtain ⟨θ, pt, hg, hl⟩ := hth
  choose s hs hgs hfs using chart_sec E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc
  have hcross := GlobalTheory.T.localThetaSections_ratio_coordinates_overlap k Ω M t.G t.PP.L n c h (SecM.ofSec t.G θ) hc (GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen)
  have hle : ∀ p : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).ι,
      (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U p ≤
        t.PP.L.U p.1 ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (p.2 PUnit.unit PUnit.unit)) := fun p y hy =>
    ⟨hy.1, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩
  refine ⟨⟨fun p => resG _ (hle p) (s _ p.1), fun p q => ?_⟩, fun K _ _ x => ?_⟩
  · obtain ⟨i, pj⟩ := p
    obtain ⟨i', qj⟩ := q
    have eB : ∀ (Y : Scheme.{0}) (φ : Y ⟶ M.Z) (u v : PUnit → PUnit → Fin (n + 1)),
        ((((ProjSpace.O1 k n).pull h).pull φ).g u v : Γ(Y, _)) =
          resG Y (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
              Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩ :
            (((ProjSpace.O1 k n).pull h).pull φ).U u ⊓ (((ProjSpace.O1 k n).pull h).pull φ).U v ≤
              φ ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (u PUnit.unit PUnit.unit) ⊓ chart k n (v PUnit.unit PUnit.unit))))
            ((φ.app _).hom ((h.app _).hom (ratioOn (chart k n (u PUnit.unit PUnit.unit) ⊓
              chart k n (v PUnit.unit PUnit.unit)) _ inf_le_left (v PUnit.unit PUnit.unit)))) := by
      intro Y φ u v
      have e1 := ProjSpace.linComb_punit_g ((ProjSpace.O1 k n).pull h) φ 1 u v
      have e2 := ProjSpace.linComb_punit_g (ProjSpace.O1 k n) h 1 (u PUnit.unit) (v PUnit.unit)
      rw [zpow_one] at e1 e2
      erw [e1]
      erw [e2]
      erw [val_res', val_pullU', val_res', val_pullU']
      rw [O1_g_eq_ratioUnit_chart_inf, val_ratioUnit]
      erw [app_resG, resG_resG']
      rfl
    have hW1 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (pj PUnit.unit PUnit.unit) ⊓ chart k n (qj PUnit.unit PUnit.unit))) :=
      fun y hy => ⟨hy.1.1, (hle _ hy.1).2, (hle _ hy.2).2⟩
    have hW2 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.PP.L.U i' ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (qj PUnit.unit PUnit.unit)) :=
      fun y hy => ⟨⟨hy.1.1, hy.2.1⟩, (hle _ hy.2).2⟩
    have e1 := congrArg (resG t.G.left hW1) (hcross _ _ (s _) (s _) (hgs _) (hgs _) i)
    have e2 := congrArg (resG t.G.left hW2) (hs (qj PUnit.unit PUnit.unit) i i')
    rw [map_mul] at e1 e2
    erw [resG_resG', resG_resG', resG_resG'] at e1
    erw [resG_resG', resG_resG', resG_resG'] at e2
    show resG _ _ (resG _ (hle (i, pj)) (s (pj PUnit.unit PUnit.unit) i)) = _ *
      resG _ _ (resG _ (hle (i', qj)) (s (qj PUnit.unit PUnit.unit) i'))
    rw [resG_resG', resG_resG']
    erw [Units.val_mul, val_res', val_res', eB, resG_resG']
    rw [e1, e2, mul_left_comm, ← _root_.mul_assoc]
    rfl
  · obtain ⟨a, ha⟩ := exists_mem_chart k n (h (x (IsLocalRing.closedPoint K)))
    have hx : Set.range x ⊆ h ⁻¹ᵁ chart k n a := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
      exact ha
    obtain ⟨y, i, hyx, hyr, hv⟩ := hfs a K x hx
    have hyr' : Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U
        (i, fun _ _ => a) := fun _ hw =>
      ⟨(hyr hw).1, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => (hyr hw).2⟩
    refine ⟨y, (i, fun _ _ => a), hyx, hyr', ?_⟩
    show valF y _ (resG _ (hle (i, fun _ _ => a)) (s a i)) ≠ 0
    rwa [valF_resG y _ ((GlobalTheory.ZH.top_le_preimage_iff y _).2 hyr')]

end GlobalTheory.UMin.ThBdl
