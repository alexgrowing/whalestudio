import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.ActExt

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.LevelActionPinned
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

private theorem congr_of_two_lifts {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : V.rank = L.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM0 : M ≠ 0) {Mb Mh : Ideal (𝓞 D.host.E)}
    (hMb : Mb = ∏ PP ∈ L.Pg, PP.asIdeal) (hM : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) (hcop : Mb ⊔ Mh = ⊤)
    {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {u u' : La →ₗ[𝓞 D.host.E] La}
    (hu : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w)
    (hu' : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u' a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w) (a : La) :
    u' a - u a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨κ, hκ, h1⟩ := hu
  obtain ⟨κ', hκ', h1'⟩ := hu'
  have hM₁ : (∏ PP ∈ L.Pg, PP.asIdeal) * Mh = Ideal.span {(M : 𝓞 D.host.E)} := by rw [← hMb, hM]
  have hMm : (M : 𝓞 D.host.E) ∈ Mb :=
    Ideal.mul_le_left (I := Mb) (J := Mh) (by rw [hM]; exact Ideal.mem_span_singleton_self _)
  have hst := mulVec_mem_of_St hβ (Formalism.L2.DIV.parLev_St hκ.2.1)
  have hd := Lev.lift_div_mem hκ hκ'
  obtain ⟨s, hs, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Mb ⊔ Mh)
  have hva : v • a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La) := Submodule.smul_mem_smul hv Submodule.mem_top
  obtain ⟨w₁, hw₁, e₁⟩ := h1 _ hva
  obtain ⟨w₂, hw₂, e₂⟩ := h1' _ hva
  obtain ⟨w₃, hw₃, e₃⟩ := lift_one_congr (L := L) hβ hL hι hM₁ hd.2.1 (Subgroup.mem_bot.1 hd.2.2) _ hva
  have e₄ : (finHom V κ').val = (finHom V κ).val * (finHom V (κ⁻¹ * κ')).val := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e₅ : fvec V ι (u' (v • a) - u (v • a)) = M • (w₂ - w₁ + (finHom V κ).val *ᵥ w₃) := by
    have e₁' : fvec V ι (u (v • a)) - (finHom V κ).val *ᵥ fvec V ι (v • a) = M • w₁ := e₁
    have e₂' : fvec V ι (u' (v • a)) - (finHom V κ').val *ᵥ fvec V ι (v • a) = M • w₂ := e₂
    rw [smul_add, smul_sub, ← Matrix.mulVec_smul, ← e₁', ← e₂', ← e₃, map_sub, e₄, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  obtain ⟨x, hx⟩ := exists_eq_nsmul hι hM0 _ _ (add_mem (sub_mem hw₂ hw₁) (hst _ hw₃)) e₅
  have e₆ : u' a - u a = s • (u' a - u a) + (M : 𝓞 D.host.E) • x := by
    rw [Nat.cast_smul_eq_nsmul, ← hx, map_smul, map_smul, ← smul_sub, ← add_smul, huv, one_smul]
  rw [e₆]
  exact add_mem (Submodule.smul_mem_smul hs Submodule.mem_top) (Submodule.smul_mem_smul hMm Submodule.mem_top)

private theorem latEmb_iota {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)

private theorem act_heq {D : D7} (i : Fin D.R.m)
    {β β' : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} (eβ : β' = β)
    {Λ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)} (hβ : IsSDFrame (Wc D i) (β i) Λ 1)
    {Pg Pg' : Finset (Formalism.L2.DIV.Pl D.host.E)} (eP : Pg' = Pg)
    {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {ι : ∀ j, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} {ι' : ∀ j, (Dw' j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    (hι : HEq ι' ι)
    (hemb : LatEmb (Wc D i) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)))
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    {G : Type} [Group G] {eG : G ≃* G0 Pg D.R.r} {eG' : G ≃* G0 Pg' D.R.r} (heG : HEq eG' eG)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La}
    {lev' : G → (Dw' ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw' ((i : ℕ) + 1)).La}
    (hlev : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) (Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) (lev g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) a)) = l.M • w)
    (hlev' : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β' i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG' g) κ ∧
      ∀ a ∈ Mfr l' • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) (lev' g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) a)) = l'.M • w)
    (g : G) (r : Rul (Xo ((i : ℕ) + 1)) c) (r' : Rul (Xo' ((i : ℕ) + 1)) c') (hr : HEq r' r) :
    HEq (actLev (Xo := Xo' ((i : ℕ) + 1)) c' (fun g => (lev' g, LinearMap.id)) g r')
      (actLev (Xo := Xo ((i : ℕ) + 1)) c (fun g => (lev g, LinearMap.id)) g r) := by
  subst eβ eP hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hι
  obtain rfl := eq_of_heq heG
  obtain rfl := eq_of_heq hr
  have key : ∀ g a, lev' g a - lev g a ∈ l'.Mb • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La) := fun g a =>
    congr_of_two_lifts
      (L := datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B)
      hβ (rank_Wc i) hemb (by have := l'.three_le; omega) hMb l'.prod l'.coprime (hlev g) (hlev' g) a
  have e : (fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev' g, LinearMap.id)) g y y') =
      fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev g, LinearMap.id)) g y y' := by
    funext S _ _ g y y'
    exact propext (GlobalTheory.LevelActionOfLifts.levR_congr (key g) y y')
  unfold actLev
  rw [e]

private theorem geo_facts {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GlobalTheory.RealGeo.GeoHalf T R ph) (i : Fin D.R.m) :
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (B.O i).lev ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧ LatEmb (Wc D i) (iotaW T i) :=
  ⟨(B.pins i).2.lift.lev, ((B.pins i).2.tuple ()).half.1, latEmb_iota T B.fw.laws i⟩

end GlobalTheory.Mem.R3.ActExt

set_option maxHeartbeats 2000000 in
theorem _root_.GlobalTheory.T.levelActions_on_liftRules_extendedData : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g →
        ∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r →
          HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj g g' hg r r' hr => ?_
  obtain ⟨h1, h3, h4⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z.geo j
  obtain ⟨h2, -, -⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z'.geo j'
  have h5 := z.lev.is.βW j
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  cases w with | mk px => ?_
  cases w' with | mk px' => ?_
  dsimp only at hpx px px'
  cases hpx
  have eg : g' = g := eq_of_heq hg
  subst eg
  exact GlobalTheory.Mem.R3.ActExt.act_heq j' (eq_of_heq hx.βW) h5 (eq_of_heq hx.Pg) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.iota h4 h3 hx.eG h1 h2 g' r r' hr
