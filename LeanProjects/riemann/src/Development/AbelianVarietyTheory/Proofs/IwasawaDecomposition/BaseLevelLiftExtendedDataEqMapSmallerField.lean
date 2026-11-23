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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem unipotentBaseLevelChar_map_coefficientField {E : Type} [Field E] [NumberField E] {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (ψ' : ∀ PP : Pl E, AddChar (kP PP) K') (h : ∀ PP c, ψ' PP c = φ (ψ PP c))
    (g : G0 Pg r) (hg : g ∈ (P0 Pg r ψ).H) (hg' : g ∈ (P0 Pg r ψ').H) :
      ((((P0 Pg r ψ').chi⁻¹ ⟨g, hg'⟩ : K'ˣ)) : K') = φ (((P0 Pg r ψ).chi⁻¹ ⟨g, hg⟩ : Kˣ) : K) := by
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
  congr 1
  unfold P0 LevelP.ofLocal at *
  dsimp only
  rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h _ _

theorem exists_int_of_mem_vGs {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : 𝓞 X.E ⧸ P.asIdeal) : ∃ b : ℤ, x = b := by
  classical
  have h : ∃ i, P ∈ Pr.vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := h
  have hc : Nat.card (𝓞 X.E ⧸ P.asIdeal) = Pr.g i := by
    rw [← hPr.vG_norm i P hi, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 X.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ (hPr.g_prime i).ne_zero)
  exact Formalism.L2.Col.owedC_exists_int (hPr.g_prime i) hc x

theorem baseLevels_correspond_weilAdditiveChars {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (I : ColIn B px) (I' : ColIn B' px')
    (hB : B'.toPre = B.toPre) (hpx : HEq px' px) (hPr : (B.primes px).Ok) (hw : I.Ch.WeilTied B.embLL B.host.xi0)
    (hw' : I'.Ch.WeilTied B'.embLL B'.host.xi0)
    (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) (e : Gc B px ≃* Gc B' px') (he : ∀ g, HEq (e g) g) :
    ∃ hP : lev0 I' = (lev0 I).map e.toMonoidHom, ∀ h : lev0 I,
      (((chr0 I')⁻¹ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : B'.LLˣ) : B'.LL) =
        φ (((chr0 I)⁻¹ h : B.LLˣ) : B.LL) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  have he' : e = MulEquiv.refl _ := MulEquiv.ext fun g => eq_of_heq (he g)
  subst he'
  refine ⟨(Subgroup.map_id _).symm, fun h => ?_⟩
  refine unipotentBaseLevelChar_map_coefficientField φ _ _ (psiC I) (psiC I') (fun PP c => ?_) h.1 h.2 h.2
  unfold psiC
  split_ifs with hP hQ hQ
  · obtain ⟨b, hb⟩ := exists_int_of_mem_vGs hPr hP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
    apply RingHom.injective (Base.embLL _)
    exact (hw' ⟨PP, hP⟩ c b hb).trans ((hφ _).trans (hw ⟨PP, hP⟩ c b hb)).symm
  · exact absurd hP hQ
  · exact absurd hQ hP
  · rw [AddChar.one_apply, AddChar.one_apply, map_one]

set_option maxHeartbeats 2000000 in

theorem lev_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∃ hP : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).P = ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P.map e.toMonoidHom, ∀ h : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P, ((((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).ψ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).ψ h : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ e he => ?_
  exact baseLevels_correspond_weilAdditiveChars w.I w'.I hE.1 hpx w.l.pr w.ok.weil w'.ok.weil φ hφ e he

end GlobalTheory.Mem.R3.DefLatBC

end
