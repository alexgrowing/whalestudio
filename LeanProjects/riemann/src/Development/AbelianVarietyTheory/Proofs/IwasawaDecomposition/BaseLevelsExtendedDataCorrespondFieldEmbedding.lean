import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LevBC

theorem exists_intCast_of_card_prime {R : Type} [Ring R] (h : (Nat.card R).Prime) (x : R) : ∃ n : ℤ, (n : R) = x := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero h.ne_zero
  have htop : AddSubgroup.zmultiples (1 : R) = ⊤ := by
    rcases h.eq_one_or_self_of_dvd _ (AddSubgroup.card_addSubgroup_dvd_card (AddSubgroup.zmultiples (1 : R))) with h1 | h1
    · exfalso
      have hb := AddSubgroup.eq_bot_of_card_eq _ h1
      have h10 : (1 : R) = 0 := by
        have : (1 : R) ∈ AddSubgroup.zmultiples (1 : R) := AddSubgroup.mem_zmultiples 1
        rw [hb] at this
        exact (AddSubgroup.mem_bot).1 this
      have : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
      rw [Nat.card_unique] at h
      exact Nat.not_prime_one h
    · exact AddSubgroup.eq_top_of_card_eq _ h1
  have hx : x ∈ AddSubgroup.zmultiples (1 : R) := by rw [htop]; exact AddSubgroup.mem_top x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  exact ⟨n, by rw [← hn, zsmul_one]⟩

theorem exists_intCast_vGs (B : Base) (px : PreX B.toPre) (PP : Pl B.host.E) (hPP : PP ∈ (B.primes px).vGs)
    (c : 𝓞 B.host.E ⧸ PP.asIdeal) : ∃ n : ℤ, (n : 𝓞 B.host.E ⧸ PP.asIdeal) = c := by
  classical
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B px
  have hi : ∃ i, PP ∈ (B.primes px).vG i := by
    rcases Finset.mem_union.1 hPP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hi
  have hn := hPr.vG_norm i PP hi
  have hp := hPr.g_prime i
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  rw [← hn] at hp
  exact exists_intCast_of_card_prime hp c

theorem baseLevelCharacter_map_coefficientRingHom {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {LL LL' : Type} [CommRing LL] [CommRing LL']
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (ψ' : ∀ PP : Pl E, AddChar (kP PP) LL') (φ : LL →+* LL')
    (h : ∀ PP ∈ Pg, ∀ c, ψ' PP c = φ (ψ PP c)) (x : (P0 Pg r ψ).H) (x' : (P0 Pg r ψ').H) (hx : (x : G0 Pg r) = x') :
    (((P0 Pg r ψ').chi x' : LL'ˣ) : LL') = φ (((P0 Pg r ψ).chi x : LLˣ) : LL) := by
  obtain ⟨x, hxm⟩ := x
  obtain ⟨x', hxm'⟩ := x'
  simp only at hx
  subst hx
  show ((((∏ PP : ↥Pg, (addCharHom (ψ' PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm'⟩ : LL'ˣ)) : LL') =
    φ (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm⟩ : LLˣ) : LL)
  rw [MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h PP.1 PP.2 _

theorem lev_bc (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (I : ColIn B px) (I' : ColIn B' px') (hI : I.Ok) (hI' : I'.Ok) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    (g' ∈ lev0 I' ↔ g ∈ lev0 I) ∧ ∀ (h0 : g ∈ lev0 I) (h0' : g' ∈ lev0 I'),
      ((chr0 I' ⟨g', h0'⟩ : B'.LLˣ) : B'.LL) = φ (chr0 I ⟨g, h0⟩ : B.LLˣ) := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp I I' hI hI' φ hφ g g' hg
  subst h
  cases hp
  cases hg
  refine ⟨Iff.rfl, fun h0 h0' => ?_⟩
  refine baseLevelCharacter_map_coefficientRingHom _ _ _ _ φ (fun PP hPP c => ?_) ⟨_, h0⟩ ⟨_, h0'⟩ rfl
  rw [psiC_of_mem _ hPP, psiC_of_mem I' hPP]
  obtain ⟨n, hn⟩ := exists_intCast_vGs _ _ PP hPP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
  have e1 := hI'.weil ⟨PP, hPP⟩ c n hn.symm
  have e2 := hI.weil ⟨PP, hPP⟩ c n hn.symm
  have e3 := hφ (I.Ch.psi0 ⟨PP, hPP⟩ c)
  exact RingHom.injective _ (e1.trans (e2.symm.trans e3.symm))

end GlobalTheory.Mem.R3.LevBC

namespace GlobalTheory.Mem.R3.Rw

theorem extN_baseLevel_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (g' ∈ (z'.F.lv2.lvl false).P ↔ g ∈ (z.F.lv2.lvl false).P) ∧ ∀ (hg : g ∈ (z.F.lv2.lvl false).P) (hg' : g' ∈ (z'.F.lv2.lvl false).P), (((z'.F.lv2.lvl false).ψ ⟨g', hg'⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.F.lv2.lvl false).ψ ⟨g, hg⟩ : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ g g' hg
  exact GlobalTheory.Mem.R3.LevBC.lev_bc B B' hE.1 w.px w'.px hpx w.I w'.I w.ok w'.ok φ hφ g g' hg

end GlobalTheory.Mem.R3.Rw
