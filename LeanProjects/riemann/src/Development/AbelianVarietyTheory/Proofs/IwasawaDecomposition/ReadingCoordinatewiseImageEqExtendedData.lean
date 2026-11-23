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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftRead

theorem read_of_span {L L' : Type} [Field L] [Field L'] (φ : L →+* L') (σ : L →+* ℂ) (σ' : L' →+* ℂ) (hφ : ∀ x, σ' (φ x) = σ x)
    {n n' : ℕ} (hn : n = n') {H H' : Type} (nH : NormedAddCommGroup H) (nH' : NormedAddCommGroup H')
    (iH : InnerProductSpace ℂ H) (iH' : InnerProductSpace ℂ H') (hH : H' = H) (h1 : HEq nH' nH) (h2 : HEq iH' iH)
    (j : (Fin n → L) →ₛₗ[σ] H) (j' : (Fin n' → L') →ₛₗ[σ'] H') (S : Set (Fin n → L)) (hS : Submodule.span L S = ⊤)
    (hj : ∀ y ∈ S, ∃ y' : Fin n' → L', (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → σ' (y' k') = σ (y k)) ∧ HEq (j' y') (j y))
    (x : Fin n → L) (x' : Fin n' → L') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq (j' x') (j x) := by
  subst hn hH
  cases h1
  cases h2
  have e : x' = fun k => φ (x k) := funext fun k => hx k k rfl
  subst e
  clear hx
  refine heq_of_eq ?_
  have hx : x ∈ Submodule.span L S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', a, b⟩ := hj y hy
    have e : (fun k => φ (y k)) = y' := funext fun k => σ'.injective ((hφ _).trans (a k k rfl).symm)
    rw [e]
    exact eq_of_heq b
  | zero =>
    have e : (fun k => φ ((0 : Fin n → L) k)) = 0 := by funext k; simp
    rw [e, map_zero, map_zero]
  | add y z _ _ hy hz =>
    have e : (fun k => φ ((y + z) k)) = (fun k => φ (y k)) + fun k => φ (z k) := by funext k; simp
    rw [e, map_add, map_add, hy, hz]
  | smul a y _ hy =>
    have e : (fun k => φ ((a • y) k)) = φ a • fun k => φ (y k) := by funext k; simp
    rw [e, map_smulₛₗ, map_smulₛₗ, hy, hφ]

set_option maxHeartbeats 4000000 in

theorem hmod_fields {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X) :
    X'.H = X.H ∧ HEq X'.nH X.nH ∧ HEq X'.iH X.iH := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 4000000 in

theorem read_extN {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x) := by
  have hk := hE.κ j j' hj
  have hc : ↥(z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) =
      ↥(z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) := (by with_unfolding_all exact ((cusp_type_congr (P₁ := B.toPre) (P₂ := B'.toPre) q (congrArg (· + 1) hj) hk.2.2
      hE.H hE.l hE.c hE.Dw hE.Xo hE.U hk.1 hk.2.1) :))
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) q
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm hE.nW j j' hj
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, hr⟩ := hE.MW j j' hj
  obtain ⟨h0, h1, h2⟩ := hmod_fields q j j' hj _ _ a b c d l e g _ _ hW
  obtain ⟨m, bs, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
  refine read_of_span φ _ _ hφ hn _ _ _ _ h0 h1 h2 _ _ (Set.range bs) hsp ?_ x x' hx
  rintro _ ⟨i, rfl⟩
  obtain ⟨u, hu⟩ := (z.geo.fw.e j).surjective ⟨bs i, hb i⟩
  have hu' : bs i = (z.geo.fw.e j u : (z.R.FW j).WK).1 := (congrArg Subtype.val hu).symm
  rw [hu']
  exact ⟨(z'.geo.fw.e j' (cast hc.symm u) : (z'.R.FW j').WK).1, hE.forms j j' hj u _ (cast_heq _ _), hr u _ (cast_heq _ _)⟩

set_option maxHeartbeats 2000000 in

theorem read_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hExt j j' hj φ hφ x x' hx => ?_
  exact read_extN hE.1 hExt j j' hj φ hφ x x' hx

end GlobalTheory.Mem.R3.LiftRead

end
