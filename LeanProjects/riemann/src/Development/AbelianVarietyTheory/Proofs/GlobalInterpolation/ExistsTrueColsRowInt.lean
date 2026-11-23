import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace GlobalTheory.PerQ.RowIntModel

theorem mem_mtildeL_iff {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (z : MtildeV W Ch sel mu P) :
  z ∈ MtildeL W Ch sel mu P ↔ ∀ d : RowPt Pr R sel mu, z.1 d ∈ nabAt X.emb W.sgTrue d.1.N := Iff.rfl

theorem mtildeL_rep_mem {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (z : MtildeV W Ch sel mu P) (hz : z ∈ MtildeL W Ch sel mu P) (c : (stepX Ch sel mu P).Cl) :
  ∃ y ∈ nabAt X.emb W.sgTrue ((stepX Ch sel mu P).rep c).1.1.deco.1.N, y = z.1 (toRow sel mu ((stepX Ch sel mu P).rep c).1.1) :=
  ⟨z.1 (toRow sel mu ((stepX Ch sel mu P).rep c).1.1), toRow_N sel mu ((stepX Ch sel mu P).rep c).1.1 ▸ (mem_mtildeL_iff W Ch sel mu P z).1 hz (toRow sel mu ((stepX Ch sel mu P).rep c).1.1), rfl⟩

def rowEmbAt {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι)
  (hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)))
  (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) : (I.per l u a).Mt :=
  GlobalTheory.PeriodOnStep.rowEmb (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a) (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (I.perIn u a).H hd B.embLL z

theorem rowVal_rowEmbAt {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι)
  (hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)))
  (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) (hz : z ∈ MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) : GlobalTheory.PerQ.RowVal I l u a (rowEmbAt I l u a hd z) := by
  intro c
  obtain ⟨y, hy, e⟩ := mtildeL_rep_mem (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps z hz c
  refine ⟨y, hy, ?_⟩
  rw [e]
  rfl

open GlobalTheory.PerQ
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

theorem rowVal_add (u a) (G G' : (I.per l u a).Mt) (h : RowVal I l u a G) (h' : RowVal I l u a G') : RowVal I l u a (G + G') := by
  intro c
  obtain ⟨y, hy, e⟩ := h c
  obtain ⟨y', hy', e'⟩ := h' c
  refine ⟨y + y', add_mem hy hy', ?_⟩
  refine (map_add ((I.perIn u a).rd B.fields.emb B.embLL) G G' ▸ (?_ : ((I.perIn u a).rd B.fields.emb B.embLL G + (I.perIn u a).rd B.fields.emb B.embLL G') c = _))
  exact (congrArg₂ (· + ·) e e').trans (map_add _ _ _).symm

theorem rowVal_smul (u a) (o : B.O) (G : (I.per l u a).Mt) (h : RowVal I l u a G) : RowVal I l u a ((B.embLL.comp B.OtoLL) o • G) := by
  intro c
  obtain ⟨y, hy, e⟩ := h c
  refine ⟨(⟨B.OtoLL o, B.O_int o⟩ : 𝓞 B.fields.K) • y, Submodule.smul_mem _ _ hy, ?_⟩
  refine (map_smul ((I.perIn u a).rd B.fields.emb B.embLL) _ G ▸ (?_ : ((B.embLL.comp B.OtoLL) o • (I.perIn u a).rd B.fields.emb B.embLL G) c = _))
  refine (congrArg ((B.embLL.comp B.OtoLL) o • ·) e).trans ?_
  exact (LinearMap.map_smulₛₗ (mapS B.embLL) (B.OtoLL o) y.1).symm

open Classical in

def rowsRestOfSpanning (W : RowsRest B (I.cols l)) (s : ∀ a, Finset (W.Amb a)) (hs : ∀ a, Submodule.span ℂ (s a : Set (W.Amb a)) = ⊤) : RowsRest B (I.cols l) :=
  { W with
    Mtilde := fun a => ⟨s a, hs a⟩
    eMt0 := fun _ => W.eMtTw B.u₀ (I.cols l).mu0
    eMtTw := fun _ a => W.eMtTw B.u₀ a
    perCol := fun u μ φ F => if h : μ = (I.cols l).mu0 then ((I.cols l).mem u).P.PtilCol (W.eMu u φ).1 ((W.eMtTw B.u₀ (I.cols l).mu0).symm (h ▸ F))
      else ((I.cols l).PTw u μ).PtilCol ((I.cols l).e0Tw u μ (W.eMu u φ).1) ((W.eMtTw B.u₀ μ).symm F)
    perCol_base_eq_PtilCol := fun u φ F => dif_pos rfl
    perCol_tie := fun u μ h φ F => dif_neg h }

theorem rowVal_of_mem_carrier (W : RowsRest B (I.cols l)) (a) (L : Rows.OLat B.O (B.embLL.comp B.OtoLL) (W.Amb a))
   (h : ∀ v ∈ L.gen, RowVal I l B.u₀ a ((W.eMtTw B.u₀ a).symm v)) : ∀ F ∈ L.carrier, RowVal I l B.u₀ a ((W.eMtTw B.u₀ a).symm F) := by
  rintro F ⟨c, rfl⟩
  rw [map_sum]
  refine Finset.sum_induction _ (RowVal I l B.u₀ a) (rowVal_add I l _ _) (rowVal_zero I l _ _) fun v hv => ?_
  rw [map_smul]
  exact rowVal_smul I l _ _ _ _ (h v hv)

open GlobalTheory.Mem.Col2.TrueColsTest in

theorem exists_rowInt_of_span (hB : StagesInhab.HasLetters B.toPre)
   (hspan : ∀ a, Submodule.span ℂ {G : (I.per l B.u₀ a).Mt | RowVal I l B.u₀ a G} = ⊤) : ∃ Z, RowInt I l Z := by
  obtain ⟨Z0⟩ := later l hB
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  let W0 := RowsRestModel.model (fits l) 1 1 1
  have key : ∀ a, ∃ s : Finset (W0.Amb a), Submodule.span ℂ (s : Set (W0.Amb a)) = ⊤ ∧ ∀ v ∈ s, RowVal I l B.u₀ a ((W0.eMtTw B.u₀ a).symm v) := by
    intro a
    have h1 : Submodule.span ℂ {v : W0.Amb a | RowVal I l B.u₀ a ((W0.eMtTw B.u₀ a).symm v)} = ⊤ := by
      have h0 : Submodule.span ℂ {G : ((I.cols l).PTw B.u₀ a).Mt | RowVal I l B.u₀ a G} = ⊤ := hspan a
      have := congrArg (Submodule.map (W0.eMtTw B.u₀ a).toLinearMap) h0
      rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this
      refine eq_top_iff.2 (this.ge.trans (Submodule.span_mono ?_))
      rintro _ ⟨G, hG, rfl⟩
      show RowVal I l B.u₀ a ((W0.eMtTw B.u₀ a).symm (W0.eMtTw B.u₀ a G))
      rw [LinearEquiv.symm_apply_apply]; exact hG
    obtain ⟨s, hs1, hs2⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (h1 ▸ Module.Finite.fg_top)
    exact ⟨s, (hs2.symm.trans h1), fun v hv => hs1 hv⟩
  choose s hs hv using key
  let W := rowsRestOfSpanning I l W0 s hs
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => ipC_herm l u x y) (fun u x hx h => ipC_pos l u x hx h) (show 1 ≤ 2 * 1 by omega)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  exact ⟨⟨GaloisStage.adapt W, V, S, N, G⟩, fun u F hF => rowVal_of_mem_carrier I l W0 (I.cols l).mu0 ⟨s _, hs _⟩ (hv _) F hF,
    fun u a F hF => rowVal_of_mem_carrier I l W0 (show (I.cols l).Tup from a) ⟨s _, hs _⟩ (hv _) F hF⟩

section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

theorem span_mtildeL (hX : X.Ok) : Submodule.span X.K (MtildeL W Ch sel mu P : Set (MtildeV W Ch sel mu P)) = ⊤ := (MtildeH_good W Ch hX sel mu P).2.2

theorem span_toMtP (hX : X.Ok) : Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) = ⊤ :=
    toCForm_span_of_span σ W.sgTrue _ _ hX (φ := fun z : MtildeL W Ch sel mu P => z.1) (eq_top_iff.2 ((span_mtildeL W Ch sel mu P hX).ge.trans (Submodule.span_mono fun z hz => ⟨⟨z, hz⟩, rfl⟩)))
include hd in

theorem exists_form_of_mt (F : (perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ) : ∃ G : MtP W Ch sel mu P σ, ∀ b d, F.1 b d = G.1 (toRow sel mu d.1.1) := by
  have hl : FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F.1 () (trivPt X _ _ _ _ p) := by
    intro p
    refine ⟨(F.2 () _).1, fun g hg => ?_⟩
    show F.1 () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (F.2 () (trivPt X _ _ _ _ p)).2 g hg
  obtain ⟨G, hG, e⟩ := hl.exists_form σ W.sgTrue (isSubLev_top _ _) hd
  exact ⟨⟨G, hG⟩, fun b p => ((e p.1.1).trans (congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p))).symm⟩

theorem exists_mem_of_form (hX : X.Ok) (T : Submodule ℂ ((perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ))
  (hT : ∀ z ∈ MtildeL W Ch sel mu P, rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ z ∈ T) (G' : MtP W Ch sel mu P σ) : ∃ F' ∈ T, ∀ b d, F'.1 b d = G'.1 (toRow sel mu d.1.1) := by
    have hG' : G' ∈ Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) := by
      rw [span_toMtP W Ch sel mu P σ hX]; exact Submodule.mem_top
    induction hG' using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ⟨_, hT z.1 z.2, fun _ _ => rfl⟩
    | zero => exact ⟨0, zero_mem _, fun _ _ => rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ea⟩ := hx; obtain ⟨b, hb, eb⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun c d => congrArg₂ (· + ·) (ea c d) (eb c d)⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, ea⟩ := hx
      exact ⟨r • a, Submodule.smul_mem _ _ ha, fun c d => congrArg (r • ·) (ea c d)⟩

theorem eq_top_of_rowEmb_mem (hX : X.Ok) (T : Submodule ℂ ((perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ))
  (hT : ∀ z ∈ MtildeL W Ch sel mu P, rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ z ∈ T) : T = ⊤ :=
  Submodule.eq_top_iff'.2 fun F => (exists_form_of_mt W Ch sel mu P b0 til ext tz hd σ F).elim fun G e =>
    (exists_mem_of_form W Ch sel mu P b0 til ext tz hd σ hX T hT G).elim fun F' h =>
      (congrArg (· ∈ T) (Subtype.ext (funext fun b => funext fun p => (h.2 b p).trans (e b p).symm) : F' = F)).mp h.1
end G

theorem span_rowVal (a) (hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) (hX : B.fields.Ok) (u) :
    Submodule.span ℂ {G : (I.per l u a).Mt | RowVal I l u a G} = ⊤ :=
    eq_top_of_rowEmb_mem (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a) (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz hd B.embLL hX (Submodule.span ℂ {G : (I.per l u a).Mt | RowVal I l u a G}) fun z hz => (Submodule.subset_span (rowVal_rowEmbAt I l u a hd z hz) : rowEmbAt I l u a hd z ∈ Submodule.span ℂ {G : (I.per l u a).Mt | RowVal I l u a G})

theorem exists_trueCols_rowInt : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Ok ∧ I.muStar ≠ I.mu0 ∧ RowInt I l Z := by
  obtain ⟨B, X, I, hL, h, hP, hs⟩ := TrueColsTest.exists_ok_pins
  obtain ⟨Z, hZ⟩ := exists_rowInt_of_span I (TrueColsTest.laws h) hL fun a => span_rowVal I _ a
    (Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1) (base_fields_primes_ok B X).1 _
  exact ⟨B, X, I, _, Z, h, hs, hZ⟩

end GlobalTheory.PerQ.RowIntModel
end
