import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.Chart0

open GlobalTheory.Mem.Col2.MemChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

abbrev lvQ (a : I.ι) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

def yT (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) : GA B (B.R.N 0) :=
  Classical.epsilon fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)

theorem yT_spec (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    PtOf (yT I u a c * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u a 0).rep c).1.1)
  exact Classical.epsilon_spec (p := fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1))
    ⟨g * (kStd X u (B.R.N 0))⁻¹, by rwa [inv_mul_cancel_right]⟩

theorem cos0 {u : B.Word} {a : I.ι} (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) : cosetIn q = cosetIn q' := by
  have key : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0, cosetIn q = fun _ => ∅ := fun q => by
    have h1 : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne _ _ _ (by have := B.R.two_le_m; omega)] at this
    funext P
    unfold cosetIn
    rw [h1]
    simp
  rw [key, key]

theorem stepZero_classes_bijective_decoratedLattice (hI : I.Ok) (u : B.Word) (a : I.ι) :
    Function.Bijective fun c : (I.stp u a 0).Cl =>
      decoCls (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ((I.stp u a 0).rep c).1.1.deco := by
  letI := StepZero.idxUnique (hI.idx_ok a)
  have h := StepZero.clMap_bijective (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)) (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) (StepZero.levQAt_zero (I.Tp a) (hI.idx_ok a))
  convert h using 1
  funext c
  have e := StepZero.clMap_cl (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) c.1 ((I.stp u a 0).rep c)
  have e2 : (I.stp u a 0).cl c.1 ((I.stp u a 0).rep c) = c := by
    obtain ⟨b, q⟩ := c
    exact congrArg (Sigma.mk b) ((I.stp u a 0).rp_spec b q)
  rw [e2] at e
  exact e.symm

theorem stab_range0 (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (stM (lvG I a) (lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c).range ↔
      ∃ g : UF B.fields.E (B.R.N 0) × (colLev I.Ch 0).grp, ufGL B.fields.E (B.R.N 0) g.1 = γ ∧
        g • ((I.stp u a 0).rep c).1.1.deco = ((I.stp u a 0).rep c).1.1.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) ((I.Tp a).pref u 0) (StepZero.levGAt_zero (I.Tp a) hL) c.1 g, rfl, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) _ (StepZero.levGAt_zero (I.Tp a) hL) c.1 g _).symm.trans (congrArg (fun q => q.1.1.deco) hg)
  · rintro ⟨g₀, rfl, hg⟩
    obtain ⟨g, h1, h2⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy (StepZero.levGAt_zero (I.Tp a) hL)
      (StepZero.levQAt_zero (I.Tp a) hL) c.1 _ _ g₀ hg
    exact ⟨⟨g, h2⟩, congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h1⟩

theorem red0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u), redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)

theorem lev0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q) :
    x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, cos0 I _ _⟩
    · show ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := red0 I hI hPr u a c x κ h1 (h2 ▸ h)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = colLev I.Ch 0 → ∀ g : Λ'.grp,
        g.1 ∈ (colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

theorem chr0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (hxU : x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp)
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ((levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) ⟨x, hxU⟩ : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a 0).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩ = (⟨κ.2.1.1, hΛ c.1 ▸ κ.2.1.2⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((lvG I a c.1).chr κ.2.1 * (lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl

set_option maxHeartbeats 1000000 in

theorem charts_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  intro B X I hI hP l Z u a
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  obtain ⟨hg, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 0 hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hL := hI.idx_ok a
  let chOf : (I.stp u a 0).Cl → Unit := fun _ => ()
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N 0)
    (fun w => (colLev I.Ch 0 w).H) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = B.T u)) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N 0) hPr u) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)
    (gramN (I.rec7 l Z) 0 hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // chOf c = ()} => (I.stp u a 0).Stab c.1) (fun c => latCrd (I.rec7 l Z) 0 hi (I.latAt u a 0 c.1))
    (diaT (Pr := B.primes X) u) (fun c => ((I.stp u a 0).rep c.1).1.1.deco) (fun c => yT I u a c.1)
    (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).1) (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).2)
    ((stepZero_classes_bijective_decoratedLattice I hI u a).comp (Equiv.subtypeUnivEquiv fun _ => rfl).bijective) (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a) (lvQ I a) _ _ c.1) (fun c => stM_inj (lvG I a) (lvQ I a) _ _ ((l.ch u a).step 0) c.1)
    (fun c γ => stab_range0 I hI u a c.1 γ)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N 0)
  letI := StepZero.idxUnique hL
  obtain ⟨q₀, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  refine ⟨badG (I.rec7 l Z), Unit, chOf, fun _ => ⟨lev, Y, h1, h2, SI, h3, h4⟩, fun _ => kStd X u (B.R.N 0),
    ⟨fun c c' => ⟨fun _ => ⟨Subsingleton.elim _ _, cos0 I _ _⟩, fun _ => rfl⟩,
      fun _ => ⟨(I.stp u a 0).cl default q₀, rfl⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3,
      fun c => ?_, fun c x q h => ?_, fun c x κ hκ h => ?_, fun c s => h9 _ _⟩⟩
  · exact (h5 ▸ Iff.rfl : x ∈ lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := h8 ⟨c, rfl⟩
    show PtOf ((Y ⟨c, rfl⟩).1 * kStd X u (B.R.N 0)) _
    rw [e]
    exact yT_spec I hI u a c
  · have e := h8 ⟨c, rfl⟩
    replace h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q := e ▸ h
    exact (h6 ▸ Iff.rfl : x ∈ lev.U ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp).trans (lev0 I hI hPr u a c x q h)
  · have e := h8 ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ x.2
    refine (congrArg Units.val (h7 x hx)).trans ?_
    exact chr0 I hI hPr u a c x.1 hx κ hκ (e ▸ h)

end GlobalTheory.Mem.Col2.TC.Chart0
