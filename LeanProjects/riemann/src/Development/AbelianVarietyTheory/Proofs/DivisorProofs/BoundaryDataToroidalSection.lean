import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSncStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open ReciprocityTheory.AnForm.M (IsSNC IsCompatChart)
open ReciprocityTheory.AnForm.R.FinalTheorems (LSncAt)
open GlobalTheory.ShFam (LiesIn IsDivNorm ev_eq_zero_iff isOpen_not_liesIn)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryData

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d m : ℕ}
  {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

def compPot (i : Fin m) : LocPot (CxPts p σ) where
  U := (GlobalTheory.DivSec.divPot hn).U
  isOpen_U := (GlobalTheory.DivSec.divPot hn).isOpen_U
  mem_U := (GlobalTheory.DivSec.divPot hn).mem_U
  φ y z := GlobalTheory.DivSec.eqF hn i y z / 2

def compSec (i : Fin m) (y z : CxPts p σ) : ℂ := ev p σ (GlobalTheory.DivSec.eqV hn i y).1 (GlobalTheory.DivSec.eqT hn i y) z

theorem norm_compSec_mul {i : Fin m} {y z : CxPts p σ} (hz : z ∈ (GlobalTheory.DivSec.divPot hn).U y) :
    ‖compSec hn i y z‖ * Real.exp (-(compPot hn i).φ y z) = n i z := by
  have e := (GlobalTheory.DivSec.eq_spec hn i y).2.2.2 z (GlobalTheory.DivSec.mem_eqV hn hz i)
  have h0 := ((hn i).1 z).1
  have hx : Real.exp (-GlobalTheory.DivSec.eqF hn i y z) = Real.exp (-GlobalTheory.DivSec.eqF hn i y z / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hx, ← mul_pow] at e
  have h1 := (pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e
  simp only [compSec, compPot]
  rw [h1, neg_div]

theorem isSection_compSec {B : FinHolAtlas d (CxPts p σ)} (hB : IsAlgAtlas B) (i : Fin m) :
    IsSection B (compPot hn i) (compSec hn i) :=
  ⟨fun y => (hB.holoOn_iff R ((GlobalTheory.DivSec.divPot hn).isOpen_U y)).2 fun j =>
      (R.holoOn_ev _ (GlobalTheory.DivSec.eqT hn i y) j).mono fun v hv => ⟨hv.1, GlobalTheory.DivSec.mem_eqV hn hv.2 i⟩,
    fun _ _ _ hz => by rw [norm_compSec_mul hn hz.1, norm_compSec_mul hn hz.2]⟩

end GlobalTheory.BdryData

namespace GlobalTheory.BdryData

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem sub_eq_re_of_eqns (R : AnRead p σ d) (C : Closeds Y) (n : CxPts p σ → ℝ) (V V' : Y.affineOpens)
    (t : Γ(Y, V.1)) (t' : Γ(Y, V'.1)) (f f' : CxPts p σ → ℝ) (hC : Dense {z : CxPts p σ | ¬ LiesIn z C})
    (ht : (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t})
    (ht' : (Scheme.IdealSheafData.vanishingIdeal C).ideal V' = Ideal.span {t'})
    (hf : R.SmoothOn (ptsIn p σ V.1) f) (hf' : R.SmoothOn (ptsIn p σ V'.1) f')
    (hn : ∀ z ∈ ptsIn p σ V.1, n z ^ 2 = ‖ev p σ V.1 t z‖ ^ 2 * Real.exp (-f z))
    (hn' : ∀ z ∈ ptsIn p σ V'.1, n z ^ 2 = ‖ev p σ V'.1 t' z‖ ^ 2 * Real.exp (-f' z))
    (y₀ : CxPts p σ) (hy₀ : y₀ ∈ ptsIn p σ V.1 ∩ ptsIn p σ V'.1) :
    ∃ W : Set (CxPts p σ), IsOpen W ∧ y₀ ∈ W ∧ ∃ G : CxPts p σ → ℂ, R.HoloOn W G ∧
      ∀ z ∈ W ∩ ptsIn p σ V.1 ∩ ptsIn p σ V'.1, f z - f' z = (G z).re := by
  have hx : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ V.1 ⊓ V'.1 := ⟨mem_ptsIn.1 hy₀.1, mem_ptsIn.1 hy₀.2⟩
  obtain ⟨h, hhW, hxh⟩ := V.2.exists_basicOpen_le (V := V.1 ⊓ V'.1) ⟨_, hx⟩ hx.1
  let Wa : Y.affineOpens := ⟨Y.basicOpen h, V.2.basicOpen h⟩
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_left
  have hWV' : Wa.1 ≤ V'.1 := hhW.trans inf_le_right
  have hy0W : y₀ ∈ ptsIn p σ Wa.1 := mem_ptsIn.2 hxh
  have e1 : (Scheme.IdealSheafData.vanishingIdeal C).ideal Wa = Ideal.span {resG Y hWV t} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, ht, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : (Scheme.IdealSheafData.vanishingIdeal C).ideal Wa = Ideal.span {resG Y hWV' t'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V') hWV', ht', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1
    (e2 ▸ e1 ▸ Ideal.mem_span_singleton_self (resG Y hWV t) : resG Y hWV t ∈ Ideal.span {resG Y hWV' t'})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1
    (e1 ▸ e2 ▸ Ideal.mem_span_singleton_self (resG Y hWV' t') : resG Y hWV' t' ∈ Ideal.span {resG Y hWV t})
  have hev : ∀ z ∈ ptsIn p σ Wa.1, ev p σ V.1 t z = ev p σ Wa.1 a z * ev p σ V'.1 t' z := by
    intro z hz
    rw [← ev_res hWV hz, ← ha, ev_mul, ev_res hWV' hz]
  have hev' : ∀ z ∈ ptsIn p σ Wa.1, ev p σ V'.1 t' z = ev p σ Wa.1 b z * ev p σ V.1 t z := by
    intro z hz
    rw [← ev_res hWV' hz, ← hb, ev_mul, ev_res hWV hz]
  have hopen : IsOpen (ptsIn p σ Wa.1) := isOpen_ptsIn _
  have hclo : ptsIn p σ Wa.1 ⊆ closure (ptsIn p σ Wa.1 ∩ {z | ¬ LiesIn z C}) := hC.open_subset_closure_inter hopen
  have hab : ∀ z ∈ ptsIn p σ Wa.1, ev p σ Wa.1 a z * ev p σ Wa.1 b z = 1 := by
    have hoff : Set.EqOn (fun z => ev p σ Wa.1 a z * ev p σ Wa.1 b z) (fun _ => 1)
        (ptsIn p σ Wa.1 ∩ {z | ¬ LiesIn z C}) := by
      rintro z ⟨hz, hzC⟩
      have ht0 : ev p σ V.1 t z ≠ 0 := fun h0 => hzC ((ev_eq_zero_iff ht (ptsIn_mono hWV hz)).1 h0)
      have := hev z hz
      rw [hev' z hz] at this
      have h2 : ev p σ V.1 t z * 1 = ev p σ V.1 t z * (ev p σ Wa.1 a z * ev p σ Wa.1 b z) := by
        rw [mul_one]; conv_lhs => rw [this]
        ring
      exact (mul_left_cancel₀ ht0 h2).symm
    exact Set.EqOn.of_subset_closure hoff ((continuousOn_ev _).mul (continuousOn_ev _)) continuousOn_const
      Set.inter_subset_left hclo
  have ha0 : ∀ z ∈ ptsIn p σ Wa.1, ev p σ Wa.1 a z ≠ 0 := fun z hz h0 => by
    have := hab z hz
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  set g := ev p σ Wa.1 (a * a) with hg_def
  have hg0 : ∀ z ∈ ptsIn p σ Wa.1, g z ≠ 0 := fun z hz => by
    rw [hg_def, ev_mul]; exact mul_ne_zero (ha0 z hz) (ha0 z hz)
  have hgn : ∀ z, ‖g z‖ = ‖ev p σ Wa.1 a z‖ ^ 2 := fun z => by
    rw [hg_def, ev_mul, norm_mul, sq]
  obtain ⟨W₁, hW₁, hyW₁, hW₁s, G, hG, hGre⟩ :=
    (R.holoOn_ev Wa.1 (a * a)).exists_log hopen hy0W (hg0 y₀ hy0W)
  have hoff : ∀ z ∈ ptsIn p σ Wa.1 ∩ {z | ¬ LiesIn z C}, f z - f' z = Real.log ‖g z‖ := by
    rintro z ⟨hz, hzC⟩
    have hzV := ptsIn_mono hWV hz
    have hzV' := ptsIn_mono hWV' hz
    have ht0 : ev p σ V.1 t z ≠ 0 := fun h0 => hzC ((ev_eq_zero_iff ht hzV).1 h0)
    have hb' : 0 < ‖ev p σ Wa.1 a z‖ := norm_pos_iff.2 (ha0 z hz)
    have ha' : 0 < ‖ev p σ V'.1 t' z‖ := by
      refine norm_pos_iff.2 fun h0 => ht0 ?_
      rw [hev z hz, h0, mul_zero]
    have e := (hn z hzV).symm.trans (hn' z hzV')
    rw [hev z hz, norm_mul, mul_pow, mul_comm (‖ev p σ Wa.1 a z‖ ^ 2), mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero 2 ha'.ne') e
    have hl := congrArg Real.log e'
    rw [Real.log_mul (pow_ne_zero 2 hb'.ne') (Real.exp_ne_zero _), Real.log_exp, Real.log_exp] at hl
    rw [hgn]
    linarith
  have hcont : ContinuousOn (fun z => f z - f' z - Real.log ‖g z‖) (ptsIn p σ Wa.1) := by
    refine (((hf.continuousOn (isOpen_ptsIn _)).mono (ptsIn_mono hWV)).sub
      ((hf'.continuousOn (isOpen_ptsIn _)).mono (ptsIn_mono hWV'))).sub ?_
    exact ((continuousOn_ev _).norm).log fun z hz => norm_ne_zero_iff.2 (hg0 z hz)
  have hall : Set.EqOn (fun z => f z - f' z - Real.log ‖g z‖) 0 (ptsIn p σ Wa.1) :=
    Set.EqOn.of_subset_closure (fun z hz => sub_eq_zero.2 (hoff z hz)) hcont continuousOn_const
      Set.inter_subset_left hclo
  refine ⟨W₁, hW₁, hyW₁, G, hG, fun z hz => ?_⟩
  rw [hGre z hz.1.1]
  exact sub_eq_zero.1 (hall (hW₁s hz.1.1))

end GlobalTheory.BdryData

namespace GlobalTheory.BdryData

variable {K : Type} [Field K] [CharZero K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {d m : ℕ}
  [SmoothOfRelativeDimension d p]
  {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

theorem isSNC_compSec (B : FinHolAtlas d (CxPts p σ)) (hB : IsAlgAtlas B) (hsnc : ∀ y : Y, LSncAt Y C y)
    (i : Fin m) : IsSNC B (compPot hn i) (compSec hn i) (Pi.single i 1) (fun k => {z | LiesIn z (C k)}) := by

  classical
  intro x
  let S : Finset (Fin m) := Finset.univ.filter fun i => LiesIn x (C i)
  have hS : ∀ i, i ∈ S ↔ LiesIn x (C i) := fun i => by simp [S]
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := d) (p := p) (σ := σ) x
  let W : Y.Opens := Finset.univ.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1
  have hWle : ∀ i, W ≤ (GlobalTheory.DivSec.eqV hn i x).1 := fun i => Finset.inf_le (Finset.mem_univ i)
  have hmemI : ∀ (z : CxPts p σ) (s : Finset (Fin m)), z ∈ ptsIn p σ (s.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1) ↔
      ∀ i ∈ s, z ∈ ptsIn p σ (GlobalTheory.DivSec.eqV hn i x).1 := by
    intro z s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]
  have hWU : ptsIn p σ W = (GlobalTheory.DivSec.divPot hn).U x := by
    ext z
    rw [hmemI z Finset.univ]
    simp only [GlobalTheory.DivSec.divPot, Set.mem_iInter, Finset.mem_univ, true_implies]
  have hxW : x ∈ ptsIn p σ W := hWU ▸ (GlobalTheory.DivSec.divPot hn).mem_U x
  let ix : Fin S.card → Fin m := fun j => (S.equivFin.symm j).1
  have hix : Function.Injective ix := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hixS : ∀ j, LiesIn x (C (ix j)) := fun j => (hS _).1 (S.equivFin.symm j).2
  let g : Fin S.card → Γ(Y, W) := fun j => resG Y (hWle (ix j)) (GlobalTheory.DivSec.eqT hn (ix j) x)
  have hgev : ∀ i z, z ∈ ptsIn p σ W →
      ev p σ W (resG Y (hWle i) (GlobalTheory.DivSec.eqT hn i x)) z = ev p σ _ (GlobalTheory.DivSec.eqT hn i x) z :=
    fun i z hz => ev_res _ hz _
  have hzero : ∀ i z, z ∈ ptsIn p σ W →
      (ev p σ _ (GlobalTheory.DivSec.eqT hn i x) z = 0 ↔ LiesIn z (C i)) := fun i z hz =>
    ev_eq_zero_iff (GlobalTheory.DivSec.eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)
  have h0 : ∀ j, ev p σ W (g j) x = 0 := fun j => by
    simp only [g]; rw [hgev _ _ hxW]; exact (hzero _ _ hxW).2 (hixS j)
  have hliA := GlobalTheory.DivSec.linearIndependent_fderiv_eqns K Y p d σ inferInstance c x hc m C (hsnc _) (fun i => GlobalTheory.DivSec.eqV hn i x)
    (fun i => GlobalTheory.DivSec.eqT hn i x) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).1) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).2.1)
  have hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev p σ W (g j) ∘ c.e.symm) (c.e x)) := by
    have h2 := hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i}))
      (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))
    convert h2 using 1
    funext j
    have e : ev p σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)]
        ev p σ _ (GlobalTheory.DivSec.eqT hn (ix j) x) ∘ c.e.symm :=
      Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
        (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2
    simp only [Function.comp_apply]
    exact e.fderiv_eq
  have hcard : S.card ≤ d := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V d) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    GlobalTheory.SncChart.exists_chart_of_fderiv K Y p d σ c x hc W hxW S.card g h0 hli
  let O : Set (CxPts p σ) := (GlobalTheory.DivSec.divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}
  have hO : IsOpen O := by
    refine ((GlobalTheory.DivSec.divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)
    by_cases h : LiesIn x (C k)
    · simp [h]
    · simpa [h] using isOpen_not_liesIn (p := p) (σ := σ) (C k)
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  have hψa : ∀ z, ψ z = e z := fun z => rfl
  have hψW : ∀ z ∈ ψ.source, z ∈ ptsIn p σ W := fun z hz => hsub (hψs ▸ hz).1
  have hψO : ∀ z ∈ ψ.source, z ∈ O := fun z hz => (hψs ▸ hz).2
  have hcompat : IsCompatChart B ψ := by
    refine GlobalTheory.DivSec.isCompatChart_of_holAlong K Y p σ d B hB ψ (fun j => ?_) ?_
    · intro V _ _ _ B' y hB' hy hm
      exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
    · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1
  let pos : ∀ k, LiesIn x (C k) → Fin d := fun k hk =>
    ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩
  let τ : Fin m → Option (Fin d) := fun k => if hk : LiesIn x (C k) then some (pos k hk) else none
  have hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev p σ _ (GlobalTheory.DivSec.eqT hn k x) z := by
    intro k hk z hz
    rw [hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]
    have hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩ := rfl
    have hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k := by simp [ix]
    rw [hj]
    simp only [g]
    rw [hgev _ _ (hψW z hz)]
    rw [hk']
  refine ⟨ψ, hcompat, hψs ▸ ⟨hx0, (GlobalTheory.DivSec.divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩,
    fun z hz => (hψO z hz).1, τ, ?_, ?_, ?_⟩
  · by_cases h : LiesIn x (C k)
    · exact Or.inl h
    · exact Or.inr h
  · intro k k' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with hk hk'
    have := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩ := Fin.ext (by simpa [pos] using congrArg Fin.val this)
    exact congrArg Subtype.val (S.equivFin.injective h3)
  · intro k
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]
    constructor
    · rintro ⟨hzk, hz⟩
      refine ⟨hz, ?_⟩
      by_cases hk : LiesIn x (C k)
      · refine ⟨pos k hk, by simp [hk], ?_⟩
        rw [hτ k hk z hz]
        exact (hzero k z (hψW z hz)).2 hzk
      · exact absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)
    · rintro ⟨hz, i, hi, h0⟩
      refine ⟨?_, hz⟩
      by_cases hk : LiesIn x (C k)
      · simp only [hk, dite_true, Option.some.injEq] at hi
        subst hi
        rw [hτ k hk z hz] at h0
        exact (hzero k z (hψW z hz)).1 h0
      · simp [hk] at hi
  · by_cases hi : LiesIn x (C i)
    · refine ⟨fun _ => 1, fun j => by exact analyticOnNhd_const, fun _ _ => one_ne_zero, fun z hz => ?_⟩
      show compSec hn i x z = 1 * _
      rw [one_mul, Finset.prod_eq_single i (fun k _ hk => by simp only [τ]; split_ifs <;> simp [Pi.single_apply, hk]) (by simp)]
      simp only [τ, hi, dite_true, Pi.single_eq_same, pow_one]
      exact (hτ i hi z hz).symm
    · refine ⟨fun z => ev p σ _ (GlobalTheory.DivSec.eqT hn i x) z, ?_, fun z hz h => ?_, fun z hz => ?_⟩
      · refine (hB.holoOn_iff R ψ.open_source).2 fun j => ?_
        exact (R.holoOn_ev _ (GlobalTheory.DivSec.eqT hn i x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle i) (hψW _ hv.2)⟩
      · exact (Set.mem_iInter.1 (hψO z hz).2 i).resolve_left hi ((hzero i z (hψW z hz)).1 h)
      · rw [Finset.prod_eq_one fun k _ => ?_, mul_one]
        · rfl
        · by_cases hk : k = i
          · subst hk; simp only [τ, hi, dite_false]
          · simp only [τ]; split_ifs <;> simp [Pi.single_apply, hk]

end GlobalTheory.BdryData

namespace GlobalTheory.BdryData

variable {K : Type} [Field K] [CharZero K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {d m : ℕ}
  [SmoothOfRelativeDimension d p]
  {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

include hn in

theorem dense_not_liesIn (B : FinHolAtlas d (CxPts p σ)) (hB : IsAlgAtlas B) (hsnc : ∀ y : Y, LSncAt Y C y)
    (i : Fin m) : Dense {z : CxPts p σ | ¬ LiesIn z (C i)} := by
  intro x
  rw [mem_closure_iff]
  intro o ho hxo
  by_cases hx : LiesIn x (C i)
  swap
  · exact ⟨x, hxo, hx⟩
  obtain ⟨ψ, -, hxs, -, τ, -, hW, -⟩ := isSNC_compSec hn B hB hsnc i x
  obtain ⟨-, j, hj, -⟩ := (Set.ext_iff.1 (hW i) x).1 ⟨hx, hxs⟩
  have hT : IsOpen (ψ '' (ψ.source ∩ o)) := ψ.isOpen_image_source_inter ho
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hT (ψ x) ⟨x, ⟨hxs, hxo⟩, rfl⟩
  let v : Fin d → ℂ := ψ x + Pi.single j ((ε / 2 : ℝ) : ℂ)
  have hv : v ∈ Metric.ball (ψ x) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [v, add_sub_cancel_left]
    refine (pi_norm_lt_iff hε).2 fun l => ?_
    by_cases hl : l = j
    · subst hl
      simp only [Pi.single_eq_same, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      linarith
    · simp [Pi.single_eq_of_ne hl, hε]
  obtain ⟨z, ⟨hzs, hzo⟩, hzv⟩ := hball hv
  refine ⟨z, hzo, fun hz => ?_⟩
  obtain ⟨-, j', hj', h0⟩ := (Set.ext_iff.1 (hW i) z).1 ⟨hz, hzs⟩
  have hjj : j' = j := Option.some.inj (hj'.symm.trans hj)
  subst hjj
  have : ψ z j' = ψ x j' + ((ε / 2 : ℝ) : ℂ) := by rw [hzv]; simp [v]
  have hx0 : ψ x j' = 0 := by
    obtain ⟨-, j'', hj'', h0'⟩ := (Set.ext_iff.1 (hW i) x).1 ⟨hx, hxs⟩
    have : j'' = j' := Option.some.inj (hj''.symm.trans hj')
    subst this; exact h0'
  rw [h0, hx0, zero_add] at this
  have := congrArg Complex.re this
  simp at this
  linarith

end GlobalTheory.BdryData

namespace GlobalTheory.BdryData

variable {K : Type} [Field K] [CharZero K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {d m : ℕ}
  [SmoothOfRelativeDimension d p]
  {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

theorem isPotential_compPot (B : FinHolAtlas d (CxPts p σ)) (hB : IsAlgAtlas B)
    (hsnc : ∀ y : Y, LSncAt Y C y) (i : Fin m) : IsPotential B (compPot hn i) := by
  have hC := dense_not_liesIn hn B hB hsnc i
  refine ⟨fun x => (hB.smoothOn_iff R ((GlobalTheory.DivSec.divPot hn).isOpen_U x)).2 ?_, fun x x' y hy => ?_⟩
  · have h : R.SmoothOn ((GlobalTheory.DivSec.divPot hn).U x) (fun z => GlobalTheory.DivSec.eqF hn i x z / 2) := fun j =>
      (((GlobalTheory.DivSec.eq_spec hn i x).2.2.1.mono fun z hz => GlobalTheory.DivSec.mem_eqV hn hz i) j).div_const 2
    exact h
  · obtain ⟨W, hW, hyW, G, hG, he⟩ := sub_eq_re_of_eqns R (C i) (n i) _ _ _ _ _ _ hC
      (GlobalTheory.DivSec.eq_spec hn i x).2.1 (GlobalTheory.DivSec.eq_spec hn i x').2.1 (GlobalTheory.DivSec.eq_spec hn i x).2.2.1
      (GlobalTheory.DivSec.eq_spec hn i x').2.2.1 (GlobalTheory.DivSec.eq_spec hn i x).2.2.2 (GlobalTheory.DivSec.eq_spec hn i x').2.2.2 y
      ⟨GlobalTheory.DivSec.mem_eqV hn hy.1 i, GlobalTheory.DivSec.mem_eqV hn hy.2 i⟩
    refine ⟨W, hW, hyW, fun z => G z / 2, (hB.holoOn_iff R hW).2 fun j => ?_, fun z hz => ?_⟩
    · exact ((hG j).mul_const (2⁻¹ : ℂ)).congr fun v _ => by simp [div_eq_mul_inv]
    · have h := he z ⟨⟨hz.1.1, GlobalTheory.DivSec.mem_eqV hn hz.1.2 i⟩, GlobalTheory.DivSec.mem_eqV hn hz.2 i⟩
      simp only [compPot]
      rw [← sub_div, h, Complex.div_ofNat_re]

theorem isBoundary_compSec (B : FinHolAtlas d (CxPts p σ)) (hB : IsAlgAtlas B)
    (hsnc : ∀ y : Y, LSncAt Y C y) :
    GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary B (compPot hn) (compSec hn) (fun i => {z | LiesIn z (C i)}) ∧
      ∀ i y, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec (compPot hn i) (compSec hn i) y = n i y := by
  have hnorm : ∀ i y, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec (compPot hn i) (compSec hn i) y = n i y := fun i y => by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec]
    exact norm_compSec_mul hn ((GlobalTheory.DivSec.divPot hn).mem_U y)
  refine ⟨fun i => ⟨isPotential_compPot hn B hB hsnc i, isSection_compSec hn hB i, isSNC_compSec hn B hB hsnc i,
    fun y => ?_⟩, hnorm⟩
  rw [hnorm]
  exact ((hn i).1 y).2

end GlobalTheory.BdryData

theorem GlobalTheory.BdryData.exists_boundaryData : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)], ∃ (Λ : Fin x.m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin x.m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary (manifold s.T.Z σ).finAtlas Λ sg (fun i => {y | LiesIn y (x.cpt i)}) ∧ ∀ i y, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec (Λ i) (sg i) y = x.nrm σ i y := by
  intro D A N j S κ s x σ _
  have : Smooth (genStr s.T.Z) := SmoothOfRelativeDimension.smooth S.Dw.dim _
  have : IsLocallyNoetherian (gen s.T.Z : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian (genStr s.T.Z)
  have := isProper_genStr s.T.Z
  have : CompactSpace (gen s.T.Z : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (genStr s.T.Z)
  have : IsNoetherian (gen s.T.Z : Scheme.{0}) := {}
  have hsnc : ∀ y : (gen s.T.Z : Scheme.{0}), LSncAt _ x.cpt y := GlobalTheory.T.snc_components_local_snc _ _ _ _ s.T.snc x.cpt_list
  exact ⟨GlobalTheory.BdryData.compPot (x.nrm_div σ), GlobalTheory.BdryData.compSec (x.nrm_div σ),
    GlobalTheory.BdryData.isBoundary_compSec (x.nrm_div σ) _ (AnRead.isAlgAtlas_finAtlas _) hsnc⟩
