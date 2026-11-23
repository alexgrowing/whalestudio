import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshOfLocallyIsPsh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCompAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCongrOn
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open ReciprocityTheory.AnForm.M

namespace GlobalTheory.QuasiPshTransfer

open GlobalTheory.Published (IsPshExt)

theorem isPshExt_congr {d : ℕ} {U : Set (Fin d → ℂ)} {v w : (Fin d → ℂ) → EReal}
    (h : IsPshExt U v) (e : ∀ z ∈ U, v z = w z) : IsPshExt U w := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : {z ∈ U | w z ≠ ⊥} = {z ∈ U | v z ≠ ⊥} :=
    Set.ext fun z => and_congr_right fun hz => by rw [e z hz]
  refine ⟨fun z hz => (e z hz) ▸ h1 z hz, fun z hz => ?_, hs ▸ h3, fun κ => ?_⟩
  · exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq (f := v) (g := w) (h2 z hz) hz
      (eventually_nhdsWithin_of_forall e)
  · exact GlobalTheory.isPsh_congr_on d U _ _ (h4 κ) fun z hz => by rw [e z hz]

theorem isPshExt_of_local {d : ℕ} {U : Set (Fin d → ℂ)} {v : (Fin d → ℂ) → EReal} (hU : IsOpen U)
    (h : ∀ z ∈ U, ∃ V : Set (Fin d → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ IsPshExt V v) :
    IsPshExt U v := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun κ => ?_⟩
  · obtain ⟨V, -, hz', -, hV⟩ := h z hz
    exact hV.1 z hz'
  · obtain ⟨V, hVo, hz', -, hV⟩ := h z hz
    have hat : UpperSemicontinuousAt v z := fun y hy => by
      have := hV.2.1 z hz' y hy
      rwa [nhdsWithin_eq_nhds.2 (hVo.mem_nhds hz')] at this
    exact hat.upperSemicontinuousWithinAt U
  · obtain ⟨V, -, hz', hVU, hV⟩ := h z hz
    exact closure_mono (s := {z ∈ V | v z ≠ ⊥}) (t := {z ∈ U | v z ≠ ⊥})
      (fun y hy => ⟨hVU hy.1, hy.2⟩) (hV.2.2.1 hz')
  · exact GlobalTheory.PshLocal.isPsh_of_local d U _ hU fun z hz => by
      obtain ⟨V, hVo, hz', -, hV⟩ := h z hz
      exact ⟨V, hVo, hz', hV.2.2.2 κ⟩

end GlobalTheory.QuasiPshTransfer

namespace GlobalTheory.QuasiPshTransfer

open GlobalTheory.Published (IsPshExt)
open ReciprocityTheory.AnForm.A (IsPsh isPsh_iff_isLeviPsh_thm isPsh_sup_thm)

theorem isPsh_mono {d : ℕ} {U V : Set (Fin d → ℂ)} {u : (Fin d → ℂ) → ℝ} (h : IsPsh U u) (hVU : V ⊆ U) :
    IsPsh V u :=
  ⟨h.1.mono hVU, fun z w hd => h.2 z w fun ζ hζ => hVU (hd ζ hζ)⟩

theorem isPsh_max_const {d : ℕ} {U : Set (Fin d → ℂ)} {u : (Fin d → ℂ) → ℝ} (hU : IsOpen U)
    (h : IsPsh U u) (c : ℝ) : IsPsh U fun z => max (u z) c := by
  have hc : IsPsh U fun _ => c := ⟨upperSemicontinuousOn_const, fun z w _ =>
    ⟨circleIntegrable_const _ _ _, by rw [Real.circleAverage_const]⟩⟩
  have := isPsh_sup_thm d Bool U (fun b => if b then u else fun _ => c) hU (by
    rintro (_ | _)
    · simpa using hc
    · simpa using h)
  refine GlobalTheory.isPsh_congr_on d U _ _ this fun z _ => ?_
  simp [Finset.sup'_insert, max_comm]

theorem isPsh_add_of_levi_nonneg {d : ℕ} {V : Set (Fin d → ℂ)} {t g : (Fin d → ℂ) → ℝ}
    (hV : IsOpen V) (ht : IsPsh V t) (hg : ContDiffOn ℝ 2 g V)
    (hl : ∀ z ∈ V, ∀ w, 0 ≤ ReciprocityTheory.AnForm.levi g z w) : IsPsh V fun z => t z + g z := by
  have hg1 : IsPsh V g := (isPsh_iff_isLeviPsh_thm d V g hV hg).2 ⟨hg, hl⟩
  refine ⟨ht.1.add hg1.1, fun z w hd => ?_⟩
  obtain ⟨i1, l1⟩ := ht.2 z w hd
  obtain ⟨i2, l2⟩ := hg1.2 z w hd
  refine ⟨i1.add i2, ?_⟩
  rw [show (fun ζ : ℂ => t (z + ζ • w) + g (z + ζ • w)) =
    (fun ζ : ℂ => t (z + ζ • w)) + (fun ζ : ℂ => g (z + ζ • w)) from rfl, Real.circleAverage_add i1 i2]
  linarith

theorem isPshExt_add_of_levi_nonneg {d : ℕ} {V : Set (Fin d → ℂ)} {v : (Fin d → ℂ) → EReal}
    {g : (Fin d → ℂ) → ℝ} (hV : IsOpen V) (hv : IsPshExt V v) (hg : ContDiffOn ℝ 2 g V)
    (hl : ∀ z ∈ V, ∀ w, 0 ≤ ReciprocityTheory.AnForm.levi g z w) :
    IsPshExt V fun z => (g z : EReal) + v z := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hg1 : IsPsh V g := (isPsh_iff_isLeviPsh_thm d V g hV hg).2 ⟨hg, hl⟩
  have hgc : ContinuousOn g V := hg.continuousOn
  have hs : {z ∈ V | (g z : EReal) + v z ≠ ⊥} = {z ∈ V | v z ≠ ⊥} :=
    Set.ext fun z => and_congr_right fun _ => by simp [EReal.add_eq_bot_iff]
  refine ⟨fun z hz => (EReal.add_lt_top (EReal.coe_ne_top _) (h1 z hz)).ne, ?_, hs ▸ h3, fun κ => ?_⟩
  · exact UpperSemicontinuousOn.add'
      (continuous_coe_real_ereal.comp_upperSemicontinuousOn hg1.1 EReal.coe_strictMono.monotone) h2
      fun z _ => EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  refine GlobalTheory.PshLocal.isPsh_of_local d V _ hV fun z hz => ?_
  set B := V ∩ g ⁻¹' Set.Iio (g z + 1) with hB
  have hBo : IsOpen B := hgc.isOpen_inter_preimage hV isOpen_Iio
  have hBV : B ⊆ V := Set.inter_subset_left
  set κ' := κ + g z + 1 with hκ'
  have hT := isPsh_max_const hBo (isPsh_add_of_levi_nonneg hBo (isPsh_mono (h4 κ') hBV) (hg.mono hBV)
    fun z' hz' w => hl z' (hBV hz') w) (-κ)
  refine ⟨B, hBo, ⟨hz, by simp⟩, GlobalTheory.isPsh_congr_on d B _ _ hT fun z' hz' => ?_⟩
  have hlt : g z' < g z + 1 := hz'.2
  have htop := h1 z' (hBV hz')
  show max ((max (v z') ((-κ' : ℝ) : EReal)).toReal + g z') (-κ) =
    (max ((g z' : EReal) + v z') ((-κ : ℝ) : EReal)).toReal
  generalize v z' = t at htop ⊢
  induction t using EReal.rec with
  | bot => simp <;> linarith
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_strictMono.monotone.map_max, ← EReal.coe_strictMono.monotone.map_max,
      EReal.toReal_coe, EReal.toReal_coe]
    rcases le_total (-κ') r with hr | hr
    · rw [max_eq_left hr, add_comm]
    · rw [max_eq_right hr, max_eq_right (by linarith), max_eq_right (by linarith)]
  | top => exact absurd rfl htop

theorem isPshExt_comp {D D' : ℕ} {U : Set (Fin D → ℂ)} {V : Set (Fin D' → ℂ)}
    {v : (Fin D → ℂ) → EReal} {h : (Fin D' → ℂ) → (Fin D → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hv : IsPshExt U v) (hh : AnalyticOnNhd ℂ h V) (hm : Set.MapsTo h V U)
    (ho : ∀ N ⊆ V, IsOpen N → IsOpen (h '' N)) : IsPshExt V (v ∘ h) := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hc : ContinuousOn h V := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  refine ⟨fun z hz => h1 _ (hm hz), h2.comp hc hm, fun z hz => ?_, fun κ =>
    GlobalTheory.PshPullback.isPsh_comp D D' U V _ h hU hV (h4 κ) hh hm⟩
  rw [mem_closure_iff]
  intro o hoo hzo
  obtain ⟨_, ⟨z', hz', rfl⟩, -, hne⟩ := mem_closure_iff.1 (h3 (hm hz)) _
    (ho _ Set.inter_subset_right (hoo.inter hV)) ⟨z, ⟨hzo, hz⟩, rfl⟩
  exact ⟨z', hz'.1, hz'.2, hne⟩

end GlobalTheory.QuasiPshTransfer

namespace GlobalTheory.QuasiPshTransfer
open GlobalTheory.Published (IsPshExt)

theorem isFormPsh_of_isQuasiPsh : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y), Y.dim = e → ∀ (a : Fin (M.n + 1)) (Θ : LocPot (M.X a)) (θ : ChartForm Y.str (I.ε a) Y.dim) (v : M.X a → EReal), IsPotential (M.A a) Θ → (∀ x, GlobalTheory.ShFam.IsPotential (AnRead.all Y.str (I.ε a) Y.dim) θ (I.pt a '' Θ.U x) (fun y => 2 * Θ.φ x ((I.pt a).symm y))) → GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsQuasiPsh (M.A a) Θ v → GlobalTheory.Published.IsFormPsh (AnRead.all Y.str (I.ε a) Y.dim) θ (v ∘ (I.pt a).symm) := by
  intro F _ _ Y e M I he a Θ θ v _ hθ hv
  subst he
  intro W φ hφ c
  refine isPshExt_of_local (c.finChart.isOpen_inter_preimage_symm hφ.1) fun z₀ hz₀ => ?_
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm (c.finChart.symm z₀))
  set x := (I.pt a).symm (c.finChart.symm z₀) with hx
  obtain ⟨c', hc'⟩ := I.alg a j
  have hsrc : ((M.A a).chart j).source = I.pt a ⁻¹' c'.finChart.source := by
    rw [hc', Homeomorph.transOpenPartialHomeomorph_source]
  have htgt : ((M.A a).chart j).target = c'.finChart.target := by
    rw [hc', Homeomorph.transOpenPartialHomeomorph_target]
  have hsymm : ∀ ζ, ((M.A a).chart j).symm ζ = (I.pt a).symm (c'.finChart.symm ζ) := fun ζ => by
    rw [hc', Homeomorph.transOpenPartialHomeomorph_symm_apply]; rfl
  set S := W ∩ I.pt a '' (Θ.U x ∩ ((M.A a).chart j).source) with hS
  have hSo : IsOpen S := hφ.1.inter ((I.pt a).isOpenMap _ ((Θ.isOpen_U x).inter ((M.A a).chart j).open_source))
  have hy₀S : c.finChart.symm z₀ ∈ S := ⟨hz₀.2, x, ⟨Θ.mem_U x, hj⟩, (I.pt a).apply_symm_apply _⟩
  set V := c.finChart.target ∩ c.finChart.symm ⁻¹' S with hV
  have hVo : IsOpen V := c.finChart.isOpen_inter_preimage_symm hSo
  refine ⟨V, hVo, ⟨hz₀.1, hy₀S⟩, fun z hz => ⟨hz.1, hz.2.1⟩, ?_⟩

  have hmem : ∀ z ∈ V, c.finChart.symm z ∈ c'.finChart.source ∧
      (I.pt a).symm (c.finChart.symm z) ∈ Θ.U x ∧ c.finChart.symm z ∈ I.pt a '' Θ.U x := by
    rintro z ⟨-, -, x', ⟨hx'U, hx's⟩, e⟩
    rw [hsrc] at hx's
    refine ⟨e ▸ hx's, ?_, ⟨x', hx'U, e⟩⟩
    rw [← e, Homeomorph.symm_apply_apply]
    exact hx'U
  set ψ : CxPts Y.str (I.ε a) → ℝ := fun y => 2 * Θ.φ x ((I.pt a).symm y) with hψ
  have hψp := hθ x
  set G : CxPts Y.str (I.ε a) → ℝ := fun y => φ y + (-1) * ψ y with hG
  set h := c'.finChart ∘ c.finChart.symm with hh
  set U := GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.chartPart (M.A a) j (Θ.U x) with hU
  have hUo : IsOpen U := ((M.A a).chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)
  have hsh : ∀ z ∈ V, ((M.A a).chart j).symm (h z) = (I.pt a).symm (c.finChart.symm z) := fun z hz => by
    rw [hsymm, hh, Function.comp_apply, c'.finChart.left_inv (hmem z hz).1]

  have h1 : IsPshExt V ((fun ζ => ((2 * Θ.φ x (((M.A a).chart j).symm ζ) : ℝ) : EReal) +
      v (((M.A a).chart j).symm ζ)) ∘ h) := by
    refine isPshExt_comp (U := U) (V := V) (h := h) hUo hVo (hv x j) ?_ ?_ ?_
    · exact (c.analyticOnNhd_trans c').mono fun z hz => ⟨hz.1, (hmem z hz).1⟩
    · intro z hz
      refine ⟨?_, ?_⟩
      · rw [htgt]; exact c'.finChart.map_source (hmem z hz).1
      · show ((M.A a).chart j).symm (h z) ∈ Θ.U x
        rw [hsh z hz]; exact (hmem z hz).2.1
    · intro N hNV hNo
      rw [hh, Set.image_comp]
      refine c'.finChart.isOpen_image_of_subset_source
        (c.finChart.symm.isOpen_image_of_subset_source hNo fun z hz => (hNV hz).1) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact (hmem z (hNV hz)).1

  have hφc : ContDiffOn ℝ 2 (φ ∘ c.finChart.symm) V :=
    (((c.contDiffOn_finChart_iff _ W _).2 (hφ.2.1.chart hφ.1 c)).of_le
      (WithTop.coe_le_coe.2 le_top)).mono fun z hz => ⟨hz.1, hz.2.1⟩
  have hψc : ContDiffOn ℝ 2 (ψ ∘ c.finChart.symm) V :=
    (((c.contDiffOn_finChart_iff _ _ _).2 (hψp.2.1.chart hψp.1 c)).of_le
      (WithTop.coe_le_coe.2 le_top)).mono fun z hz => ⟨hz.1, (hmem z hz).2.2⟩
  have hGc : ContDiffOn ℝ 2 (G ∘ c.finChart.symm) V := hφc.add (contDiffOn_const.mul hψc)
  have hlevi : ∀ z ∈ V, ∀ w, ReciprocityTheory.AnForm.levi (G ∘ c.finChart.symm) z w = 0 := by
    intro z hz w
    have hy : c.finChart.symm z ∈ c.e.source := c.finChart.map_target hz.1
    have hyW : c.finChart.symm z ∈ W := hz.2.1
    have hyψ := (hmem z hz).2.2
    have e1 := hφ.2.2 c _ hy hyW w
    have e2 := hψp.2.2 c _ hy hyψ w
    have hφa := hφ.2.1.contDiffAt_two hφ.1 hy hyW
    have hψa := hψp.2.1.contDiffAt_two hψp.1 hy hyψ
    have hGa : ContDiffAt ℝ 2 (G ∘ c.e.symm) (c.e (c.finChart.symm z)) := hφa.add (contDiffAt_const.mul hψa)
    have e3 := c.leviV_re_eq hGa w
    rw [c.finChart.right_inv hz.1] at e3
    rw [← e3]
    change c.levi G (c.finChart.symm z) w = 0
    rw [hG, AlgChart.levi_add hφa (contDiffAt_const.mul hψa), AlgChart.levi_const_mul _ hψa]
    rw [ddcForm] at e1 e2
    have : c.levi φ (c.finChart.symm z) w = c.levi ψ (c.finChart.symm z) w := by
      have := e1.symm.trans e2
      field_simp at this
      exact this
    rw [this]; ring
  have h2 := isPshExt_add_of_levi_nonneg hVo h1 hGc fun z hz w => (hlevi z hz w).ge
  refine isPshExt_congr h2 fun z hz => ?_
  simp only [Function.comp_apply]
  rw [hsh z hz, ← add_assoc, ← EReal.coe_add]
  congr 2
  simp only [hG, hψ]
  ring

end GlobalTheory.QuasiPshTransfer
