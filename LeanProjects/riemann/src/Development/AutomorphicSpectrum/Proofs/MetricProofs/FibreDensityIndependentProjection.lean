import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
open ReciprocityTheory.AnForm.R (conePts)

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

def BlockNonzero (S : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0

def ScaleStable (S : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ S, (fun p => c p.1 * z p) ∈ S

variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem setSheet_analyticAt {S : Set ((Σ k, ι k) → ℂ)} {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hc : IsSetSheet S Ψ y w γ) : AnalyticAt ℂ γ y := by
  obtain ⟨V, hVs, hV, hy⟩ := mem_nhds_iff.mp hc.2
  exact analyticOnNhd_of_diffOn hV (fun y' hy' => (hVs hy').1) y hy

theorem exists_local_set {S : Set ((Σ k, ι k) → ℂ)} {w₀ : ((k : K) → ι k) → ℂ} (h : cxSimple S Ψ w₀) :
    ∃ (y₀ : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ))
      (N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))),
      IsOpen U ∧ IsOpen N ∧ (y₀, w₀) ∈ N ∧ segre (γ y₀) = w₀ ∧
      (∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧ Ψ (segre (γ y)) = Fin.cons 1 y) ∧
      ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)) := by
  obtain ⟨y₀, γ, hsh, hev⟩ := h
  obtain ⟨U, hUs, hU, hy₀⟩ := mem_nhds_iff.mp hsh.2
  obtain ⟨N₁, hN₁s, hN₁, hq₁⟩ := mem_nhds_iff.mp hev
  exact ⟨y₀, γ, U, N₁ ∩ U ×ˢ Set.univ, hU, hN₁.inter (hU.prod isOpen_univ), ⟨hq₁, hy₀, trivial⟩,
    hsh.1, fun y hy => hUs hy, fun q hq => ⟨hq.2.1, hN₁s hq.1⟩⟩

theorem nrm_mem_setFibre {S : Set ((Σ k, ι k) → ℂ)} (hSs : ScaleStable S) (k0 : K)
    {z' : (Σ k, ι k) → ℂ} (hz' : z' ∈ S) (h0 : Ψ (segre z') 0 ≠ 0) :
    nrm Ψ (segre z') ∈ setFibre S Ψ (crd Ψ (segre z')) := by
  classical
  set c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z') 0)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h0]
    · simp [hcdef, Function.update_of_ne hk]
  have hprod : ∏ k, c k = (Ψ (segre z') 0)⁻¹ := by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * z' p, hSs c hc _ hz', ?_, map_nrm h0⟩
  rw [segre_smul, hprod]
  rfl

theorem setSheetDensity_eq {S : Set ((Σ k, ι k) → ℂ)} (hS0 : BlockNonzero S) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {G : ((Σ k, ι k) → ℂ) → ℝ}
    (hG : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → G (fun p => c p.1 * z p) = G z)
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hq : (y, w) ∈ N) (hw : w ∈ setFibre S Ψ y) :
    setSheetDensity S Ψ (pot L) G y w = G (γ y) * maDensity (fun j y' => pot L j (γ y')) y := by
  obtain ⟨hyU, hw'⟩ := hNp _ hq
  have hw1 : w = segre (γ y) := hw' hw
  have hsh : IsSetSheet S Ψ y w γ := ⟨hw1.symm, Filter.eventually_of_mem (hU.mem_nhds hyU) hγ⟩
  have hex : ∃ γ', IsSetSheet S Ψ y w γ' := ⟨γ, hsh⟩
  have han : AnalyticOnNhd ℂ γ U := analyticOnNhd_of_diffOn hU fun y hy => (hγ y hy).1
  unfold setSheetDensity
  rw [dif_pos hex]
  have hc := hex.choose_spec
  set γc := hex.choose
  have hcont : ContinuousAt (fun y' => (y', segre (γc y'))) y :=
    continuousAt_id.prodMk (continuous_segre.continuousAt.comp hc.2.self_of_nhds.1.continuousAt)
  have hN' : ∀ᶠ y' in 𝓝 y, (y', segre (γc y')) ∈ N :=
    hcont.eventually (hN.mem_nhds (by show (y, segre (γc y)) ∈ N; rw [hc.1]; exact hq))
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γc y') := by
    filter_upwards [hN', hc.2] with y' h1 h2
    exact ((hNp _ h1).2 ⟨γc y', h2.2.1, rfl, h2.2.2⟩).symm
  have hblk : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hS0 _ (hγ y hyU).2.1
  rw [apply_eq_of_segre_eq hG hblk (hc.1.trans hw1).symm,
    maDensity_eq_of_segre hL (han y hyU) (setSheet_analyticAt hc) hblk hseg]

theorem cxPosDens_eq {S : Set ((Σ k, ι k) → ℂ)} (hS0 : BlockNonzero S) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z)
    {E : Set ((Σ k, ι k) → ℂ)}
    (hE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z p) ∈ E ↔ z ∈ E))
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)))
    (hEN : ∀ z' ∈ E, Ψ (segre z') 0 ≠ 0 → (crd Ψ (segre z'), nrm Ψ (segre z')) ∈ N)
    (y : Fin e → ℂ) :
    cxPosDens S Ψ (pot L) (E.indicator g) y = (U ∩ γ ⁻¹' E).indicator
      (fun y => max (g (γ y) * maDensity (fun j y' => pot L j (γ y')) y) 0) y := by
  classical
  have hEg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      E.indicator g (fun p => c p.1 * z p) = E.indicator g z := by
    intro c z hc
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hE c z hc).2 hz), hg c z hc]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hE c z hc).1 h))]
  have hmemE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      ((fun p => c p.1 * z p) ∈ E) = (z ∈ E) := fun c z hc => propext (hE c z hc)

  have hnz : ∀ w ∈ setFibre S Ψ y, setSheetDensity S Ψ (pot L) (E.indicator g) y w ≠ 0 →
      (y, w) ∈ N ∧ γ y ∈ E := by
    intro w hw hne
    obtain ⟨-, -, -, hΨw⟩ := hw
    unfold setSheetDensity at hne
    split_ifs at hne with h
    · have hc := h.choose_spec
      have hcE : h.choose y ∈ E := by
        by_contra hn
        exact hne (by rw [Set.indicator_of_notMem hn, zero_mul])
      have hw0 : Ψ (segre (h.choose y)) 0 ≠ 0 := by
        rw [hc.1, hΨw]; simp
      have hqN := hEN _ hcE hw0
      rw [hc.1, crd_of_eq hΨw, nrm_of_eq hΨw] at hqN
      refine ⟨hqN, ?_⟩
      obtain ⟨hyU, hw1⟩ := hNp _ hqN
      have hseg : segre (h.choose y) = segre (γ y) := hc.1.trans (hw1 ⟨h.choose y, hc.2.self_of_nhds.2.1, hc.1, hΨw⟩)
      have := apply_eq_of_segre_eq hmemE (hS0 _ hc.2.self_of_nhds.2.1) hseg
      rw [this]
      exact hcE
    · exact absurd rfl hne
  unfold cxPosDens
  by_cases hy : y ∈ U ∩ γ ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hyU := hy.1
    have hΨ1 : Ψ (segre (γ y)) = Fin.cons 1 y := (hγ y hyU).2.2
    have hfib : segre (γ y) ∈ setFibre S Ψ y := ⟨γ y, (hγ y hyU).2.1, rfl, hΨ1⟩
    have hqN : (y, segre (γ y)) ∈ N := by
      have h := hEN _ hy.2 (by rw [hΨ1]; simp)
      rwa [crd_of_eq hΨ1, nrm_of_eq hΨ1] at h
    rw [finsum_eq_single _ (segre (γ y)) ?_, finsum_eq_if, if_pos hfib,
      setSheetDensity_eq hS0 hL hEg hU hγ hN hNp hqN hfib, Set.indicator_of_mem (show γ y ∈ E from hy.2)]
    intro w hne
    rw [finsum_eq_if]
    split_ifs with hw
    · by_cases h0 : setSheetDensity S Ψ (pot L) (E.indicator g) y w = 0
      · rw [h0, max_self]
      · exact absurd ((hNp _ (hnz w hw h0).1).2 hw) hne
    · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    by_cases h0 : setSheetDensity S Ψ (pot L) (E.indicator g) y w = 0
    · rw [h0, max_self]
    · obtain ⟨hqN, hγE⟩ := hnz w hw h0
      exact absurd ⟨(hNp _ hqN).1, hγE⟩ hy

theorem posPart_local_set {S : Set ((Σ k, ι k) → ℂ)} (hS0 : BlockNonzero S) (hSs : ScaleStable S) (k0 : K)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (hL : ∀ j, IsSmoothHerm (L j))
    (hg : ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z')
    (hs : cxSimple S Ψ ((Ψ (segre z) 0)⁻¹ • segre z))
    (hs' : cxSimple S Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z)) :
    ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
      (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
      ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
        E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (cxPosDens S Ψ (pot L) (E.indicator g) y) =
            ∫⁻ y, ENNReal.ofReal (cxPosDens S Ψ' (pot L) (E.indicator g) y) := by
  obtain ⟨y₀, γ₀, U, N, hU, hN, hq₀, hseg₀, hγ₀, hNp⟩ := exists_local_set hs
  obtain ⟨y₀', γ₀', U', N', hU', hN', hq₀', hseg₀', hγ₀', hNp'⟩ := exists_local_set hs'

  have hz0 : Ψ (segre z) 0 ≠ 0 := by
    intro h0
    have h := congrFun (hγ₀ y₀ (hNp _ hq₀).1).2.2 0
    rw [hseg₀, h0, inv_zero, zero_smul, map_zero] at h
    simp at h
  have hz0' : Ψ' (segre z) 0 ≠ 0 := by
    intro h0
    have h := congrFun (hγ₀' y₀' (hNp' _ hq₀').1).2.2 0
    rw [hseg₀', h0, inv_zero, zero_smul, map_zero] at h
    simp at h
  have hN0 : (crd Ψ (segre z), nrm Ψ (segre z)) ∈ N := by
    have h1 : Ψ (nrm Ψ (segre z)) = Fin.cons 1 y₀ := by
      rw [← (hγ₀ y₀ (hNp _ hq₀).1).2.2, hseg₀]
      rfl
    have h2 : crd Ψ (segre z) = y₀ := by
      funext i
      simp [crd, h1]
    rw [h2]
    exact hq₀
  have hN0' : (crd Ψ' (segre z), nrm Ψ' (segre z)) ∈ N' := by
    have h1 : Ψ' (nrm Ψ' (segre z)) = Fin.cons 1 y₀' := by
      rw [← (hγ₀' y₀' (hNp' _ hq₀').1).2.2, hseg₀']
      rfl
    have h2 : crd Ψ' (segre z) = y₀' := by
      funext i
      simp [crd, h1]
    rw [h2]
    exact hq₀'

  set WS : Set (((k : K) → ι k) → ℂ) := {w | Ψ w 0 ≠ 0 ∧ Ψ' w 0 ≠ 0 ∧ (crd Ψ w, nrm Ψ w) ∈ N ∧
    (crd Ψ' w, nrm Ψ' w) ∈ N'} with hWSdef
  have hWS : IsOpen WS := by
    refine isOpen_iff_mem_nhds.mpr fun w hw => ?_
    have c0 : ContinuousAt (fun w => Ψ w 0) w := (differentiableAt_coord w 0).continuousAt
    have c0' : ContinuousAt (fun w => Ψ' w 0) w := (differentiableAt_coord w 0).continuousAt
    filter_upwards [c0.eventually_ne hw.1, c0'.eventually_ne hw.2.1,
      ((continuousAt_crd hw.1).prodMk (continuousAt_nrm hw.1)).eventually (hN.mem_nhds hw.2.2.1),
      ((continuousAt_crd hw.2.1).prodMk (continuousAt_nrm hw.2.1)).eventually (hN'.mem_nhds hw.2.2.2)]
      with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hWSs : ∀ t : ℂ, t ≠ 0 → ∀ w, t • w ∈ WS ↔ w ∈ WS := by
    intro t ht w
    have e1 : ∀ Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), Φ (t • w) 0 ≠ 0 ↔ Φ w 0 ≠ 0 :=
      fun Φ => by simp [map_smul, ht]
    simp only [hWSdef, Set.mem_setOf_eq, e1, crd_smul ht, nrm_smul ht]
  refine ⟨segre ⁻¹' WS, hWS.preimage continuous_segre, ⟨hz0, hz0', hN0, hN0'⟩,
    fun c z' hc => ?_, fun E _ hE hEW => ?_⟩
  · show segre (fun p => c p.1 * z' p) ∈ WS ↔ segre z' ∈ WS
    rw [segre_smul]
    exact hWSs _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k) _

  have hl : ∀ y, cxPosDens S Ψ (pot L) (E.indicator g) y = (U ∩ γ₀ ⁻¹' E).indicator
      (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) y :=
    cxPosDens_eq hS0 hL hg hE hU hγ₀ hN hNp fun z' hz' _ => (hEW hz').2.2.1
  have hl' : ∀ y, cxPosDens S Ψ' (pot L) (E.indicator g) y = (U' ∩ γ₀' ⁻¹' E).indicator
      (fun y => max (g (γ₀' y) * maDensity (fun j y' => pot L j (γ₀' y')) y) 0) y :=
    cxPosDens_eq hS0 hL hg hE hU' hγ₀' hN' hNp' fun z' hz' _ => (hEW hz').2.2.2
  simp_rw [hl, hl']

  have hγ₀an : AnalyticOnNhd ℂ γ₀ U := analyticOnNhd_of_diffOn hU fun y hy => (hγ₀ y hy).1
  have hγ₀'an : AnalyticOnNhd ℂ γ₀' U' := analyticOnNhd_of_diffOn hU' fun y hy => (hγ₀' y hy).1
  set Φ : (Fin e → ℂ) → Fin (e + 1) → ℂ := fun y => Ψ (segre (γ₀' y)) with hΦdef
  have hΦan : AnalyticOnNhd ℂ Φ U' := analyticOnNhd_of_diffOn hU' fun y hy =>
    (differentiable_map (Ψ := Ψ) _).comp y (segre_differentiableAt (hγ₀' y hy).1)
  set O' := U' ∩ γ₀' ⁻¹' (segre ⁻¹' WS) with hO'def
  have hO' : IsOpen O' := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hγ₀' y hy).1.continuousAt.continuousWithinAt) hU' (hWS.preimage continuous_segre)
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y => crd Ψ (segre (γ₀' y)) with hτdef
  have hτeq : τ = fun y (i : Fin e) => (Φ y 0)⁻¹ * Φ y i.succ := funext fun y => crd_eq _
  have hτan : AnalyticOnNhd ℂ τ O' := fun y hy => by
    rw [hτeq]
    exact analyticAt_pi_iff.mpr fun i =>
      (AnalyticAt.inv (f := fun y => Φ y 0) (analyticAt_pi_iff.mp (hΦan y hy.1) 0) hy.2.1).mul
        (analyticAt_pi_iff.mp (hΦan y hy.1) i.succ)
  have hτU : ∀ y ∈ O', τ y ∈ U ∧ segre (γ₀ (τ y)) = nrm Ψ (segre (γ₀' y)) := fun y hy => by
    have hq : (τ y, nrm Ψ (segre (γ₀' y))) ∈ N := hy.2.2.2.1
    obtain ⟨h1, h2⟩ := hNp _ hq
    exact ⟨h1, (h2 (nrm_mem_setFibre hSs k0 (hγ₀' y hy.1).2.1 hy.2.1)).symm⟩

  set c : (Fin e → ℂ) → K → ℂ := fun y => Function.update (fun _ => (1 : ℂ)) k0 (Φ y 0)⁻¹ with hcdef
  have hc_ne : ∀ y, Φ y 0 ≠ 0 → ∀ k, c y k ≠ 0 := by
    intro y h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hprod : ∀ y, ∏ k, c y k = (Φ y 0)⁻¹ := fun y => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  set γt : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y => bsmul (c y) (γ₀' y) with hγtdef
  have hγtseg : ∀ y, segre (γt y) = nrm Ψ (segre (γ₀' y)) := fun y => by
    show segre (fun p => c y p.1 * γ₀' y p) = _
    rw [segre_smul, hprod]
    rfl

  have hcmp : ∀ y ∈ O', (γ₀ (τ y) ∈ E ↔ γ₀' y ∈ E) ∧ g (γ₀ (τ y)) = g (γ₀' y) ∧
      maDensity (fun j y' => pot L j (γ₀' y')) y =
        maDensity (fun j y' => pot L j (γ₀ y')) (τ y) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det := by
    intro y hy
    obtain ⟨hτy, hsy⟩ := hτU y hy
    have hblk : ∀ k, ∃ i, γ₀ (τ y) ⟨k, i⟩ ≠ 0 := hS0 _ (hγ₀ _ hτy).2.1
    have hseg : segre (γ₀ (τ y)) = segre (γt y) := hsy.trans (hγtseg y).symm
    have hy0 : Φ y 0 ≠ 0 := hy.2.1
    have hmemE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
        ((fun p => c p.1 * z p) ∈ E) = (z ∈ E) := fun c z hc => propext (hE c z hc)
    have hE1 : (γt y ∈ E) = (γ₀ (τ y) ∈ E) := apply_eq_of_segre_eq hmemE hblk hseg
    have hE2 : (γt y ∈ E) = (γ₀' y ∈ E) := hmemE (c y) (γ₀' y) (hc_ne y hy0)
    have hg1 : g (γt y) = g (γ₀ (τ y)) := apply_eq_of_segre_eq hg hblk hseg
    have hg2 : g (γt y) = g (γ₀' y) := hg (c y) (γ₀' y) (hc_ne y hy0)
    refine ⟨by rw [← hE1, hE2], by rw [← hg1, hg2], ?_⟩
    have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := fun k => by
      by_cases hk : k = k0
      · subst hk
        simp only [hcdef, Function.update_self]
        exact AnalyticAt.inv (f := fun y => Φ y 0) (analyticAt_pi_iff.mp (hΦan y hy.1) 0) hy0
      · simp only [hcdef, Function.update_of_ne hk]
        exact analyticAt_const
    have hγ'a : AnalyticAt ℂ γ₀' y := hγ₀'an y hy.1
    have hγta : AnalyticAt ℂ γt y :=
      analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ'a p)
    have hτa : AnalyticAt ℂ τ y := hτan y hy
    have hγτa : AnalyticAt ℂ (fun y' => γ₀ (τ y')) y := (hγ₀an _ hτy).comp hτa
    have h1 : maDensity (fun j y' => pot L j (γt y')) y = maDensity (fun j y' => pot L j (γ₀' y')) y :=
      maDensity_bsmul (c := fun k y' => c y' k) hL hγ'a (hS0 _ (hγ₀' y hy.1).2.1) hca (fun k => hc_ne y hy0 k)
        (Eventually.of_forall fun y' => rfl)
    have h2 : maDensity (fun j y' => pot L j (γt y')) y =
        maDensity (fun j y' => pot L j (γ₀ (τ y'))) y :=
      maDensity_eq_of_segre hL hγτa hγta hblk (by
        filter_upwards [hO'.mem_nhds hy] with y' hy'
        exact (hτU y' hy').2.trans (hγtseg y').symm)
    have h3 : maDensity (fun j y' => pot L j (γ₀ (τ y'))) y =
        maDensity (fun j y' => pot L j (γ₀ y')) (τ y) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun j y' => pot L j (γ₀ y')) τ y hτa fun j =>
        pot_contDiffAt (hL j) (hγ₀an _ hτy) hblk
    rw [← h1, h2, h3]

  have hback : ∀ y ∈ O', y = crd Ψ' (nrm Ψ (segre (γ₀' y))) := by
    intro y hy
    have h1 : crd Ψ' (segre (γ₀' y)) = y := crd_of_eq (hγ₀' y hy.1).2.2
    have h2 := crd_smul (Ψ := Ψ') hy.2.1 (nrm Ψ (segre (γ₀' y)))
    rw [← eq_smul_nrm hy.2.1, h1] at h2
    exact h2
  have hτinj : Set.InjOn τ O' := by
    intro y₁ h₁ y₂ h₂ h
    have e₁ := (hτU y₁ h₁).2
    have e₂ := (hτU y₂ h₂).2
    rw [h] at e₁
    rw [hback y₁ h₁, hback y₂ h₂, ← e₁, ← e₂]

  have hsupp : ∀ y ∈ U ∩ γ₀ ⁻¹' E, y ∈ τ '' O' := by
    intro y hy
    have hz₁ := hγ₀ y hy.1
    have hw₁ : segre (γ₀ y) ∈ WS := hEW hy.2
    have hfib := nrm_mem_setFibre (Ψ := Ψ') hSs k0 hz₁.2.1 hw₁.2.1
    obtain ⟨hy'U, hy'seg⟩ := hNp' _ hw₁.2.2.2
    have hseg' := hy'seg hfib
    refine ⟨crd Ψ' (segre (γ₀ y)), ⟨hy'U, ?_⟩, ?_⟩
    · show segre (γ₀' (crd Ψ' (segre (γ₀ y)))) ∈ WS
      rw [← hseg']
      exact (hWSs _ (inv_ne_zero hw₁.2.1) _).2 hw₁
    · show crd Ψ (segre (γ₀' (crd Ψ' (segre (γ₀ y))))) = y
      rw [← hseg']
      show crd Ψ ((Ψ' (segre (γ₀ y)) 0)⁻¹ • segre (γ₀ y)) = y
      rw [crd_smul (inv_ne_zero hw₁.2.1)]
      exact crd_of_eq hz₁.2.2
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ γ₀ ⁻¹' E).indicator
          (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => hsupp y ?_).symm
        by_contra h
        exact hy (by simp [Set.indicator_of_notMem h])
    _ = ∫⁻ y in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det) *
          ENNReal.ofReal ((U ∩ γ₀ ⁻¹' E).indicator
            (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) (τ y)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ y in O', ENNReal.ofReal ((U' ∩ γ₀' ⁻¹' E).indicator
          (fun y => max (g (γ₀' y) * maDensity (fun j y' => pot L j (γ₀' y')) y) 0) y) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun y hy => ?_
        obtain ⟨hE', hg', hma⟩ := hcmp y hy
        by_cases hyE : γ₀' y ∈ E
        · rw [Set.indicator_of_mem (show τ y ∈ U ∩ γ₀ ⁻¹' E from ⟨(hτU y hy).1, hE'.2 hyE⟩),
            Set.indicator_of_mem (show y ∈ U' ∩ γ₀' ⁻¹' E from ⟨hy.1, hyE⟩)]
          rw [hg', hma, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (show τ y ∉ U ∩ γ₀ ⁻¹' E from fun hm => hyE (hE'.1 hm.2)),
            Set.indicator_of_notMem (show y ∉ U' ∩ γ₀' ⁻¹' E from fun hm => hyE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun y hy => ?_
        have hyE : y ∈ U' ∩ γ₀' ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        exact ⟨hyE.1, hEW hyE.2⟩

theorem cxPosPart_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ conePts Q → cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
  intro K _ ι _ Q e Ψ Ψ' L g z hQ _ _ hL _ hg _ hs hs'
  classical
  obtain ⟨k0⟩ := hQ.1
  exact posPart_local_set (fun _ hz => hz.1)
    (fun c hc z' hz' => GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.bsmul_mem_conePts hQ.2.1.2.1 hc hz') k0 hL hg hs hs'

end GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal
