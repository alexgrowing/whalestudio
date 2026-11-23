import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemMcPtsOfOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

theorem analyticAt_eval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → σ → ℂ} {w₀ : E}
    (hg : ∀ q, AnalyticAt ℂ (fun w => g w q) w₀) (f : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun w => eval (g w) f) w₀ := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    refine (hp.add hq).congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  | mul_X p n hp =>
    refine (hp.mul (hg n)).congr (Filter.Eventually.of_forall fun w => ?_)
    simp

section Overlap

variable (hP : IsMultiHomogIdeal P) (C₁ C₂ : OrbitChart P e) (x₁ x₂ : PtsOf P)
include hP

theorem mem_O_of_mem_srcOf {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) : C₁.φ w ∈ C₂.O := by
  have h' : rep (cls (C₁.φ w) (C₁.mem w hw)) ∈ C₂.O := by
    rw [← clsT_of_mem x₁ (C₁.mem w hw)]
    exact h
  exact mem_O_of_orbit C₂ hP h' (Proj.orbit_symm (rep_cls_orbit _ _)) (rep_mem_mcPts _)

theorem rho_clsT {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) :
    C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := by
  have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw h
  refine C₂.ρ_orbit _ hO _ h ?_
  rw [clsT_of_mem x₁ (C₁.mem w hw)]
  exact rep_cls_orbit _ _

theorem isOpen_overlap :
    IsOpen ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
  (orbChart hP C₁ x₁).isOpen_inter_preimage_symm (isOpen_srcOf hP C₂)

theorem analytic_transition :
    AnalyticOnNhd ℂ (orbChart hP C₂ x₂ ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' (orbChart hP C₂ x₂).source) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w))
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
    (GlobalTheory.T.orbit_chart_transition_analytic K ι P e C₁ C₂).mono fun w hw => ⟨hw.1, mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2⟩
  exact h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => (rho_clsT hP C₁ C₂ x₁ hw.1 hw.2).symm

theorem analytic_lift (p : Σ k, ι k) :
    AnalyticOnNhd ℂ ((fun y : PtsOf P => C₂.φ (C₂.ρ (rep y)) p) ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.φ (C₂.ρ (C₁.φ w)) p)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := fun w hw => by
    have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2
    exact AnalyticAt.comp (g := fun v => C₂.φ v p) (f := fun w => C₂.ρ (C₁.φ w))
      (C₂.holo p _ (C₂.ρ_mem _ hO)) (GlobalTheory.T.orbit_chart_transition_analytic K ι P e C₁ C₂ w ⟨hw.1, hO⟩)
  refine h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => ?_
  have e1 : C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := rho_clsT hP C₁ C₂ x₁ hw.1 hw.2
  show C₂.φ (C₂.ρ (C₁.φ w)) p = C₂.φ (C₂.ρ (rep (clsT x₁ (C₁.φ w)))) p
  rw [e1]

theorem immersion_lift {x : PtsOf P} (hx₂ : x ∈ srcOf C₂) (hx₁ : x ∈ srcOf C₁) (p : (k : K) → ι k)
    (hp : ∀ k, C₂.φ (C₂.ρ (rep x)) ⟨k, p k⟩ ≠ 0) :
    (fderiv ℂ (fun y => affCoord p (C₂.φ (C₂.ρ (rep ((orbChart hP C₁ x₁).symm y)))))
      (orbChart hP C₁ x₁ x)).ker = ⊥ := by
  set ψ := orbChart hP C₁ x₁ with hψ
  have hw₀ : ψ x ∈ ψ.target := ψ.map_source hx₁
  have hsym : ψ.symm (ψ x) = x := ψ.left_inv hx₁
  have hV : ψ.target ∩ ψ.symm ⁻¹' srcOf C₂ ∈ 𝓝 (ψ x) :=
    (isOpen_overlap hP C₁ C₂ x₁).mem_nhds ⟨hw₀, by rw [Set.mem_preimage, hsym]; exact hx₂⟩
  have heq : (fun y => affCoord p (C₂.φ (C₂.ρ (rep (ψ.symm y))))) =ᶠ[𝓝 (ψ x)]
      fun y => affCoord p (C₁.φ y) := by
    filter_upwards [hV] with w hw
    have hm := C₁.mem w hw.1
    have h1 : SameOrbit (rep (ψ.symm w)) (C₁.φ w) := by
      show SameOrbit (rep (clsT x₁ (C₁.φ w))) (C₁.φ w)
      rw [clsT_of_mem x₁ hm]
      exact rep_cls_orbit _ hm
    exact Proj.affCoord_eq (Proj.orbit_trans (C₂.φ_ρ _ hw.2) h1) p
  rw [heq.fderiv_eq]
  have ho : SameOrbit (C₂.φ (C₂.ρ (rep x))) (C₁.φ (ψ x)) :=
    Proj.orbit_trans (C₂.φ_ρ _ hx₂) (Proj.orbit_symm (C₁.φ_ρ _ hx₁))
  exact C₁.immersion _ hw₀ p fun k => Proj.orbit_ne ho (hp k)

end Overlap

def atlasOf (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) : FinHolAtlas e (PtsOf P) where
  n := t.card
  chart j := orbChart hP (Cx (t.equivFin.symm j)) (t.equivFin.symm j)
  cover x := by
    obtain ⟨y, hy, hx⟩ := hcov x
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    show x ∈ srcOf (Cx (t.equivFin.symm (t.equivFin ⟨y, hy⟩)))
    rw [Equiv.symm_apply_apply]
    exact hx
  holo j k := analytic_transition hP _ _ _ _

theorem isCompat_orbChart (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (x₀ : PtsOf P) :
    IsCompatChart (atlasOf hP Cx t hcov) (orbChart hP C x₀) := fun _ =>
  ⟨analytic_transition hP _ _ _ _, analytic_transition hP _ _ _ _⟩

theorem holoOn_eval (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (atlasOf hP Cx t hcov).HoloOn (srcOf C) (fun y => eval (C.φ (C.ρ (rep y))) f) := fun j w hw =>
  analyticAt_eval (g := fun w => C.φ (C.ρ (rep (((atlasOf hP Cx t hcov).chart j).symm w))))
    (fun q => analytic_lift hP _ C _ q w hw) f

def resOf (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P) (Cx : PtsOf P → OrbitChart P e)
    (hCx : ∀ x, x ∈ srcOf (Cx x)) (t : Finset (PtsOf P)) (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) :
    AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hnd
  X := PtsOf P
  top := inferInstance
  compact := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  t2 := inferInstance
  A := atlasOf hP Cx t hcov
  U x := srcOf (Cx x)
  isOpen_U x := isOpen_srcOf hP _
  mem_U := hCx
  lift x y := (Cx x).φ ((Cx x).ρ (rep y))
  holo x p j := analytic_lift hP _ _ _ p
  mem x y hy := (Cx x).mem _ ((Cx x).ρ_mem _ hy)
  compat x x' y hy := Proj.orbit_trans ((Cx x).φ_ρ _ hy.1) (Proj.orbit_symm ((Cx x').φ_ρ _ hy.2))
  surj z hz _ := ⟨cls z hz, Proj.orbit_trans ((Cx _).φ_ρ _ (hCx _)) (rep_cls_orbit z hz)⟩
  inj x x' _ h := pts_eq_of_orbit (Proj.orbit_trans (Proj.orbit_symm ((Cx x).φ_ρ _ (hCx x)))
    (Proj.orbit_trans h ((Cx x').φ_ρ _ (hCx x'))))
  immersion x _ p hp j hj := immersion_lift hP _ (Cx x) _ (hCx x) hj p hp
  snc f a _ _ hz := ⟨0, Fin.elim0, Fin.elim0, fun x => ⟨orbChart hP (Cx x) x, isCompat_orbChart hP Cx t hcov _ _,
    hCx x, subset_rfl, Fin.elim0, fun k => k.elim0, fun k => k.elim0,
    fun y => eval ((Cx x).φ ((Cx x).ρ (rep y))) (map (Int.castRingHom ℂ) f),
    holoOn_eval hP Cx t hcov (Cx x) _,
    fun y hy h0 => Proj.not_mem_mcPts_top _ (hz _ ((Cx x).mem _ ((Cx x).ρ_mem _ hy)) h0),
    fun y _ => by simp⟩⟩
  null j := by
    have : {x : PtsOf P | (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts (⊤ : Ideal (MRing ι))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x => Proj.not_mem_mcPts_top _
    rw [this]
    simp

theorem exists_anLogRes_of_orbitCharts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ), Nonempty K → IsMultiHomogIdeal P → ¬ (⊤ : Ideal (MRing ι)) ≤ P → (∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) → ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ), IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧ ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  intro K _ ι _ P e _ hP hnd hcov
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
