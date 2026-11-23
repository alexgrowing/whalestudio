import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

noncomputable section

open MeasureTheory
open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSupBound

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem continuous_mov_pair (hθ : IsInfFam θ) (u : RW T S) :
    Continuous fun p : GA D S × GA D T => mov θ p.1⁻¹ p.2⁻¹ u := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
    ((GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_snd)).matrix_mul continuous_const).matrix_mul
    ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt S).1.comp continuous_fst))

theorem uniform_level_pair (hom : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) {C : Set (GA D S × GA D T)} (hC : IsCompact C) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ p ∈ C, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ u ∈ K₀, u.map (infPart D) = 0 →
        heisO ψ S T u (om p φ) = om p φ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × (GA D S × GA D T) => actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (((GlobalTheory.RealWeil.continuous_mt T).2.comp (continuous_snd.comp continuous_snd)).matrix_mul
      continuous_fst).matrix_mul ((GlobalTheory.RealWeil.continuous_mt S).1.comp (continuous_fst.comp continuous_snd))
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ p ∈ C, actO S T p.1⁻¹ p.2⁻¹ u ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  refine ⟨K₀, h0, hK₀, fun ⟨g, h⟩ hp φ hφ hl u hu hinf => ?_⟩
  have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) φ hφ
  rw [hl _ (hsub hu _ hp) hv, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  exact e.symm

theorem cube_bound_at (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {N : ℕ}
    (b : Module.Basis (Fin N) ℝ (RW T S)) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T u (om p φ) = om p φ) → ∀ B : ℝ, (∀ w, ‖φ w‖ ≤ B) → ∀ y,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖om p φ (y + ∑ i, iotaW σ T S (t i • b i))‖ ^ 2 ≤ c * B ^ 2 := by
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  refine ⟨c, hc0, fun ⟨g, h⟩ φ hφ hl B hB y => ?_⟩
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ y) φ hφ
  rw [actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  have hn := GlobalTheory.HeisOrtho.norm_heisO (S := S) (T := T) hom.std.1
  have key := hcube (g, h) _ (GlobalTheory.ThetaClosed.thetaClosed ψ θ hom.std hc.inf S T φ hφ |>.1 (actO S T g⁻¹ h⁻¹ y))
    (fun w hw => by
      generalize hu : w - iotaW σ T S (piW θ T S w) = u at hw
      have hinf : u.map (infPart D) = 0 := by
        have hp : piW θ T S u = 0 := by
          rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
        ext i j
        exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
      rw [e, hn, hn]
      conv_rhs => rw [← hl u hw hinf, hn, ← hu]
      congr 2
      abel_nf) B (fun w => by rw [hn]; exact hB _)
  simp only [e, hn, zero_add] at key
  simpa only [add_comm y] using key

theorem exists_sup_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ C : Set (GA D S × GA D T), IsCompact C →
      ∃ c : ℝ, ∀ p ∈ C, ∀ w, ‖om p f w‖ ≤ c := by
  intro D ψ S T χS χT om hom f hf C hC
  have hψ := hom.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := uniform_level_pair hom hU hC
  obtain ⟨c, hc0, hcube⟩ := cube_bound_at hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun m => theta_bounded hψ m.2) N ⟨f, hf⟩
  obtain ⟨κ, hκ⟩ := hC.exists_bound_of_continuousOn
    (f := fun (p : GA D S × GA D T) (i : Fin N) => mov θ p.1⁻¹ p.2⁻¹ (b i))
    (continuous_pi fun i => continuous_mov_pair hθ (b i)).continuousOn
  refine ⟨√(4 ^ N * (c * (C₁ * max 1 κ ^ N) ^ 2)), fun ⟨g, h⟩ hp w => ?_⟩
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ max 1 κ) ∧ F = om (g, h) (wd l).1}
  refine Real.le_sqrt_of_sq_le (sobolev_iter N 0 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * max 1 κ ^ N) ^ 2) w
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (g, h) f) ⟨[], le_rfl, by simp, rfl⟩)
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact ((norm_le_pi_norm (fun i => mov θ g⁻¹ h⁻¹ (b i)) i).trans (hκ (g, h) hp)).trans (le_max_right _ _)
    · rw [dv_om hom hc g h (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    exact hcube (g, h) _ (wd l).2 (hlev (g, h) hp _ (wd l).2 fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _
      (hC₁ _ (le_max_left _ _) l (by simpa using h1) h2) w

end GlobalTheory.WeilSupBound

end
