import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhoodStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionContinuousAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsNeighbourhoodInOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoiceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformBoundOnClosedConeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem exists_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (hξ : IsCptGen ξ)
    (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z) {e : Li} (he : e ∈ M.lat ⟨centre z, hz⟩) :
    ∃ v : epsAt z ⟶ G, M.ValAt z e v := by
  obtain ⟨E, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M ℂ z hz E MR hξ inferInstance
  exact ⟨MR.pt (ev ⟨e, he⟩), (hev e _).2 ⟨he, rfl⟩⟩

theorem lat_of_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {z : Sp ℂ ⟶ X} (hz : genPt ξ ⤳ centre z)
    {e : Li} {v : epsAt z ⟶ G} (h : M.ValAt z e v) : e ∈ M.lat ⟨centre z, hz⟩ := by
  obtain ⟨_, v', hv', -⟩ := h
  exact Submodule.subset_span ⟨v', hv'⟩

theorem local_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y A.a e₀ → IsSmoothHerm A →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ), CoordsAt ξ y z₀ w₀ → ∃ N ∈ 𝓝 w₀, ∃ C : ℝ,
    ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) → e ∈ flagStep Ω b₀ (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      IsCls b₀ i e t → ValAt ξ z (t / gen y A.a e₀ c₀) u → u ≠ 0 → (gramAt h z v).det ≠ 0 →
      |(1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)| ≤ C := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm z₀ w₀ hw₀
  have hξ := htie.gen
  obtain ⟨g, hg⟩ := GlobalTheory.T.smooth_group_rel_dim_generic X Ω ξ G hall
  choose c₁ hc₁ using fun k => hw₀.1 k
  have hc₁' : ∀ k, w₀ ⟨k, c₁ k⟩ ≠ 0 := fun k => (hc₁ k).ne_zero
  have h₀ := hall (centre z₀)
  obtain ⟨b, π, κ, hfl, hfr, hmb, hd, hmπ, hκ0, hκr, hκi, hκ⟩ :=
    GlobalTheory.T.exists_graded_sandwich_coordinates X Ω ξ K J y G Li M V r b₀ m i A.a e₀ hind hsw hdeg ⟨centre z₀, h₀⟩ c₁ (in_chart h₀ hw₀ hc₁')
  obtain ⟨U, hU, hnear⟩ := GlobalTheory.T.regular_sections_open_neighbourhood X Ω ξ G g Li M hξ hg ⟨centre z₀, h₀⟩ r (fun j => (m : Ω) • b j)
    (fun j => (m : Ω) • π j) hmb (fun j e he => by simpa using hmπ j e he)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : Ω) ≠ 0 := by exact_mod_cast hm.ne'
  have hminv : ∀ (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z), (m : Ω)⁻¹ ∈ regAt ξ ⟨centre z, hz⟩ := fun z hz => by
    obtain ⟨_, h'⟩ := val_spec (val_inv₀ hm0 (val_nat (ξ := ξ) hz m))
    exact h'
  have hbq : ∀ (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z), centre z ∈ U → ∀ j, b j ∈ M.lat ⟨centre z, hz⟩ := by
    intro z hz hzU j
    have h1 := (hnear ⟨centre z, hz⟩ hzU).1 j
    have h2 := (M.lat ⟨centre z, hz⟩).smul_mem ⟨_, hminv z hz⟩ h1
    have h3 : (⟨(m : Ω)⁻¹, hminv z hz⟩ : regAt ξ ⟨centre z, hz⟩) • ((m : Ω) • b j) = b j := by
      show ((m : Ω)⁻¹) • ((m : Ω) • b j) = b j
      rw [smul_smul, inv_mul_cancel₀ hm1, one_smul]
    rwa [h3] at h2
  have hπq : ∀ (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z), centre z ∈ U → ∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩,
      π j e ∈ regAt ξ ⟨centre z, hz⟩ := by
    intro z hz hzU j e he
    have h1 := (hnear ⟨centre z, hz⟩ hzU).2 j e he
    have h2 := mul_mem (hminv z hz) h1
    have h3 : (m : Ω)⁻¹ * ((m : Ω) • π j) e = π j e := by
      simp [hm1]
    rwa [h3] at h2
  obtain ⟨N1, hN1, hN1'⟩ := GlobalTheory.T.coords_neighbourhood_in_open X Ω ξ K J y hall htie z₀ w₀ U hw₀ hU
  obtain ⟨φ, hφc, N2, hN2, hN2'⟩ := GlobalTheory.T.regular_function_continuous_at X Ω ξ K J y hall htie z₀ w₀ h₀ κ hw₀ hκr
  choose F hFc hFe using fun (a c : Fin r) => h.cont (b a) (b c)
  have hφ0 : φ w₀ ≠ 0 := by
    have hv := hN2' z₀ w₀ (mem_of_mem_nhds hN2) hw₀
    intro h0
    rw [h0] at hv
    obtain ⟨r', hr'⟩ := val_exists hκi
    have h1 := val_mul hv hr'
    rw [mul_inv_cancel₀ hκ0, zero_mul] at h1
    exact one_ne_zero (val_unique hξ (val_one h₀) h1)
  have hN3 : {w : (Σ k, J k) → ℂ | ∀ k, w ⟨k, c₁ k⟩ ≠ 0} ∈ 𝓝 w₀ := by
    have : {w : (Σ k, J k) → ℂ | ∀ k, w ⟨k, c₁ k⟩ ≠ 0} = ⋂ k, {w | w ⟨k, c₁ k⟩ ≠ 0} := by ext; simp
    rw [this]
    exact (isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const).mem_nhds
      (by simpa using hc₁')
  have hN5 : {w | φ w ≠ 0} ∈ 𝓝 w₀ := hφc.eventually_ne hφ0
  set N₀ : Set ((Σ k, J k) → ℂ) := N1 ∩ N2 ∩ {w | ∀ k, w ⟨k, c₁ k⟩ ≠ 0} ∩ {w | φ w ≠ 0} with hN₀
  have hN₀m : N₀ ∈ 𝓝 w₀ := inter_mem (inter_mem (inter_mem hN1 hN2) hN3) hN5
  set S₀ : Set ((Σ k, J k) → ℂ) := {w | w ∈ N₀ ∧ ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w} with hS₀
  have hw₀S : w₀ ∈ S₀ := ⟨mem_of_mem_nhds hN₀m, z₀, hw₀⟩
  have hS : ∀ a c, S₀ ⊆ {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z (b a) va ∧ M.ValAt z (b c) vb} := by
    rintro a c w ⟨hwN, z, hz⟩
    have hzU := hN1' z w hwN.1.1.1 hz
    obtain ⟨va, hva⟩ := exists_lieVal M hξ z (hall _) (hbq z (hall _) hzU a)
    obtain ⟨vb, hvb⟩ := exists_lieVal M hξ z (hall _) (hbq z (hall _) hzU c)
    exact ⟨z, va, vb, hz, hva, hvb⟩
  have hFw : ∀ a c, ContinuousWithinAt (F a c) S₀ w₀ := fun a c => ((hFc a c).mono (hS a c)) w₀ hw₀S
  let G₁ : ((Σ k, J k) → ℂ) → Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ := fun w =>
    Matrix.of fun a c => F (Fin.castLE i.2 a) (Fin.castLE i.2 c) w
  let G₀ : ((Σ k, J k) → ℂ) → Matrix (Fin i) (Fin i) ℂ := fun w =>
    Matrix.of fun a c => F (Fin.castLE i.2.le a) (Fin.castLE i.2.le c) w
  have hg1 : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (B : Fin r → (epsAt z ⟶ G)), CoordsAt ξ y z w →
      (∀ j, M.ValAt z (b j) (B j)) → (gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)) = G₁ w := by
    intro z w B hz hB
    ext a c
    exact (hFe _ _ z w _ _ hz (hB _) (hB _)).symm
  have hg0 : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (B : Fin r → (epsAt z ⟶ G)), CoordsAt ξ y z w →
      (∀ j, M.ValAt z (b j) (B j)) → (gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)) = G₀ w := by
    intro z w B hz hB
    ext a c
    exact (hFe _ _ z w _ _ hz (hB _) (hB _)).symm
  choose B₀ hB₀ using fun j => exists_lieVal M hξ z₀ h₀ (hbq z₀ h₀ (hN1' z₀ w₀ (mem_of_mem_nhds hN1) hw₀) j)
  have hπ₀ := hπq z₀ h₀ (hN1' z₀ w₀ (mem_of_mem_nhds hN1) hw₀)
  have hne1 : (G₁ w₀).det ≠ 0 := by
    rw [← hg1 z₀ w₀ B₀ hw₀ hB₀]
    exact GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame X Ω ξ K J y G Li M h z₀ h₀ r b π B₀ hξ hd hπ₀ hB₀ _ _ (Fin.castLE_injective _)
  have hne0 : (G₀ w₀).det ≠ 0 := by
    rw [← hg0 z₀ w₀ B₀ hw₀ hB₀]
    exact GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame X Ω ξ K J y G Li M h z₀ h₀ r b π B₀ hξ hd hπ₀ hB₀ _ _ (Fin.castLE_injective _)
  have hd1 : ContinuousWithinAt (fun w => (G₁ w).det) S₀ w₀ :=
    (Continuous.matrix_det continuous_id).continuousAt.comp_continuousWithinAt
      (continuousWithinAt_pi.2 fun a => continuousWithinAt_pi.2 fun c => hFw _ _)
  have hd0 : ContinuousWithinAt (fun w => (G₀ w).det) S₀ w₀ :=
    (Continuous.matrix_det continuous_id).continuousAt.comp_continuousWithinAt
      (continuousWithinAt_pi.2 fun a => continuousWithinAt_pi.2 fun c => hFw _ _)
  let D : ((Σ k, J k) → ℂ) → ℝ := fun w => (1 / 2) * (Real.log ‖(G₁ w).det‖ - Real.log ‖(G₀ w).det‖) - Real.log ‖φ w‖ -
    ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₁ k⟩‖ + Real.log (A.h w)
  have hb₀ : ∀ k, ∃ j, w₀ ⟨k, j⟩ ≠ 0 := fun k => ⟨c₁ k, hc₁' k⟩
  have hA : ContinuousWithinAt A.h S₀ w₀ := by
    refine (hsm.continuousOn w₀ hb₀).mono ?_
    rintro w ⟨-, z, hz⟩ k
    exact (hz.1 k).imp fun c hc => hc.ne_zero
  have hsum : ContinuousWithinAt (fun w : (Σ k, J k) → ℂ => ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₁ k⟩‖) S₀ w₀ := by
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finset_sum _ fun k _ => ?_
    refine ContinuousAt.mul continuousAt_const ?_
    exact ((continuous_apply _).continuousAt.norm).log (norm_ne_zero_iff.2 (hc₁' k))
  have hD : ContinuousWithinAt D S₀ w₀ :=
    (((continuousWithinAt_const.mul ((hd1.norm.log (norm_ne_zero_iff.2 hne1)).sub
      (hd0.norm.log (norm_ne_zero_iff.2 hne0)))).sub
      (hφc.continuousWithinAt.norm.log (norm_ne_zero_iff.2 hφ0))).sub hsum).add (hA.log (A.pos w₀ hb₀).ne')
  have hev : ∀ᶠ w in 𝓝[S₀] w₀, dist (D w) (D w₀) < 1 := (Metric.tendsto_nhds.1 hD) 1 one_pos
  obtain ⟨N4, hN4, hN4'⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  refine ⟨N4 ∩ N₀, inter_mem hN4 hN₀m, |D w₀| + 1, ?_⟩
  rintro z w ⟨hw4, hwN⟩ hz c₀ hc₀ f e v ve t u hf he hv hve hcls hu hu0 hG
  have hzq := hall (centre z)
  have hzU := hN1' z w hwN.1.1.1 hz
  have hc₁w : ∀ k, w ⟨k, c₁ k⟩ ≠ 0 := hwN.1.2
  have hφw : φ w ≠ 0 := hwN.2
  choose B hB using fun j => exists_lieVal M hξ z hzq (hbq z hzq hzU j)
  obtain ⟨s, hs⟩ := val_exists (R := ℂ) (hπq z hzq hzU i e (lat_of_lieVal hzq hve))
  have hκv := hN2' z w hwN.1.1.2 hz
  have hmul := val_mul hs hκv
  rw [← hκ e t he hcls] at hmul
  have hr := GlobalTheory.T.val_at_gen_independent_choice X Ω ξ K J y z w A.a e₀ t c₀ c₁ u (s * φ w) hξ hdeg.1 hz hc₀ hc₁w hu hmul
  have hp0 : ∏ k, w ⟨k, c₀ k⟩ ^ A.a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc₀ k)
  have hp1 : ∏ k, w ⟨k, c₁ k⟩ ^ A.a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc₁w k)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hr
    exact mul_ne_zero hu0 hp0 hr
  have hgv := GlobalTheory.T.lie_metric_frame_projection_at X Ω ξ K J y G Li M h z hzq r b π B i hξ hd (hπq z hzq hzU) hB f e v ve s
    (fun j => by rw [hfl]; exact hf j) (by rw [hfl]; exact he) hv hve hs hs0 hG
  rw [hg1 z w B hz hB, hg0 z w B hz hB] at hgv
  have hlog : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → Real.log ‖∏ k, c k ^ A.a k‖ = ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
    intro c hc'
    rw [norm_prod, Real.log_prod (fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hc' k)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_zpow, Real.log_zpow]
  have hnorm : Real.log ‖u‖ + ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ =
      Real.log ‖s‖ + Real.log ‖φ w‖ + ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₁ k⟩‖ := by
    have h1 := congrArg (fun x : ℂ => Real.log ‖x‖) hr
    simp only [norm_mul] at h1
    rw [Real.log_mul (norm_ne_zero_iff.2 hu0) (norm_ne_zero_iff.2 hp0),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hs0) (norm_ne_zero_iff.2 hφw)) (norm_ne_zero_iff.2 hp1),
      Real.log_mul (norm_ne_zero_iff.2 hs0) (norm_ne_zero_iff.2 hφw),
      hlog (fun k => w ⟨k, c₀ k⟩) hc₀, hlog (fun k => w ⟨k, c₁ k⟩) hc₁w] at h1
    exact h1
  have hfin : (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w) = D w := by
    simp only [D]
    rw [hgv]
    linarith
  rw [hfin]
  have h4 : dist (D w) (D w₀) < 1 := hN4' ⟨hw4, hwN, z, hz⟩
  rw [Real.dist_eq] at h4
  have h5 := abs_sub_abs_le_abs_sub (D w) (D w₀)
  linarith

theorem arch_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y A.a e₀ → IsSmoothHerm A →
    ∃ C : ℝ, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) → e ∈ flagStep Ω b₀ (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      IsCls b₀ i e t → ValAt ξ z (t / gen y A.a e₀ c₀) u → u ≠ 0 → (gramAt h z v).det ≠ 0 →
      |(1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)| ≤ C := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm
  let Ex : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (c₀ : (k : K) → J k) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (u : ℂ), ℝ :=
    fun z w c₀ v ve u => (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)
  let Bd : ((Σ k, J k) → ℂ) → ℝ → Prop := fun w x => ∃ (z : Sp ℂ ⟶ X), CoordsAt ξ y z w ∧ ∃ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) ∧
      ∃ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧ (∀ j, M.ValAt z (f j) (v j)) ∧ M.ValAt z e ve ∧
      IsCls b₀ i e t ∧ ValAt ξ z (t / gen y A.a e₀ c₀) u ∧ u ≠ 0 ∧ (gramAt h z v).det ≠ 0 ∧ x = Ex z w c₀ v ve u
  obtain ⟨C, hC⟩ := GlobalTheory.T.uniform_bound_on_closed_cone K J {w | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w} Bd
    (fun w ⟨z, hz⟩ k => (hz.1 k).imp fun c hc => hc.ne_zero)
    (fun w hw hb => GlobalTheory.T.complex_points_closure_coords X Ω ξ K J y hall htie w hw hb)
    (fun w x ⟨z, hz, _⟩ => ⟨z, hz⟩)
    (by
      rintro w x c hc ⟨z, hz, c₀, hc₀, f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩
      refine ⟨z, coordsAt_smul c hc hz, c₀, fun k => mul_ne_zero (hc k) (hc₀ k), f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
      have hb : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => ⟨c₀ k, hc₀ k⟩
      have hp := A.pos w hb
      have hs := A.smul c w hc
      simp only [Ex]
      rw [hs, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))) hp.ne',
        Real.log_prod (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]
      have : ∀ k, (A.a k : ℝ) * Real.log ‖c k * w ⟨k, c₀ k⟩‖ = (A.a k : ℝ) * Real.log ‖c k‖ + (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ := fun k => by
        rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hc₀ k))]; ring
      simp only [this, Finset.sum_add_distrib, Real.log_zpow]
      ring)
    (by
      rintro w₀ ⟨z₀, hz₀⟩
      obtain ⟨N, hN, C, hC⟩ := local_bound X Ω ξ K J y G Li M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm z₀ w₀ hz₀
      refine ⟨N, hN, C, ?_⟩
      rintro w hw x ⟨z, hz, c₀, hc₀, f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩
      exact hC z w hw hz c₀ hc₀ f e v ve t u h1 h2 h3 h4 h5 h6 h7 h8)
  refine ⟨C, ?_⟩
  intro z w hz c₀ hc₀ f e v ve t u h1 h2 h3 h4 h5 h6 h7 h8
  exact hC w _ ⟨z, hz, c₀, hc₀, f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
