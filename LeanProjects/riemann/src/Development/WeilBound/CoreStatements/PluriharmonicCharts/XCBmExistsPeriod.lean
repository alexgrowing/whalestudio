import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.FamilyPeriod
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

open PositivityTheory.Xgp.c_bm_exists_period FramePeriods in
theorem PositivityTheory.Xgp.t_c_bm_exists_period : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  intro hG E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie hp1 _ n Rb s hInt hcl F hF τ x hx hg
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨j, r, p, hr, hj, hw, hp⟩ := exists_family (𝔐 := 𝔐) Rb hcl hx
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all n _ _ p
    Metric.isOpen_ball hw fun u hu => (hp u hu).2.1
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p u) := fun u hu =>
    (hInt _ _ (hp u hu).2.2).1 (hp u hu).1
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hg0 : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre (p 0), 𝔐.all _⟩) := by
    rw [ptIdeal_centre (hp 0 hb0).2.1, smul_zero, add_zero, (Rb.A.chart j).left_inv hj]
    exact hg
  have fin : ∀ (ρ : ℝ) (B : Set (Fin n → ℂ)) (Pi Γ : (Fin n → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
      0 < ρ → ρ ≤ 1 → IsOpen B → 0 ∈ B → B ⊆ Metric.ball 0 1 → HolM B Pi →
      (∀ u ∈ B, 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (gb tie F τ) (Γ u) ∧ IsPeriodGram D.p (Pi u) (blockG (Γ u))) →
      ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧
        (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧
        ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
    intro ρ B Pi Γ hρ hρ' hB h0 hsub hPi hgr
    obtain ⟨h1, h2, h3⟩ := to_manifold Rb.A j hj (r := (r : ℂ) * ρ) hB h0
    refine ⟨_, fun x' => Pi (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x)), h1, h2,
      fun a b => h3 _ (hPi a b), fun x' hx' => ?_⟩
    have hm := smul_mem_ball' hρ hρ' (hsub hx'.2)
    have hc := (hp _ hm).2.2
    have hne : (r : ℂ) * ρ ≠ 0 := by exact_mod_cast (mul_pos hr hρ).ne'
    rw [smul_smul (r : ℂ), smul_inv_smul₀ hne, add_sub_cancel, (Rb.A.chart j).left_inv hx'.1] at hc
    rw [baseGram, gramFn_eq hc (hint _ hm) (hgr _ hx'.2).1]
    exact (hgr _ hx'.2).2
  set σ : KA l →+* ℂ := τ₀.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨ρ, B, Pi, Γ, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
      family_period hG.1.2.2.1 tie hpq hF p τ₀ hs hhol hτ hint hg0
    exact fin ρ B (Pi τ) (Γ τ) h1 h2 h3 h4 h5 (h6 τ) (h7 τ)
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X M.Ω 𝔐.ξ _ _ M.x _ 0).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all n _ _ p'
      Metric.isOpen_ball (diffOn_star' hw)
      fun u hu => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X M.Ω 𝔐.ξ _ _ M.x _ _).2 (hp _ (star_mem_ball' hu)).2.1
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ₀).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ₀.comp (algebraMap (𝓞 c.F) c.F)))
        (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_ball' hu)
    have hs' : (((starRingEnd ℂ).comp τ₀).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hg0' : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre (p' 0), 𝔐.all _⟩) := by
      have e : (⟨centre (p' 0), 𝔐.all _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), 𝔐.all _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hg0
    obtain ⟨ρ, B, Pi, Γ, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
      family_period hG.1.2.2.1 tie hpq hF p' _ hs' hhol' hτ' hint' hg0'
    refine fin ρ (star ⁻¹' B) (fun u => (Pi τ (star u)).map (starRingEnd ℂ))
      (fun u => (Γ τ (star u)).map (starRingEnd ℂ)) h1 h2 (h3.preimage continuous_star) (by simpa using h4)
      (fun u hu => by simpa using star_mem_ball' (h5 hu)) (fun a b u hu => ?_) fun u hu => ⟨?_, ?_⟩
    · have := ((h6 τ a b).differentiableAt (h3.mem_nhds hu)).star_star
      rw [star_star] at this
      exact this.differentiableWithinAt
    · have := GlobalTheory.T.gramAt_conj_point_map_conj E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ _ _ _ (h7 τ _ hu).1
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ : ℂ) • star u) = p ((ρ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this
    · rw [blockG_conj]
      exact periodGram_conj (h7 τ _ hu).2
