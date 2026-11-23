import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.FramePeriods
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem exists_isFramePeriods_noGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  intro E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 a b N bb n Bd χ t₀ cc f hBd ht₀ hfr hdom
  classical
  obtain ⟨a₀, π, ρ₀, ha, hρ₀, hρ₀', hπ, hgeo⟩ := GlobalTheory.T.snc_chart_local_normal_form K J Ω y _ n Bd χ t₀ cc f ht₀ hdom
  have hw : DifferentiableOn ℂ (fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u)) (Metric.ball 0 1) := by
    refine χ.analytic.differentiableOn.comp ?_ fun u hu => (hgeo ρ₀ hρ₀ le_rfl u hu).1
    unfold HodgeMetric.recentre
    exact (differentiable_const _ |>.add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))).differentiableOn
  set w : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u) with hwdef
  have htie := 𝔐.tie
  have hall := 𝔐.all
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧ CoordsAt 𝔐.ξ y z (w u) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w u)).1 (χ.mem _ (hgeo ρ₀ hρ₀ le_rfl u hu).1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

  have fin : ∀ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ₁ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ₁ → ρ₁ ≤ 1 →
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) →
      (∀ u ∈ Flat.punct n a₀ 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w ((ρ₁ : ℂ) • u)) →
        𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u)) →
      ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
    intro g Λ _ L ρ₁ U h1 h2 h3 h4 h5
    have hle : ρ₀ * ρ₁ ≤ ρ₀ := by nlinarith
    have hpos : 0 < ρ₀ * ρ₁ := mul_pos hρ₀ h1
    refine ⟨a₀, g, Λ, inferInstance, L, π, ρ₀ * ρ₁, U, hpos, by nlinarith, h3, h4, hπ, fun u hu => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
    refine ⟨g1, g2, g3, fun hup z hz => ?_⟩
    rw [recentre_mul] at hz
    exact h5 u hup z hz
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hfr0 : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), hall _⟩ := by
    have hd := (hgeo ρ₀ hρ₀ le_rfl 0 hb0).2.1
    obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y htie (p 0) (w 0) cc f (hall _) (hp 0 hb0) hd
    exact hfr _ c1 c2
  by_cases hpq : D.p + D.q = 0
  · have hV : ∀ s, 𝔐.Vgen s = ⊥ := fun s => by
      obtain ⟨-, -, b', hb', -⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
      have hr : labelRk D s = 0 := by
        rcases s with s | s <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
      have : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
      have e : Set.range b' = ∅ := Set.range_eq_empty b'
      rw [e, Submodule.span_empty] at hb'
      exact hb'.symm
    have hli := hfr0.1
    haveI : Subsingleton ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := by
      rw [hV a, hV b, sup_bot_eq]
      infer_instance
    haveI : IsEmpty (Fin N) := ⟨fun k => hli.ne_zero k (Subsingleton.elim _ _)⟩
    obtain ⟨Λ, _, ⟨L⟩⟩ := zeroPeriods n a₀ ha
    exact fin 0 Λ _ L 1 (fun _ _ => 0) one_pos le_rfl (fun k => isEmptyElim k) linearIndependent_empty_type
      fun u _ z _ => ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  have hpq' : 1 ≤ D.p + D.q := Nat.one_le_iff_ne_zero.2 hpq
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  set σ : KA l →+* ℂ := τ.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨g, Λ, _, L, ρ₁, U, h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p τ hpq' hs ha hhol hτ hint (hall _) hfr0
    refine fin g Λ _ L ρ₁ U h1 h2 h3 h4 fun u hu z hz => ?_
    rw [huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
    exact h5 u hu
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcoord : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (p' u) (fun q => star (w (star u) q)) := fun u hu =>
      (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ _).2 (hp _ (star_mem_ball' hu))
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ (w 0)).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ _ p' Metric.isOpen_ball
      (diffOn_star' hw) hcoord
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_punct' hu)
    have hs' : (((starRingEnd ℂ).comp τ).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hfr0' : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p' 0), hall _⟩ := by
      have e : (⟨centre (p' 0), hall _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), hall _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hfr0
    obtain ⟨g, Λ, _, L', ρ₁, U', h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p' _ hpq' hs' ha hhol' hτ' hint' (hall _) hfr0'
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_conjugate_log_periods n a₀ g N Λ L' U' (GlobalTheory.T.bijective_logPeriods_T n a₀ g Λ L')
    refine fin g Λ _ L ρ₁ (fun k u' => star (U' k (star u'))) h1 h2 (fun k => diffOn_star' (h3 k)) ?_ fun u hu z hz => ?_
    · refine Fintype.linearIndependent_iff.2 fun c' hc' k => ?_
      have e := congrArg star hc'
      simp only [star_sum, star_smul, star_star, star_zero] at e
      have := Fintype.linearIndependent_iff.1 h4 (fun k => star (c' k)) (by simpa [star_smul] using e) k
      simpa using this
    · rw [hL u hu, huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
      have := GlobalTheory.T.gramAt_conj_point_map_conj E H D l (Xo l) c Y S Ω K J y 𝔐 _ N _ _ (h5 (star u) (star_mem_punct' hu))
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ₁ : ℂ) • star u) = p ((ρ₁ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this

end GlobalTheory.CompanionTheory.Ar.PB.BMx
