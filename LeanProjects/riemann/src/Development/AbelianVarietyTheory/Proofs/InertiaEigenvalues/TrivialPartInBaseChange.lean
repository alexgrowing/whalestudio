import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.MuBlockLoc

theorem placesOver_finite (D : D7) (k : Fin 2) : (placesOver D.host.E (D.host.g k)).Finite := by
  have hne : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

theorem mem_isoInf (D : D7) (Pa : List (Part D.naut.CG)) (p : Part D.naut.CG) (hp : p ∈ Pa) (hd : 1 ≤ p.d)
    (τ : D.host.E →+* ℂ) :
    (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤ isoInf D.nd D.naut Pa τ := by
  unfold isoInf
  refine le_trans ?_ (List.single_le_sum (by intro x _; exact Multiset.zero_le x) _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  refine List.single_le_sum (by intro x _; exact Multiset.zero_le x) _ (List.mem_map.2 ⟨(0 : ℂ), ?_, rfl⟩)
  simp
  exact ⟨0, hd, by simp⟩

theorem part_norm (D : D7) (ht : SumRepresentations.tie0 D) (hT : SumRepresentations.adm7 D) {j : ℕ} {π : D.nbc.AU j}
    {Pa : List (Part D.naut.CG)} (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa)
    (w : PlE D.host) (hu : D.naut.unr (D.naut.locG p.π w)) :
    ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), ‖α‖ = 1 := by
  intro α hα
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤
      D.nbc.infW j (D.nbc.wtAU j π) τ := fun τ => by
    rw [← hB.2.2.2.2.2 τ]; exact mem_isoInf D Pa p hp hd1 τ
  have hW := fun τ => D.nbc.infW_alg j (D.nbc.wtAU j π) τ
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (D.naut.tempered_unr _ hu).1 (hT p.a p.π ha1 hcsd hr w) α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    have htw := hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w
    rw [D.naut.locG_tw] at htw
    have hd1' := D.naut.locG_dim D.naut.etaT w
    have heu := D.naut.etaT_unr w
    obtain ⟨e, he⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ heu).trans hd1')
    have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; simp)
    have hcu := D.naut.unr_char _ _ hd1' hu heu
    have hmem : α * e ∈ D.naut.frobEig (D.naut.lpChar (D.naut.locG p.π w) (D.naut.locG D.naut.etaT w)) := by
      rw [D.naut.frobEig_char _ _ e hu heu hd1' he]
      exact Multiset.mem_map_of_mem _ hα
    have := (D.naut.tempered_unr _ hcu).1 htw _ hmem
    rwa [norm_mul, hen, mul_one] at this

theorem mu_ralg (D : D7) (Rw : RowSide D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j) (μ : D.naut.CG 1)
    (hA : LiftAt D Rw j σ π μ) : D.naut.ralg μ := by
  obtain ⟨a, ha⟩ := GlobalTheory.LocalInv.r_odd D.R
  have hnV : (D.R.nV : ℂ) = 2 * (a : ℂ) + 1 + D.R.t := by
    show ((D.R.r + D.R.t : ℕ) : ℂ) = _
    rw [ha]; push_cast; ring
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hq : ∀ (τ : D.host.E →+* ℂ) (s : ℂ), D.naut.infG D.naut.etaTinv τ = {s} →
      (∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] τ, ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2) →
      ∀ z ∈ D.naut.infG μ τ, ∃ k : ℤ, z + s + ((D.R.t : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ s hs hx z hz
    have hle := mem_isoInf D [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩
      (List.mem_singleton_self _) ht1 τ
    dsimp only at hle
    rw [D.naut.infG_tw _ _ τ s hs, Multiset.map_map] at hle
    obtain ⟨k, hk⟩ := hx _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; simp⟩
  refine (D.naut.ralg_def _).2 fun φ => ?_
  obtain ⟨z0, hz0⟩ := Multiset.card_eq_one.mp (D.naut.infG_card μ φ)
  refine ⟨by rw [hz0]; exact Multiset.nodup_singleton z0, fun z hz => ?_⟩
  obtain ⟨τ, hτ | hτ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D φ
  · have e : φ = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ := hτ
    subst e
    have hx : ∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ),
        ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := fun x hx =>
      (D.nbc.infW_alg j (D.nbc.wtAU j π) _).2 x (by rw [(hA.inf τ).1]; exact Multiset.mem_add.2 (Or.inr hx))
    obtain ⟨k, hk⟩ := hq _ _ (hA.eta τ).1 hx z hz
    refine ⟨k + a + 1, ?_⟩
    rw [hnV] at hk
    push_cast
    linear_combination hk
  · have e : φ = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ := hτ
    subst e
    have hx : ∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ),
        ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := fun x hx =>
      (D.nbc.infW_alg j (D.nbc.wtAU j π) _).2 x (by rw [(hA.inf τ).2]; exact Multiset.mem_add.2 (Or.inr hx))
    obtain ⟨k, hk⟩ := hq _ _ (hA.eta τ).2 hx z hz
    refine ⟨k + a, ?_⟩
    rw [hnV] at hk
    push_cast
    linear_combination hk

end GlobalTheory.MuBlockLoc

namespace GlobalTheory.MuBlockLoc

theorem split_step (D : D7) (Rw : RowSide D) (hL : ParLaws D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j)
    (μ : D.naut.CG 1) (Pa : List (Part D.naut.CG)) (hA : LiftAt D Rw j σ π μ) (hR : RowLoc D Rw σ)
    (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hg : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k))
    (hPa : ∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) (hμ : D.naut.unr (D.naut.locG μ w)) :
    (∃ p ∈ Pa, D.R.t ≤ p.d) ∧ ∀ p ∈ Pa, D.R.t ≤ p.d → p.d = D.R.t ∧
      D.naut.frobEig (D.naut.locG p.π w) = D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := by
  have hT := hL.tie0
  have hLP := hT.1
  have hAut := hT.2.1

  have heu := D.naut.etaT_unr w
  have hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
  obtain ⟨e, he⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ heu hed
  have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)
  have he0 : e ≠ 0 := by intro h; rw [h] at hen; simp at hen
  obtain ⟨hbu, hbe⟩ := D.naut.etaTinv_def w
  have hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹} := by rw [hbe, he]; simp
  have hbn : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]

  obtain ⟨m, hm⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)
  have hmt := hL.temp 1 μ le_rfl hA.csd (mu_ralg D Rw j σ π μ hA) w
  have hmn : ‖m‖ = 1 := (D.naut.tempered_unr _ hμ).1 hmt m (by rw [hm]; exact Multiset.mem_singleton_self m)
  have htw : D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) = {m * e⁻¹} := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]; simp

  have hV := hA.loc w hs
  have hiso := GlobalTheory.MuBlock.frobEig_isoLoc D.nd D.naut Pa w hPa
  have hVu : D.naut.unr (D.nbc.locAU j π w) := by rw [← hB.2.2.2.1 w hs]; exact hiso.1
  have hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1} := by
    have hu := D.naut.unr_char _ _ hed hbu heu
    rw [D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]; simp [he0]
  have hX : D.naut.lpChar (D.nbc.locAU j π w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) := by
    rw [hV, (hLP w (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w))
      (Rw.locR σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]
    exact (hLP w _ (Rw.locR σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1
  have hXu : D.naut.unr (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) := by
    rw [← hX]; exact D.naut.unr_char _ _ hed hVu heu
  obtain ⟨hWu, hSu⟩ := (D.naut.unr_sum _ _).1 hXu
  have hmu := GlobalTheory.MuBlock.frobEig_spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w hμ
  dsimp only at hmu
  have hVe : D.naut.frobEig (D.nbc.locAU j π w) =
      (D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹) +
      ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^
        (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum := by
    rw [hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add]
    rw [hmu.2, hm]
    congr 1
    rw [← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]
    ring_nf
  have key := GlobalTheory.longest_segment_unique_of_bounded_remainder (Formalism.ConjugateSelfDual.normV w) D.R.t
    (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w)))
    ((D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹)) (m * e⁻¹)
    (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos
    (by rw [norm_mul, hmn, hbn, one_mul])
    (by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hbn, mul_one]
      have := (hR w hs hg).2 α hα
      rwa [GlobalTheory.MuBlock.absNorm_eq_normV] at this)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      refine ⟨(hB.1 p hp).2.1, ?_, part_norm D hT hL.temp hB p hp w (hPa p hp)⟩
      intro h0
      change D.naut.frobEig (D.naut.locG p.π w) = 0 at h0
      have h1 := D.naut.frobEig_card _ (hPa p hp)
      rw [h0, D.naut.locG_dim] at h1
      have := (hB.1 p hp).1
      simp at h1
      omega)
    (by
      have hiso2 := hiso.2
      simp only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2
      rw [List.map_map]
      exact hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))
  refine ⟨?_, fun p hp hpt => ?_⟩
  · obtain ⟨x, hx, hxt⟩ := key.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, hxt⟩
  · obtain ⟨h1, h2⟩ := key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt
    exact ⟨h1, h2.trans htw.symm⟩

theorem mu_block_mem : ∀ (D : D7) (Rw : RowSide D), ParLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa →
    (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  intro D Rw hL j σ π μ Pa hA hR hB
  have hgood : ∀ᶠ w in Filter.cofinite, ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧
      D.naut.unr (D.naut.locG μ w)) ∧ ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    refine Filter.Eventually.and (Filter.Eventually.and ?_ (D.naut.locG_unr_ae _)) ?_
    · exact (Filter.eventually_all_finite (List.finite_toSet Pa)).2 fun p _ => D.naut.locG_unr_ae p.π
    · exact Filter.eventually_all.2 fun k => (placesOver_finite D k).compl_mem_cofinite
  obtain ⟨w0, hw0, hs0⟩ := GlobalTheory.MuBlock.exists_split_not_mem D.nd hL.an.2.2.1 _ (Filter.eventually_cofinite.1 hgood)
  have hg0 : ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w0)) ∧ D.naut.unr (D.naut.locG μ w0)) ∧
      ∀ k : Fin 2, w0 ∉ placesOver D.host.E (D.host.g k) := by
    have h := hw0
    simp only [Set.mem_setOf_eq, not_not] at h
    exact h
  obtain ⟨⟨p0, hp0, hpt⟩, -⟩ := split_step D Rw hL j σ π μ Pa hA hR hB w0 hs0 hg0.2 hg0.1.1 hg0.1.2
  have hall : ∀ w, (((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧ D.naut.unr (D.naut.locG μ w)) ∧
      ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
      IsSplitPl D.host w → p0.d = D.R.t ∧ D.naut.frobEig (D.naut.locG p0.π w) =
        D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) :=
    fun w hw hs => (split_step D Rw hL j σ π μ Pa hA hR hB w hs hw.2 hw.1.1 hw.1.2).2 p0 hp0 hpt
  have htu : ∀ w, D.naut.unr (D.naut.locG μ w) →
      D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := fun w h => by
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ _) h (D.naut.etaTinv_def w).1
  obtain ⟨hd0, hf0⟩ := hall w0 hg0 hs0
  have ha0 : p0.a = 1 := by
    have h1 := D.naut.frobEig_card _ (hg0.1.1 p0 hp0)
    rw [hf0, D.naut.frobEig_card _ (htu w0 hg0.1.2), D.naut.locG_dim, D.naut.locG_dim] at h1
    exact h1.symm
  obtain ⟨a, π', d⟩ := p0
  dsimp only at ha0 hd0 hall hp0
  subst ha0 hd0
  have hν : π' = D.naut.tw μ D.naut.etaTinv := by
    refine hL.one π' _ ?_
    filter_upwards [hgood] with w hw hs
    rw [D.naut.unr_eq_lpUnr _ (hw.1.1 _ hp0), (hall w hw hs).2, ← D.naut.unr_eq_lpUnr _ (htu w hw.1.2)]
  subst hν
  exact hp0

end GlobalTheory.MuBlockLoc
