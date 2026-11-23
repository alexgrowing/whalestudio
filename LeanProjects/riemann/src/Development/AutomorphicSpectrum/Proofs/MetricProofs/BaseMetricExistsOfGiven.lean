import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCoverStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelFrameHeightComparisonStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlasStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDefStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalHoloIsPeriodGramBlockGBaseGramStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelHeightLowerEstimateStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelResolutionIntegrabilityStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem card_cmType_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 0 < Fintype.card (CMType H) := by
  intro E _ _ _ H
  have h := (GlobalTheory.T.cm_host_rank_bounds E H).2.2
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  by_contra h0
  have h3 : Fintype.card (CMType H) = 0 := by omega
  simp_all

theorem exists_coordsAt_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z (Rb.lift x x) := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 n Rb x
  obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 (Rb.mem x x (Rb.mem_U x))
  exact ⟨z, hz⟩

theorem mem_bdry_conj_iff : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (x₀ : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (Rb : AnLogRes (mCoordIdeal x₀) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd) → ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → (p' ∈ bdry s ↔ p ∈ bdry s) := by
  intro K _ J _ Ω _ x₀ n bd Rb s hb htor hconj p p' ho
  obtain ⟨c, hc, e⟩ := ho
  have hm : ∀ p, Rb.lift p p ∈ mcPts (mCoordIdeal x₀) := fun p => Rb.mem p p (Rb.mem_U p)
  rw [hb p', hb p]
  constructor
  · intro h
    have h1 := hconj _ ⟨hm p', h⟩
    have h2 := htor _ h1 (fun k => (starRingEnd ℂ (c k))⁻¹) (fun k => inv_ne_zero ((map_ne_zero _).2 (hc k)))
    have e2 : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => (starRingEnd ℂ (c k))⁻¹)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec (Rb.lift p' p')) = Rb.lift p p := by
      funext q
      simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec]
      rw [e]
      simp [inv_mul_cancel_left₀, (map_ne_zero (starRingEnd ℂ)).2 (hc q.1)]
    rw [e2] at h2
    exact h2.2
  · intro h
    have h1 := hconj _ ⟨hm p, h⟩
    have h2 := htor _ h1 c hc
    have e2 : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c
        (GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec (Rb.lift p p)) = Rb.lift p' p' := by
      funext q
      simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec]
      rw [e]
    rw [e2] at h2
    exact h2.2

theorem gramAt_sub {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {L : LB G.left}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {r r' : ℕ} {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ}
    (h : M.GramAt L z b Γ) (e : Fin r' → Fin r) : M.GramAt L z (fun i => b (e i)) (Γ.submatrix e e) := by
  obtain ⟨v, hv, h'⟩ := h
  exact ⟨fun i => v (e i), fun i => hv _, fun p q => h' _ _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem gb_wEmb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.p) :
    gb tie F τ (wEmb D.p D.q a) = tie.wFrame F τ a := by
  simp only [gb, gbS, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inr]

theorem gb_omEmb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.q) :
    gb tie F τ (omEmb D.p D.q a) = (dualFam tie F τ a : 𝔐.Li) := by
  simp only [gb, gbS, ← blockEquiv_inl, Equiv.symm_apply_apply, Sum.elim_inl]

theorem gramAt_wFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ}
    (h : 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ) :
    𝔐.M.GramAt 𝔐.t.PP.L z (tie.wFrame F τ) (wBlock (blockG Γ)) := by
  rw [wBlock_blockG]
  have := gramAt_sub h (wEmb D.p D.q)
  simp only [gb_wEmb] at this
  exact this

theorem dualGramAt_omFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ}
    (h : 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ) (hp : Γ.PosDef)
    (hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0) :
    DualGramAt 𝔐.M 𝔐.t.PP.L z (𝔐.Vgen (.inr τ)) (tie.omFrame F τ) (omBlock (blockG Γ)) := by
  refine ⟨dualFam tie F τ, omBlock Γ, hd, ?_, ?_⟩
  · have := gramAt_sub h (omEmb D.p D.q)
    simp only [gb_omEmb] at this
    exact this
  · have hpos : (omBlock Γ).PosDef := hp.submatrix (omEmb_strictMono D.p D.q).injective
    have hu : IsUnit (omBlock Γ).det := (Matrix.isUnit_iff_isUnit_det _).1 hpos.isUnit
    rw [omBlock_blockG, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    exact Matrix.nonsing_inv_mul _ hu

theorem baseMetricExists_of_given : Given → PB.BaseMetricExists := by
  intro hG E _ _ _ H D l Xo₀ c Y S K _ ι _ Φ _ y M 𝔐 tie d hp hq hcov hsnc
  classical
  obtain ⟨Xo, rfl⟩ : ∃ Xo : ∀ l' : Level H, Moduli D l', Xo l = Xo₀ :=
    ⟨Function.update (fun l' => (hG.1.2.1 E H D l' (by omega)).some) l Xo₀, Function.update_self ..⟩
  classical
  set n := Fintype.card (CMType H) * D.p * D.q with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Fintype.card (CMType H) := card_cmType_pos E H
    exact Nat.mul_pos (Nat.mul_pos this hp) hq
  obtain ⟨bd, hbd, hint⟩ := hsnc
  have harith := GlobalTheory.T.isArithVar_of_snc_model 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x n bd hn1 𝔐.tie hbd
  obtain ⟨hcl, htor, hconj⟩ := GlobalTheory.T.boundary_points_closed 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x
    (abLocus 𝔐.t.G) bd 𝔐.tie hint
  obtain ⟨Rb, L, s, nb, m, W, potL, sec, snc, norm_le, hbdry, hrconj⟩ :=
    GlobalTheory.T.lowerBound_height_on_boundary (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x n bd hbd harith hcl htor hconj
  obtain ⟨Bat, adapted⟩ := GlobalTheory.T.adapted_atlas_snc_section Rb.A L s m W potL sec snc norm_le
  have hInt : ∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) →
      (x ∉ bdry s ↔ 𝔐.Interior z) := fun x z hz => by
    rw [hbdry x, hint z _ hz, not_not]
  have hZ : IsClosed (bdry s) := GlobalTheory.T.isClosed_section_boundary n Rb.X Rb.A L s sec
  obtain ⟨q, O, F, hO, hOc, hF, hgood⟩ :=
    GlobalTheory.T.exists_finite_frame_cover K ι Φ y (CMType H) (D.p + D.q) D.p n M Rb
  have hgood' : ∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) :=
    fun l x hx => hgood l x (subset_closure hx)
  have hr : ∀ x, x ∉ bdry s → Real.exp 1 ≤ rW L s x := fun x _ => by
    have := norm_le x
    unfold rW
    linarith
  have hb := fun (i : Fin q) (τ : CMType H) => GlobalTheory.T.cutoff_function_on_compatible_atlas n D.p D.q Rb.X Rb.A Bat (bdry s) (closure (O i)) (O i) (rW L s)
    (baseGram tie (F i) τ Rb) adapted.1 adapted.2.1 adapted.2.2.1 hZ isClosed_closure (hO i) subset_closure hr
    (fun k w₀ hw₀ hc => GlobalTheory.T.flagModel_global_height_identity hG E H D Xo l c Y S K ι Φ y M 𝔐 tie n Rb L s Bat potL sec norm_le adapted hInt (F i)
      (hF i) τ k w₀ hw₀ (hgood i _ hc))
  choose C₀ hC₀ using fun i τ => (hb i τ).2
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ, ∀ i τ, C₀ i τ ≤ Cst := by
    refine ⟨∑ i, ∑ τ, |C₀ i τ|, fun i τ => ?_⟩
    calc C₀ i τ ≤ |C₀ i τ| := le_abs_self _
      _ ≤ ∑ τ, |C₀ i τ| := Finset.single_le_sum (f := fun τ => |C₀ i τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
      _ ≤ ∑ i, ∑ τ, |C₀ i τ| := Finset.single_le_sum (f := fun i => ∑ τ, |C₀ i τ|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hcoords : ∀ x : Rb.X, ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z (Rb.lift x x) := exists_coordsAt_lift E H D Xo l c Y S K ι Φ y M 𝔐 n Rb
  have hgr := fun (i : Fin q) (τ : CMType H) (x : Rb.X) (hx : x ∈ O i \ bdry s) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
      (hz : CoordsAt 𝔐.ξ M.x z (Rb.lift x x)) =>
    GlobalTheory.T.flagModel_frame_height_comparison E H D Xo l c Y S K ι Φ y M 𝔐 tie (F i) (hF i) τ (Rb.lift x x) z hz ((hInt x z hz).1 hx.2) (hgood' i x hx.1)
  obtain ⟨hom, hdeg, hind, hconjH⟩ := GlobalTheory.T.flagModel_resolution_integrability E H D Xo l c Y S K ι Φ y M 𝔐 tie n Rb s hInt q O F hOc hF hgood'
  have hper : ∀ i, ∀ x ∈ O i \ bdry s, ∃ V Pi, x ∈ V ∧
      IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F i) τ Rb x')) := by
    intro i x hx
    have := fun τ => GlobalTheory.T.exists_local_holo_isPeriodGram_blockG_baseGram hG E H D Xo l c Y S K ι Φ y M 𝔐 tie hp hq n Rb s hInt hZ (F i) (hF i) τ x hx.2 (hgood' i x hx.1)
    choose V P hV hxV hP hPG using this
    refine ⟨⋂ τ, V τ, P, Set.mem_iInter.2 hxV, isOpen_iInter_of_finite hV, fun τ a b => ?_, fun τ x' hx' => hPG τ x' (Set.mem_iInter.1 hx' τ)⟩
    intro k
    exact (hP τ a b k).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ τ)))
  obtain ⟨lI, xI, hxI, VI, PiI, hxV, hPer, himm⟩ := GlobalTheory.T.flagModel_height_lower_estimate hG E H D Xo l c Y S K ι Φ y M 𝔐 tie hp hq d hcov Rb s hInt hZ q O F hO hOc hF hgood'
  refine ⟨{ Rb := Rb, L := L, s := s, nb := nb, m := m, W := W, potL := potL, sec := sec, snc := snc, norm_le := norm_le,
            Bat := Bat, adapted := adapted, q := q, O := O, O_open := hO, O_cover := hOc, F := F, isFrame := hF, good := hgood'
            G := fun i τ x => blockG (baseGram tie (F i) τ Rb x)
            G_pos := ?_, G_smooth := fun i τ a b => (hb i τ).1 a b
            Cst := Cst
            size := fun i τ x hx => ((hC₀ i τ Cst (hCst i τ)).1 x ⟨subset_closure hx.1, hx.2⟩)
            grad := fun i τ a b k w hw hx => (hC₀ i τ Cst (hCst i τ)).2 a b k w hw ⟨subset_closure hx.1, hx.2⟩
            period := hper
            immersion := ⟨lI, xI, hxI, VI, PiI, hxV, hPer, himm⟩
            hom := hom, hom_deg := hdeg, induced := hind }, ?_, ?_⟩
  · intro i τ x hx
    obtain ⟨z, hz⟩ := hcoords x
    exact GlobalTheory.T.blockG_blockDiag_posDef D.p D.q _ (hgr i τ x hx z hz).2.1
  · refine ⟨hInt, fun i τ x hx z hz => ?_, fun i τ x hx z hz => ?_⟩
    · exact gramAt_wFrame tie (F i) τ (hgr i τ x hx z hz).1
    · exact dualGramAt_omFrame tie (F i) τ (hgr i τ x hx z hz).1 (hgr i τ x hx z hz).2.1 (hgr i τ x hx z hz).2.2
  · refine ⟨fun x x' ho => ?_, fun p z hz x hx ho => hconjH p z hz x hx ho⟩
    exact ⟨mem_bdry_conj_iff (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x n bd Rb s hbdry htor hconj x x' ho, hrconj x x' ho⟩

end GlobalTheory.CompanionTheory.Ar.PB.BMx
