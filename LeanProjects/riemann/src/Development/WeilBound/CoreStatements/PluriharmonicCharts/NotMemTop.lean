import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJLowerUniSwapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionOpenStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChooseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeEstimateStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalNormComparisonStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PRhoContinuousStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVSmul
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrabilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorMulSelf
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartImmersion
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

noncomputable section

namespace PositivityTheory.Xgp.c_smooth

theorem exists_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P)
    (hcov : ∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) :
    ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ),
      IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧
        ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
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

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb hd keep Kk _ ιk _ κ v hb hrng
  obtain ⟨e, he, ⟨ε⟩⟩ : ∃ e, e = n + Nat.card (PIdx j keep) ∧ Nonempty (Fin n ⊕ PIdx j keep ≃ Fin e) :=
    ⟨_, rfl, ⟨(Equiv.sumCongr (Equiv.refl _) (Finite.equivFin _)).trans finSumFinEquiv⟩⟩
  have hP : IsMultiHomogIdeal (mCoordIdeal (y ∘ v)) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
  have hnd : ¬ (⊤ : Ideal (MRing ιk)) ≤ mCoordIdeal (y ∘ v) := fun h =>
    (RingHom.ker_isPrime _ : (mCoordIdeal (y ∘ v)).IsPrime).ne_top (top_le_iff.mp h)
  have hcov := GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover.main K ι Φ y Ψ N j M n Rb keep Kk ιk κ v hb hrng
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h →
      ∃ C : OrbitChart (mCoordIdeal (y ∘ v)) e, C.D = pD ε V ∧ C.φ = pPhi M F keep v bl h ε ∧
        C.O = pO M Rb keep v F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.1.1
    have hh := GlobalTheory.T.frameData_local_resolution_regular K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hr := GlobalTheory.T.frameData_local_integrability K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ho := GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hO := GlobalTheory.T.frameData_local_degree_bound K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hb' := GlobalTheory.T.frameData_local_norm_comparison K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ht := GlobalTheory.T.frameData_local_norm_bound K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hi := GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm.chart_immersion K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    exact ⟨{ D := pD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := pPhi M F keep v bl h ε
             holo := hh
             mem := fun w hw => (hr w hw).1.1
             O := pO M Rb keep v F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := pRho M Rb keep v F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := exists_res (e := e) hP hnd (fun z hz => by
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
    obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
    exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = pD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (pPhi M F keep v bl h ε (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩
  have hob := (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hb hrng).2

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (pBase M v (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    refine ⟨(Rb.A.chart kb).symm (pB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := hob _ _ (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h → ψ.target = pD ε V → x ∈ ψ.source →
      SameOrbit (pPhi M F keep v bl h ε (ψ x)) (R.lift x x) →
      pr x = (Rb.A.chart kb).symm (pB ε (ψ x)) ∧ pr x ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    have h1 : SameOrbit (bl (pB ε (ψ x))) (pBase M v (R.lift x x)) := by
      have := hob _ _ hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (pB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_top _) h2
    have hwt : pB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨rfl, (Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  have hlast : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hψ, hT, hx, hs⟩ := key x
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun a b e' => Sum.inl_injective (ε.injective e')⟩, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨-, h1, h2⟩ := hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')
    exact ⟨h1, h2⟩
  refine ⟨e, R, ?_, pr, ?_, ?_, hlast⟩
  · intro hall
    rw [he, GlobalTheory.T.card_pIdx_eq_choose Ψ N j keep M.j_le hall, hd]
  · refine GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord e n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨ψ, kb, σ, h1, h2, h3⟩ := hlast x
    exact ⟨ψ, kb, σ, h1, h2, h3⟩
  · intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    obtain ⟨z₀, hz₀, hzv, hzb⟩ := GlobalTheory.T.frameData_local_degree_estimate K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    obtain ⟨hpe, -, -⟩ := hcoord x F kb V bl r h ψ hc hT hx (hs x hx)
    obtain ⟨c, hc0, hce⟩ := orbit_symm (hs x hx)
    let c' : K → ℂ := fun k => if hk : ∃ k', κ k' = k then c hk.choose else 1
    have hc'0 : ∀ k, c' k ≠ 0 := fun k => by
      simp only [c']
      split_ifs
      · exact hc0 _
      · exact one_ne_zero
    have hc'κ : ∀ k', c' (κ k') = c k' := fun k' => by
      have hk : ∃ k'', κ k'' = κ k' := ⟨k', rfl⟩
      simp only [c']
      rw [dif_pos hk, hb.1 hk.choose_spec]
    have hyP : IsMultiHomogIdeal (mCoordIdeal y) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
    refine ⟨fun p => c' p.1 * z₀ p, mcPts_smul hyP c' hc'0 hz₀, ?_, ?_⟩
    · funext q
      have e1 : z₀ (v q) = pPhi M F keep v bl h ε (ψ x) q := congrFun hzv q
      have e2 := congrFun hce q
      show c' (v q).1 * z₀ (v q) = _
      rw [e2, e1, hb.2.2.1 q, hc'κ]
    · have h1 : SameOrbit (fun q => c' q.1.1 * basePart M.blk z₀ q) (bl (pB ε (ψ x))) := by
        rw [hzb]
        exact ⟨fun k => c' k.1, fun k => hc'0 _, rfl⟩
      have h2 : (basePart M.blk fun p => c' p.1 * z₀ p) = fun q => c' q.1.1 * basePart M.blk z₀ q := rfl
      rw [h2, hpe]
      exact orbit_trans h1 (orbit_symm (hB.2.2.2.2 _ hw).2.2.2)

end PositivityTheory.Xgp.c_smooth
