import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDat
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHyp

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

include Ct in

theorem framepf_data' [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (l : ℕ) (hl : PD.p = l)
    (hyp : Nonempty (FramepfBas W T) ∧ (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧
      (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ a ∈ W.AΔ, ∃! f : ZMod n → PowerSeries O, ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
      (∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0) ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) ∧ W.gamK = W.gam ∧
      ∃ Fs : PowerSeries O,
        W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
        PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s' ∧
        (∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) ∧
        ∃ aσ : O, (l : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : ∀ (Bs : FramepfBas W T) hπ0 hΔπ hR2 γ0 hu,
      FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  obtain ⟨⟨Bs⟩, hπ0, hΔπ, hR2, γ0, hu, hγN, hK, Fs, hFs, hF0, hne, aσ, haσ⟩ := hyp
  exact framepf_data Ct T hι hT hs Pt c hprim h4 hR hs' h' M σ hM1 hM hK
    Bs hπ0 hΔπ hR2 γ0 hu hγN Fs hFs hF0 hne aσ (by rw [hl]; exact haσ) (hB Bs hπ0 hΔπ hR2 γ0 hu)

end Local

set_option maxHeartbeats 1000000 in

theorem framepf_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hB : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (Bs : FramepfBas ((HW l).W K 1 LL hG) T) hπ0 hΔπ hR2 γ0 hu,
        IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) →
        Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ → ∀ u ∈ ((HW l).W K 1 LL hG).AΔ,
        ((HW l).W K 1 LL hG).φA π' ^ MK l K h' = π' ^ MK l K h' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') * u →
        FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')) :
    FrameA ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
      (sigA l (sK l K) h') c := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hK : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam := ((HW l).W K 1 LL hG).gamK_eq_one hs hp2
  have hs' := ramification_quotient_pos l hl K LL hG
  have hM : 4 * h' ≤ sK l K * MK l K h' := by
    have hsR : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs'
    have hc : (4 * h' : ℝ) / (sK l K : ℝ) ≤ (MK l K h' : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hsR] at hc
    have h4 : ((4 * h' : ℕ) : ℝ) ≤ ((sK l K * MK l K h' : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have hM1 : 1 ≤ MK l K h' := by
    rcases Nat.eq_zero_or_pos (MK l K h') with h0 | h0
    · rw [h0, mul_zero] at hM
      omega
    · exact h0
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨u, huΔ, hφ⟩ := framepf_φπ hR hs h' _ hM
  obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
  obtain ⟨t, htΔ, ht⟩ := framepf_γE hR hs ((HW l).W K 1 LL hG).gamK
  obtain ⟨t', ht'Δ, ht'⟩ := framepf_γE' hR hs ((HW l).W K 1 LL hG).gamK
  have huE := framepf_E_unit hR hs
  refine framepf_frameA _ _ π' _ h' _ _ c hK (framepf_π_unit hR) huE hR.1 u huΔ hφ hfΔ
    (by rw [hK]; exact hf) htΔ ht ht'Δ ht' fun T hT => ?_
  exact framepf_data' ((Cm l).C K 1 LL hG).tie T hι hT hs _ c hprim ((h1 l K 1 LL hG).2.2.2.1 T hT) hR
    hs' h' _ _ hM1 hM l hpl (framepf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT c h')
    fun Bs hπ0 hΔπ hR2 γ0 hu => hB T hT Bs hπ0 hΔπ hR2 γ0 hu huE (framepf_E_Δ hR) u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
