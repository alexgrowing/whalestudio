import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PiNSOfPi
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfD
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
import Formalism.SharpRestriction.LevelLetterCocycles.DdRFull

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem u1r2_pt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    LevelExpansions.V.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hz : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨hQ0, hQ1⟩ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hz
  obtain ⟨-, -, -, p4, -⟩ := hA l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : ∀ i, PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev i 1 letπ) = 0 := fun i => by
    rw [CrystallineExponents.cc_lev_pi _ i 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  refine ⟨hT, ⟨1, by simpa using hz⟩, hz.pow_eq_one, hQ0, hQ1, fun x k hk => ?_,
    fun x hx => ((HW l).W K 1 LL hG).N_φ T x hx⟩
  exact (((p4 T hT).1 (c - 1) 1 ⟨0, one_pow _⟩ (by rw [hX]; exact hπ1 _)).1 x k).2 hk

theorem u1r2_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  classical
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have p9 := (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1
  have h92 := (p9 T hT hs hp2).2.1
  obtain ⟨π₀, E₀, -, hm⟩ := h92
  obtain ⟨⟨r, b, hbΔ, hbu, hbe⟩, -⟩ := hm
  have hw := hp9.2.2.1
  obtain ⟨w₁, hw₁⟩ := hw
  have hs1 : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hBL := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs1 w₁ hw₁ hp9.2.1 b hbΔ hbu hbe c
  obtain ⟨bL⟩ := hBL
  have hsurj : ∀ k, ∃ y : ((HW l).W K 1 LL hG).DD T, ∃ hy : y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1),
      bL k = mkL ((HW l).W K 1 LL hG) T π' c y hy := by
    intro k
    have hq := Submodule.Quotient.mk_surjective _ (bL k)
    obtain ⟨⟨y, hy⟩, hyk⟩ := hq
    exact ⟨y, hy, hyk.symm⟩
  choose rep hrep hbr using hsurj
  exact ⟨r, bL, rep, hrep, hbr⟩

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames

end
