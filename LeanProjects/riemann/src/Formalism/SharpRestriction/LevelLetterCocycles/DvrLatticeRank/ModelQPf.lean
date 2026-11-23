import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfD
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

set_option maxHeartbeats 1000000 in
theorem modelqlink_pf : ModelQLinkStep := by
  intro D HW F Cm CA CB CK hA hML l hpf hl K LL hG π' E hR h' hh' T hT hJ c
  have hL := hML l hl K LL hG π' E hR h' hh' T hT hJ c
  obtain ⟨hL1, -, -, hL4, hL5, -, -⟩ := hL
  have h1 : adm1 D HW F Cm := hA.1
  have hs : 1 ≤ sK l K := by
    have := frobpin_sK_pos hl K LL hG
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hπu, hπΔ, -⟩ := gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
  obtain ⟨w₁, hw₁⟩ := hR.2.2.1
  obtain ⟨w₂, hw₂⟩ := hR.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨hcard, -, -⟩ := h9W T hT hs1 hp
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨r, b, hbΔ, hbu, hbe⟩ := hm₀.1
  haveI hdvr : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  obtain ⟨bL⟩ := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs w₁ hw₁ hR.2.1 b hbΔ hbu hbe c
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hcpos : 0 < ((HW l).W K 1 LL hG).DelF.card := by
    refine Finset.card_pos.2 ⟨1, ((HW l).W K 1 LL hG).DelF_def 1 |>.2 ⟨1, one_pos, one_pow _⟩⟩
  have hclt : ((HW l).W K 1 LL hG).DelF.card < l := by
    rw [hcard, hpl]
    have := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hΔu : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    gradNPf_unit_nat ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hpf.out hlv _
      (Nat.not_dvd_of_pos_of_lt hcpos hclt)
  have hpP : ((D.loc l).PD K).p.Prime := by rw [hpl]; exact hpf.out
  haveI hcompl : IsAdicComplete (Ideal.span {(((D.loc l).PD K).p : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact FrobeniusSpanLemma.phib_OL_complete LL
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    show ∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π'
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply,
      show ((HW l).W K 1 LL hG).γ₀ δ (π' i) = π' i from congrFun (hπΔ δ hδ) i]
  have hEe : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = ((w₂⁻¹ : (LetA ↥(OL LL) _)ˣ) : LetA ↥(OL LL) _) * ((HW l).W K 1 LL hG).q := by
    rw [hw₂, ← mul_assoc, Units.inv_mul, one_mul]
  have hEu : IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    rw [hEe, map_mul]
    exact ((w₂⁻¹).isUnit.map _).mul (MQ.q_unit ((HW l).W K 1 LL hG) hpP)
  obtain ⟨D', S, hdiv⟩ := MQ.div_at ((HW l).W K 1 LL hG) hpP (sK l K) h' π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w₁ w₂ hw₁ hw₂
    hΔu.unit hΔu.unit_spec hR.1 hEΔ c
  have hp0 : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := by
    intro h0
    have : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((D.loc l).PD K).p : ↥(OL LL))) = 1 := by
      rw [map_natCast, hpl]; exact hlv
    rw [h0, map_zero, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have hpu : ¬ IsUnit (((D.loc l).PD K).p : ↥(OL LL)) := by
    intro hU
    obtain ⟨bb, hbb⟩ := hU.exists_right_inv
    have e := congrArg (fun z => (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 z)) hbb
    simp only [map_mul, map_one, AddValuation.map_mul, AddValuation.map_one] at e
    rw [map_natCast, hpl, hlv] at e
    have hb0 : 0 ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 bb) := (hRv _).2 ⟨bb, rfl⟩
    revert e hb0
    generalize (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 bb) = z
    intro e hb0
    induction z using WithTop.recTopCoe with
    | top => simp at e
    | coe q =>
      have e' : (1 + q : ℚ) = 0 := by exact_mod_cast e
      have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hb0
      linarith
  refine ⟨MQ.finite_of (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c hEu hL4
    (MQ.finite_L ((HW l).W K 1 LL hG) T π' (sK l K) hs w₁ hw₁ hR.2.1 b hbΔ hbu hbe c) D' S hdiv, ?_⟩
  exact MQ.tf_of (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c hπu hL1 hL5
    (MQ.sat_of π' c bL (MQ.hlet_of ((HW l).W K 1 LL hG) (sK l K) hs π' w₁ hw₁ hR.1 hπu c))
    (MQ.dvd_pow_of_dvr _ hp0 hpu)

end Formalism.MainNotions.N.Ln34
