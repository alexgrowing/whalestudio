import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSecMulPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanksStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwistRank

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem rkK_eq_of_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) : Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  have hmap : (Submodule.span K (L : Set V)).map (φ : V →ₗ[K] W) = Submodule.span K (L' : Set W) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro f hf
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    · rw [Submodule.span_le]
      intro g hg
      refine ⟨a⁻¹ • (a • φ.symm g), Submodule.smul_mem _ _ (Submodule.subset_span (R := K) (hout g hg)), ?_⟩
      show φ (a⁻¹ • (a • φ.symm g)) = g
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul, φ.apply_symm_apply]
  unfold Formalism.HN.rkK
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem rankOn_twist {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) :
    rankOn U Z (G + G₀) = rankOn U Z G := by
  obtain ⟨φ, -, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := Good.exists_twist_scalar s
  exact rkK_eq_of_equiv φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _))

theorem cuspW_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') :
    cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem rankOn_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : rankOn U Z G = rankOn U Z G' := by
  have e : cuspOn U Z G = cuspOn U Z G' := by rw [cuspOn, cuspOn, cuspW_congr hU h]
  unfold rankOn latOn
  rw [e]

theorem psi_nonempty : Nonempty (Psi H) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : φ (H.rt : E) = H.rt0
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨conjEmb φ, conj_mem h⟩⟩

theorem exists_twSec_par (hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {a : ℝ} (hF : FlatExistsAt U x a) (Z : Comp Xo c) (w : Psi H → ℤ) :
    Nonempty (TwSec U x Z (wtOf Dw (parWt Dw w) 0)) := by
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF Z τ).1.some
  obtain ⟨τ₀⟩ := psi_nonempty (H := H)
  have hp : HasPts U Z := (sF τ₀).hasPts
  let s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ) :=
    (FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _)
  refine ⟨TwSec.ofConst s (GlobalTheory.FlatTwisting.finite_sum_flDefect w) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq s)
    fun G hG f hf => ?_⟩
  have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl)
    (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
  rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem wtOf_zero_nat (k : ℕ) : wtOf Dw 0 (k : ℤ) = k • wtOf Dw 0 1 := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_smul]; exact wtOf_zero
  | succ k ih =>
    rw [succ_nsmul, ← ih, ← wtOf_add]
    simp

end Gen

end GlobalTheory.TwistRank

namespace GlobalTheory.TwistRank

theorem flat_twist_ranks : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → (∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ), Dom a n → Even n → Y.GoodAt (shiftG (T.Q.Dw j) a n s) → (Y.rk (shiftG (T.Q.Dw j) a n s) : ℝ) = ∑ᶠ Z, Y.rkC (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) Z := by
  intro hP D T hL j hp hq hE hj Y e o hY c₁ hF
  have hU := hY.unf
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hK : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
    obtain ⟨σ, hσ⟩ : ∃ σ, GoodEmb Y.d.c₂ σ := ⟨Y.d.c₂.F.val.toRingHom, rfl⟩
    obtain ⟨-, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
    exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F hpq hY.geo
  have part1 : ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z,
      Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z := by
    intro la w Z
    obtain ⟨t⟩ := exists_twSec_par hK hU hpq hF Z w
    show ((AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) 0) : ℕ) : ℝ) =
      ((AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℕ) : ℝ)
    rw [GlobalTheory.FlatLine.wtOf_add', rankOn_twist t _ (AllWt.even_wtOf _ _)]
  refine ⟨part1, ?_⟩
  intro a n kc s _hdom hn hgood
  have hR := GlobalTheory.T.supLattice_rank_eq_sum_component_ranks D T.Q.H (T.Q.Dw j) _ Y.d.Xo₂ Y.d.c₂ _ Y.U (xiR D) (fun _ => D.sp.W j) Y.dict
    (shiftG (T.Q.Dw j) a n s) hU hgood
  haveI : Finite (Comp Y.d.Xo₂ Y.d.c₂) := GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.finite_comp
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  show ((AllWt.rankW Y.U (shiftG (T.Q.Dw j) a n s) : ℕ) : ℝ) = _
  rw [hR]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  obtain ⟨m, hm⟩ := hn
  have hn2 : n / 2 = m := by omega
  set L := laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j) with hLdef

  have h1 : AllWt.rankOn Y.U Z (shiftG (T.Q.Dw j) a n s) = AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L (m : ℤ)) := by
    refine rankOn_congr hU Z ?_
    rw [hLdef, ← add_zero (m : ℤ), AllWt.wtOf_add, shiftG, GlobalTheory.FlatTw.exZ_add_eq, GlobalTheory.FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)
    rw [AllWt.exOf] at this
    rw [laOf, hn2] at *
    rw [this, wtZ]
    congr 2
    omega

  have h2 : AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L (m : ℤ)) = AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L 0) := by
    have he : wtOf (T.Q.Dw j) L (m : ℤ) = wtOf (T.Q.Dw j) L 0 + wtOf (T.Q.Dw j) 0 (m : ℤ) := by
      rw [← AllWt.wtOf_add, add_zero, zero_add]
    obtain ⟨t1⟩ := GlobalTheory.T.nonempty_twisted_section_component hP D T hL j hp hq hE hj Y e o hY c₁ hF Z
    obtain ⟨t, -⟩ := GlobalTheory.FlatTw.TwSec.exists_pow t1 m
    rw [he]
    exact rankOn_twist (t.copy (wtOf_zero_nat (Dw := T.Q.Dw j) m).symm) _ (AllWt.even_wtOf _ _)

  have h3 : L = (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a n kc) := by
    rw [hLdef, ← uWt_add_anchor (T.Q.Dw j) a n kc]; abel
  have h4 := part1 (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) (anchor (T.Q.Dw j) a n kc) Z
  rw [← h3] at h4
  rw [h1, h2]
  exact h4

end GlobalTheory.TwistRank
