import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopCountExponentBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTermsGramClassOverSublatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMeanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBotStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftedFlagLatticeChainSpansStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairLatticeLeLiftedPairLatticeSupIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonSublatticeSmallDetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesBoundedDetLeSumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndexStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntPrimLatticeImageIsometryStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PairMean

theorem cnt_triples {α γ ι : Type} {E : α → α → Prop} (hE : Equivalence E) (X : Set (α × α × γ))
    (R : α × α × γ → α × α × γ → Prop) (hR : ∀ p ∈ X, ∀ q ∈ X, R p q ↔ E p.1 q.1 ∧ E p.2.1 q.2.1)
    (S : Set ι) (Y₁ Y₂ : ι → Set α) (h : ∀ p ∈ X, ∃ i ∈ S, p.1 ∈ Y₁ i ∧ p.2.1 ∈ Y₂ i) (K : ℝ≥0∞) (hK : K ≠ 0)
    (h₁ : ∀ i ∈ S, (cntCl (Y₁ i) E : ℝ≥0∞) ≤ K) (h₂ : ∀ i ∈ S, (cntCl (Y₂ i) E : ℝ≥0∞) ≤ K) :
    (cntCl X R : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) * (K * K) := by
  rcases S.finite_or_infinite with hS | hS
  swap
  · rw [hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul (mul_ne_zero hK hK)]
    exact le_top
  lift S to Finset ι using hS
  let c : α → Set α := fun a => {b | E a b}
  have e1 : cntCl X R ≤ (⋃ i ∈ S, (c '' Y₁ i) ×ˢ (c '' Y₂ i)).encard := by
    refine le_trans (Set.encard_le_encard ?_)
      (Set.encard_image_le (fun C : Set α × Set α => {q | q ∈ X ∧ q.1 ∈ C.1 ∧ q.2.1 ∈ C.2}) _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, hi, a1, a2⟩ := h p hp
    refine ⟨(c p.1, c p.2.1), ?_, ?_⟩
    · simp only [Set.mem_iUnion]
      exact ⟨i, hi, ⟨_, a1, rfl⟩, ⟨_, a2, rfl⟩⟩
    · ext q
      exact and_congr_right fun hq => (hR p hp q hq).symm
  have e2 := e1.trans (FrEqv.encard_biUnion_le' S _)
  refine (ENat.toENNReal_le.2 e2).trans ?_
  rw [show ((∑ i ∈ S, ((c '' Y₁ i) ×ˢ (c '' Y₂ i)).encard : ℕ∞) : ℝ≥0∞) =
    ∑ i ∈ S, ((((c '' Y₁ i) ×ˢ (c '' Y₂ i)).encard : ℕ∞) : ℝ≥0∞) from map_sum ENat.toENNRealRingHom _ _]
  refine (Finset.sum_le_card_nsmul S _ (K * K) fun i hi => ?_).trans ?_
  · rw [Set.encard_prod, ENat.toENNReal_mul, ← FrEqv.cntCl_eq_encard hE, ← FrEqv.cntCl_eq_encard hE]
    exact mul_le_mul' (h₁ i hi) (h₂ i hi)
  · simp

theorem Xflag_top {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : LFlag S r T) : Xflag F r = Xsp F := by
  unfold Xflag Xsp FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

theorem X_le_L0sub {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : toO S (Xsp F) ≤ L0sub Λ F := by
  intro x hx
  refine ⟨⟨Submodule.mem_sup_right hx, FrEqv.X_le_orth hx⟩, ?_⟩
  have : Xsp F ≤ LinearMap.ker (S.hT F.fl.z) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact GlobalTheory.Mass.RowPerp.swap_zero S.herm (F.fl.z_orth a)
  exact this hx

theorem seen_mono (D : D7) {T : D.host.E} (F : Fg D T) {N N' : LatV D} (h : N ≤ N' ⊔ toO (hS D) (Xsp F)) :
    seen D F N ≤ seen D F N' :=
  Submodule.comap_mono (sup_le h le_sup_right)

theorem term_seen (D : D7) {T T' : D.host.E} (F : Fg D T) (F' : Fg D T') (Λ : LatV D) (hF : FixedHyp D Λ F)
    (hW : WHyp D F (Wsp D)) (h : IsTermF D Λ F F') :
    seen D F (La Λ (gS D) F F') ≤ L0X D Λ F ∧ seen D F (Thp Λ F F') ≤ seen D F (La Λ (gS D) F F') ∧
    rkW D (seen D F (Thp Λ F F')) = rkW D (seen D F (La Λ (gS D) F F')) ∧
    idxW D (seen D F (La Λ (gS D) F F')) (seen D F (Thp Λ F F')) = iIdx Λ (gS D) F F' := by
  obtain ⟨a1, -, a3⟩ := GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot _ _ _ _ _ Λ F F' hF.1 hF.2.2.1 h.1.1 h.1.2.2
  obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.liftedFlag_lattice_chain_spans _ _ _ _ _ Λ (gS D) F F' hF.1 hF.2.2.1 h.1.1
  have b4 : La Λ (gS D) F F' ≤ toO (hS D) (Hp Λ F F') := b2.trans inf_le_right
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index D T F _ hW a1 a3 _ _ b4 (b1.trans b4)
  obtain ⟨-, d2, -⟩ := GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index D T F _ hW a1 a3 _ _ (b1.trans b4) b4
  refine ⟨Submodule.comap_mono (sup_le (b2.trans inf_le_left) (X_le_L0sub Λ F)),
    seen_mono D F (b1.trans le_sup_left), ?_, c3⟩
  have : spanE (hS D) (La Λ (gS D) F F') = Hp Λ F F' :=
    le_antisymm (Submodule.span_le.2 b4) (b3.symm.le.trans (Submodule.span_mono b1))
  rw [c2, d2, b3, this]

theorem pair_sub (D : D7) {T T' : D.host.E} (F : Fg D T) (Λ : LatV D) (hF : FixedHyp D Λ F)
    (hW : WHyp D F (Wsp D)) (hpos : IsPosDef (D.sp.X 0).hT) (hfg : (L0X D Λ F).FG)
    (hint : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ F)) (Z' Z'' : GramM D) (s : ℕ) (hs : 1 ≤ s) (De : ℝ)
    (p : Trip D T') (hp : p ∈ PairSet D Λ T' F Z' Z'' s De) :
    ∃ P ∈ {P : LatW D | P ≤ L0X D Λ F ∧ rkW D P = D.R.k - s ∧ detW D P ≤ De},
      p.1 ∈ FrSet D Λ F T' Z' P ∧ p.2.1 ∈ FrSet D Λ F T' Z'' P := by
  obtain ⟨t1, t2, hpr, z1, z2, hs0, hd⟩ := hp
  obtain ⟨a1, a2, a3, a4⟩ := term_seen D F p.1 Λ hF hW t1
  obtain ⟨b1, b2, b3, b4⟩ := term_seen D F p.2.1 Λ hF hW t2
  obtain ⟨c1, -, c3⟩ := GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot _ _ _ _ _ Λ F p.1 hF.1 hF.2.2.1 t1.1.1 t1.1.2.2
  obtain ⟨-, d2, -, d4⟩ := GlobalTheory.T.liftedFlag_lattice_chain_spans _ _ _ _ _ Λ (gS D) F p.1 hF.1 hF.2.2.1 t1.1.1
  have hM : Mlat Λ F p.1 p.2.1 p.2.2 (gS D) ≤ La Λ (gS D) F p.1 := inf_le_left
  have hMH := hM.trans (d2.trans inf_le_right)
  obtain ⟨e1, e2, -⟩ := GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index D T F _ hW c1 c3 _ _ hMH hMH
  have m1 := seen_mono D F (hM.trans le_sup_left)
  have m2 := seen_mono D F (GlobalTheory.T.pairLattice_le_liftedPairLattice_sup_isotropic _ _ _ _ _ Λ (gS D) F p.1 p.2.1 p.2.2 hpr)
  obtain ⟨P, q1, q2, q3, q4, q5⟩ := GlobalTheory.T.exists_common_sublattice_small_det D _ _ _ _ _ _ hpos hfg hint m1 m2 a1 b1 a2 b2 a3 b3
  refine ⟨P, ⟨q1.trans (m1.trans a1), ?_, ?_⟩, ⟨t1, z1, q2⟩, ⟨t2, z2, q3⟩⟩
  · rw [q4, e2, d4]
    unfold s0 at hs0
    omega
  · rw [e1, a4, b4] at q5
    exact q5.trans hd

theorem pEqv_iff (D : D7) {T : D.host.E} {T' : ℕ} (hT' : 0 < T') (hg : 3 ≤ gS D) (F : Fg D T) (Λ : LatV D)
    (hF : FixedHyp D Λ F) (Z' Z'' : GramM D) (s : ℕ) (De : ℝ) (p : Trip D (T' : D.host.E))
    (hp : p ∈ PairSet D Λ (T' : D.host.E) F Z' Z'' s De) (q : Trip D (T' : D.host.E))
    (hq : q ∈ PairSet D Λ (T' : D.host.E) F Z' Z'' s De) :
    PEqv D Λ F p q ↔ TEqv D Λ F p.1 q.1 ∧ TEqv D Λ F p.2.1 q.2.1 := by
  constructor
  · rintro ⟨n', h', n'', h'', a, b, -⟩
    exact ⟨⟨n', h', a⟩, ⟨n'', h'', b⟩⟩
  · rintro ⟨⟨n', h', a⟩, ⟨n'', h'', b⟩⟩
    refine ⟨n', h', n'', h'', a, b, ?_⟩
    obtain ⟨t1, t2, hpr, -⟩ := hq
    obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.isPair_move_by_integralUnipotent D _ _ Λ (gS D) F p.1 p.2.1 q.1 q.2.1 p.2.2 n' n'' hp.2.2.1 h' h'' a b
    have hX := hpr.2.1 D.R.rS
    rw [Xflag_top, Xflag_top] at hX
    exact GlobalTheory.T.pair_isometry_unique_on_orth_mod_isotropic _ _ _ _ _ Λ (gS D) F q.1 q.2.1 q.2.2 _ hF.1 hF.2.1 hg (Nat.cast_ne_zero.2 hT'.ne')
      (GlobalTheory.T.trace_form_pos_on_orth_liftedFlag D T' q.1 hT')
      (GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag _ _ _ _ _ Λ (gS D) F q.1 hF.2.2.2 t1.2.1 t1.1.2.1)
      (GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag _ _ _ _ _ Λ (gS D) F q.2.1 hF.2.2.2 t2.2.1 t2.1.2.1)
      hpr.1 hX (by rw [hpr.2.2.1, sub_self]; exact Submodule.zero_mem _) hpr.2.2.2 c1 c2 c3 c4

theorem mean_le {ι : Type} (what₂ : Finset ι) (w cnt : ι → ℝ≥0∞) (N : ℕ → ι → ℝ≥0∞) (I : Finset ℕ) (c B : ℕ → ℝ)
    (K Bd : ℝ) (hK : 0 ≤ K) (hc : ∀ d ∈ I, 0 ≤ c d) (hB : ∀ d ∈ I, 0 ≤ B d)
    (h1 : ∀ i ∈ what₂, cnt i ≤ (∑ d ∈ I, N d i * ENNReal.ofReal (c d)) * (ENNReal.ofReal K * ENNReal.ofReal K))
    (h2 : ∀ d ∈ I, ∑ i ∈ what₂, w i * N d i ≤ (∑ i ∈ what₂, w i) * ENNReal.ofReal (B d))
    (h3 : (∑ d ∈ I, B d * c d) * K ^ 2 ≤ Bd) :
    ∑ i ∈ what₂, w i * cnt i ≤ (∑ i ∈ what₂, w i) * ENNReal.ofReal Bd := by
  calc ∑ i ∈ what₂, w i * cnt i
      ≤ ∑ i ∈ what₂, w i * ((∑ d ∈ I, N d i * ENNReal.ofReal (c d)) * (ENNReal.ofReal K * ENNReal.ofReal K)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (h1 i hi)
    _ = ∑ d ∈ I, (∑ i ∈ what₂, w i * N d i) * (ENNReal.ofReal (c d) * (ENNReal.ofReal K * ENNReal.ofReal K)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ d ∈ I, ((∑ i ∈ what₂, w i) * ENNReal.ofReal (B d)) *
          (ENNReal.ofReal (c d) * (ENNReal.ofReal K * ENNReal.ofReal K)) :=
        Finset.sum_le_sum fun d hd => mul_le_mul' (h2 d hd) le_rfl
    _ = (∑ i ∈ what₂, w i) * ENNReal.ofReal ((∑ d ∈ I, B d * c d) * K ^ 2) := by
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun d hd => mul_nonneg (hB d hd) (hc d hd)),
          ENNReal.ofReal_sum_of_nonneg (fun d hd => mul_nonneg (hB d hd) (hc d hd)), ENNReal.ofReal_pow hK,
          Finset.sum_mul I, Finset.mul_sum I]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [ENNReal.ofReal_mul (hB d hd)]
        ring
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h3)

theorem sum_bound (k : ℕ) (De N e e' l X X' : ℝ) (hDe : 1 ≤ De) (hN : 1 ≤ N) (he : 0 ≤ e) (hee : e ≤ e') (hl : 0 ≤ l)
    (hX : 0 ≤ X) (hXX : X ≤ X') :
    ∑ d ∈ Finset.Icc 1 ⌊De⌋₊, ((d : ℝ) / N) ^ k * ((d : ℝ) * N) ^ e * X * (De / d) ^ ((k : ℝ) + l + 1) ≤
      (De / N) ^ k * X' * (De ^ (4 + l) * (De * N) ^ e') := by
  have hD0 : 0 < De := by linarith
  have hN0 : 0 < N := by linarith
  have hX' : 0 ≤ X' := hX.trans hXX
  refine (Finset.sum_le_card_nsmul _ _ ((De / N) ^ k * X' * (De ^ (l + 1) * (De * N) ^ e')) fun d hd => ?_).trans ?_
  · obtain ⟨d1, d2⟩ := Finset.mem_Icc.1 hd
    have d1' : (1 : ℝ) ≤ d := by exact_mod_cast d1
    have d2' : (d : ℝ) ≤ De := (Nat.le_floor_iff hD0.le).1 d2
    have d0 : (0 : ℝ) < d := by linarith
    have a1 : ((d : ℝ) * N) ^ e ≤ (De * N) ^ e' :=
      (Real.rpow_le_rpow (by positivity) (by gcongr) he).trans
        (Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hDe hN) hee)
    have a2 : (De / d) ^ (l + 1) ≤ De ^ (l + 1) :=
      Real.rpow_le_rpow (by positivity) (div_le_self hD0.le d1') (by linarith)
    have a3 : (De / N) ^ k = ((d : ℝ) / N) ^ k * (De / d) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    rw [add_assoc, Real.rpow_add (by positivity), Real.rpow_natCast, a3]
    calc _ = ((d : ℝ) / N) ^ k * (De / d) ^ k * X * ((De / d) ^ (l + 1) * ((d : ℝ) * N) ^ e) := by ring
      _ ≤ _ := by gcongr
  · have a1 : De * De ^ (l + 1) ≤ De ^ (4 + l) := by
      calc De * De ^ (l + 1) = De ^ (1 + (l + 1)) := by rw [Real.rpow_add hD0 1, Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hDe (by linarith)
    have a2 : (⌊De⌋₊ : ℝ) ≤ De := Nat.floor_le hD0.le
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    calc _ ≤ De * ((De / N) ^ k * X' * (De ^ (l + 1) * (De * N) ^ e')) := by gcongr
      _ = (De / N) ^ k * X' * (De * De ^ (l + 1) * (De * N) ^ e') := by ring
      _ ≤ _ := by gcongr

theorem K_bound (s r f : ℕ) (De N H : ℝ) (hDe : 0 ≤ De) (hN : 0 ≤ N) (hH : 1 ≤ H) (h1 : De ≤ H) (h2 : N ≤ H) :
    N ^ (2 * r) * De ^ r * 9 ^ (s * f) * H ^ (9 * s + 9 * s * r + 16 * r ^ 2) ≤
      9 ^ (s * f) * (H ^ 8) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2) := by
  have hH0 : 0 ≤ H := by linarith
  calc _ ≤ H ^ (2 * r) * H ^ r * 9 ^ (s * f) * H ^ (9 * s + 9 * s * r + 16 * r ^ 2) := by gcongr
    _ = 9 ^ (s * f) * H ^ (3 * r + 9 * s + 9 * s * r + 16 * r ^ 2) := by ring
    _ ≤ _ := by
      rw [← pow_mul]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH ?_) (by positivity)
      nlinarith [Nat.zero_le (s * r), Nat.zero_le r, Nat.zero_le s]

theorem mass_nonneg (D : D7) (j : ℕ) : 0 ≤ massS D j := by
  unfold massS massU Formalism.HermitianLatticesTheory.mass
  split_ifs
  · positivity
  · exact le_rfl

theorem Xi_mono (D : D7) (u : D.what₂.Word) (HH C C' : ℝ) (s : ℕ) (hH : 1 ≤ HH) (hN : 1 ≤ NT D u) (hC : 0 ≤ C)
    (hCC : C ≤ C') : 0 ≤ XiS D u HH C s ∧ XiS D u HH C s ≤ XiS D u HH C' s := by
  unfold XiS Xi
  split_ifs
  · exact ⟨div_nonneg (mul_nonneg (mass_nonneg D _) (mass_nonneg D _)) (mass_nonneg D _), le_rfl⟩
  · have h1 := one_le_mul_of_one_le_of_one_le hH hN
    have h0 : 0 ≤ HH * NT D u := by linarith
    have hC' : 0 ≤ C' := hC.trans hCC
    refine ⟨by positivity, mul_le_mul (by gcongr) (Real.rpow_le_rpow_of_exponent_le h1 (by gcongr))
      (by positivity) (by positivity)⟩
  · exact ⟨le_rfl, le_rfl⟩

theorem one_le_sizeZ (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  have key : ∀ {ι : Type} (s : Finset ι) (f : ι → ℝ), (∀ i ∈ s, 1 ≤ f i) → 1 ≤ ∏ i ∈ s, f i := by
    intro ι s f h
    exact Finset.prod_induction f (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h
  exact key _ _ fun τ _ => key _ _ fun l _ => le_max_left _ _

theorem rpow_le_HHZ (D : D7) (b C x : ℝ) (hb : 1 ≤ b) (hC : 1 ≤ C) (hx : x ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f)
    (Z : GramM D) : b ^ x ≤ HHZ D b C Z := by
  have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have h1 : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f) := Real.one_le_rpow hb (by positivity)
  calc b ^ x ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f) := Real.rpow_le_rpow_of_exponent_le hb hx
    _ ≤ (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) :=
      Real.self_le_rpow_of_one_le h1 (one_le_mul_of_one_le_of_one_le hC hm)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (one_le_sizeZ D b C Z))

theorem main : ∀ Cg cb Cu cT CT C0 A Ad C₁ : ℝ, 0 ≤ C₁ → ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.UnitaryVolumeMass.stLem3L0 D u → Formalism.MainNotions.S.UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C₁ → Formalism.MainNotions.S.UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C := by
  intro Cg cb Cu cT CT C0 A Ad C₁ hC₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.count_terms_gramClass_over_sublattice Cg cb Cu cT CT C0 A
  obtain ⟨C₃, -, hC₃⟩ := GlobalTheory.loop_count_exponent_bound (max C₁ 1) (max Ad 1 * 8) (le_max_right _ _)
  refine ⟨max (max C₂ C₃) (max (max C₁ 1) |CT|), ?_⟩
  intro C hC D large₂ u u' C' Cl hCl _ H1 hyp F0 he hz what₂ hrows Z' Z'' r1 r2 s s2 sk De d1 d2
  simp only [ge_iff_le, max_le_iff] at hC
  obtain ⟨⟨c2, c3⟩, ⟨c1, c0⟩, cT'⟩ := hC
  rcases what₂.eq_empty_or_nonempty with rfl | ⟨Λ₀, hΛ₀⟩
  · simp [MeanLe]
  have hst : Stand D u u' := hyp.2.1
  have hbase : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨-, p1, p2, p3, p4, p5, -, g1, g2, -⟩ := id hst
  have hg : 3 ≤ gS D := by
    have := g1.two_le
    have := g2.two_le
    unfold gS
    nlinarith
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hT : Tr D u ≤ large₂.sc.b ^ (CT * D.R.m) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hyp.1.1
    exact (h u).2
  have hf : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact this
  have hm1 : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hm : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast (GlobalTheory.real_places_facts D).2.2.2.1
  have hN1 : 1 ≤ NT D u := one_le_pow₀ (by exact_mod_cast (show 1 ≤ Tu D u by omega))
  have o1 : 1 ≤ HHZ D large₂.sc.b C Z' := by simpa using rpow_le_HHZ D _ C 0 hb c0 (by positivity) Z'
  have o2 : 1 ≤ HHZ D large₂.sc.b C Z'' := by simpa using rpow_le_HHZ D _ C 0 hb c0 (by positivity) Z''
  have hN : NT D u ≤ HHZ D large₂.sc.b C Z' := by
    refine le_trans ?_ (rpow_le_HHZ D _ C (CT * D.R.m * (D.R.f : ℕ)) hb c0 ?_ Z')
    · rw [Real.rpow_mul_natCast (by linarith), NT]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hT _
    · refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have := le_abs_self CT
      nlinarith [mul_le_mul_of_nonneg_right (this.trans cT') (by linarith : (0 : ℝ) ≤ D.R.m),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (by linarith : (0 : ℝ) ≤ D.R.m))
          (by linarith : (0 : ℝ) ≤ D.R.m - 1)]
  have hHb : Hb large₂.sc.b C₁ D.R.m D.R.f ≤ HHZ D large₂.sc.b C Z' := rpow_le_HHZ D _ C _ hb c0 (by gcongr) Z'
  have q1 : HHZ D large₂.sc.b C Z' ≤ HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' := le_mul_of_one_le_right (by linarith) o2
  have q2 : HHZ D large₂.sc.b C Z'' ≤ HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' := le_mul_of_one_le_left (by linarith) o1
  generalize HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' = HH at q1 q2 d2 ⊢
  have hH : 1 ≤ HH := o1.trans q1
  have e1 : HH ≤ HH ^ max Ad 1 := Real.self_le_rpow_of_one_le hH (le_max_right _ _)
  have e2 : De ≤ HH ^ max Ad 1 := d2.trans (Real.rpow_le_rpow_of_exponent_le hH (le_max_left _ _))
  have e3 : (HH ^ max Ad 1) ^ 8 = HH ^ (max Ad 1 * 8) := by
    rw [← Real.rpow_mul_natCast (by linarith)]; norm_num
  have e4 : max (max Ad 1 * 8) 3 = max Ad 1 * 8 := max_eq_left (by linarith [le_max_right Ad 1])
  have e5 : 1 ≤ HH ^ max Ad 1 := hH.trans e1
  have e6 : De ≤ (HH ^ max Ad 1) ^ 3 := e2.trans (le_self_pow₀ e5 (by norm_num))
  have fin := hC₃ C c3 s D.R.rS D.R.f De (NT D u) HH (by omega) hf d1 hN1 hH
    (by rw [← e3]; exact e2.trans (le_self_pow₀ e5 (by norm_num))) (hN.trans q1)
  rw [e4, ← e3, ← hm] at fin
  have kb := K_bound s D.R.rS D.R.f De (NT D u) _ (by linarith) (by linarith) e5 e2 ((hN.trans q1).trans e1)
  have s23 := fun Λ hΛ Z hZ P hP hr hd hh => hC₂ C c2 D large₂ u u' C' Cl hCl hyp F0 he hz Λ hΛ Z hZ s (by omega) sk P hP hr
    De (HH ^ max Ad 1) d1 hd hh e6
  have k0 : 0 < NT D u ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
    (HH ^ max Ad 1) ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2) := by positivity
  generalize NT D u ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
    (HH ^ max Ad 1) ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2) = K at kb s23 k0
  obtain ⟨x0, x1⟩ := Xi_mono D u HH C₁ C s hH hN1 hC₁ c1
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have lf0 : 0 ≤ Real.log D.R.f := Real.log_nonneg hf'
  have l0 : 0 ≤ lg2f D.R.f := Real.logb_nonneg (by norm_num) (by linarith)
  obtain ⟨-, -, hpos, hlat₀, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ₀ hst hbase (hrows.1 Λ₀ hΛ₀)
  obtain ⟨⟨reps, hreps⟩, -, hmass⟩ := Formalism.HermitianLatticesTheory.final_massBasic _ _ (D.sp.X 0).hT (D.sp.X 0).herm
    (GlobalTheory.Mass.GenusOrb.trace_pos_of_PD _ hpos) _ hlat₀
  refine mean_le what₂ _ _ (fun d Λ => (cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) d : ℝ≥0∞))
    (Finset.Icc 1 ⌊De⌋₊) (fun d => (De / (d : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1))
    (fun d => ((d : ℝ) / NT D u) ^ D.R.k * ((d : ℝ) * NT D u) ^ (C₁ * s + C₁ * Real.log D.R.f) * XiS D u HH C₁ s)
    K _ k0.le (fun d _ => by positivity) (fun d _ => by positivity) (fun Λ hΛ => ?_) (fun d hd => ?_) ?_
  · have hR := hrows.1 Λ hΛ
    obtain ⟨hW, -, -, hlat, hint, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hst hbase hR
    refine (cnt_triples (FrEqv.TEqv_equivalence D Λ (lf D F0)) _ _
      (pEqv_iff D (by omega) hg _ Λ hR.2.1 Z' Z'' s De) _ _ _
      (pair_sub D _ Λ hR.2.1 hW hpos hlat.fg hint Z' Z'' s (by omega) De) (ENNReal.ofReal K)
      (ENNReal.ofReal_pos.2 k0).ne' (fun P hP => s23 Λ hR Z' r1 P hP.1 hP.2.1 hP.2.2 (q1.trans e1))
      (fun P hP => s23 Λ hR Z'' r2 P hP.1 hP.2.1 hP.2.2 (q2.trans e1))).trans (mul_le_mul' ?_ le_rfl)
    exact GlobalTheory.T.encard_sublattices_bounded_det_le_sum D _ hpos (GlobalTheory.Mass.RowPerp.main D u F0 he hz).1.2 hlat.fg hint _ De d1
  · have a1 := GlobalTheory.T.rowLattices_mean_eq_genus_mean D u p1 p3 p5 F0 he hz what₂ hrows Λ₀ (hrows.1 Λ₀ hΛ₀) reps hreps
      (fun L => cntPrim (D.sp.X 0).hT L (D.R.k - s) d) (fun γ hγ L => GlobalTheory.T.cntPrim_latticeImage_isometry _ _ _ γ hγ L _ _)
    have a2 := H1 hyp F0 he hz Λ₀ (hrows.1 Λ₀ hΛ₀) reps hreps s s2 sk d (Finset.mem_Icc.1 hd).1 HH (hHb.trans q1)
    rw [ENNReal.ofReal_mul hmass.le] at a2
    refine (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hmass).ne' ENNReal.ofReal_ne_top).1 ?_
    rw [a1, mul_assoc]
    exact mul_le_mul' le_rfl (a2.trans (mul_comm _ _).le)
  · have a1 := sum_bound D.R.k De (NT D u) (C₁ * s + C₁ * Real.log D.R.f)
      (max C₁ 1 * s + max C₁ 1 * Real.log D.R.f) (lg2f D.R.f) _ _ d1 hN1 (by positivity)
      (by have := le_max_left C₁ 1; gcongr) l0 x0 x1
    have x2 := x0.trans x1
    refine (mul_le_mul a1 (pow_le_pow_left₀ k0.le kb 2) (by positivity) (by positivity)).trans ?_
    rw [mul_assoc ((De / NT D u) ^ D.R.k * XiS D u HH C s), mul_assoc ((De / NT D u) ^ D.R.k * XiS D u HH C s)]
    exact mul_le_mul_of_nonneg_left fin (by positivity)

end GlobalTheory.LoopC.PairMean
