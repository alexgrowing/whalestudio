import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdMaxInvLeProdMax
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFlagPairLatticeSumDiscriminantEqNormMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalFormStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc

namespace GlobalTheory.TypeAsm.CompatibleChartOperations
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Amp in

theorem prod_degBd_le_explicit (C' : ℝ) (ι : Type) [Fintype ι] (k r j q : ℕ) (H₁ : ℝ) (Dm : ι → Fin (r + 1) → ℝ)
    (De D sg : ι → ℝ) (hj : 1 ≤ j) (hjr : j ≤ r) (hk5 : 5 * r ≤ k) (hk : 40 * r ^ 4 ≤ k)
    (hq : q = (⌈C'⌉₊ + 2) * k * r) (hH : 1 ≤ H₁)
    (hD : ∀ l, (∀ v, Dm v l = 0) ∨ ((∀ v, 0 < Dm v l) ∧ 1 ≤ ∏ v, Dm v l))
    (hDe : ∀ v, De v = Finset.univ.fold max 1 fun l => (Dm v l)⁻¹)
    (hsg : ∀ v, sg v = Finset.univ.fold max 1 fun l => Dm v l / (2 * H₁) ^ (2 * r)) (hD0 : ∀ v, 0 < D v) :
    ∏ v, degBd k r j q H₁ (De v) (D v) (sg v) ≤
      (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * Fintype.card ι) * ((∏ v, D v) ^ (k - 1 - j))⁻¹ *
        (8 * r * H₁) ^ (80 * r ^ 4 * Fintype.card ι) * ∏ v, sg v ^ (-(C' * k)) := by
  have hr : 1 ≤ r := hj.trans hjr
  have hC : C' + 2 ≤ ((⌈C'⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil C']
  have hP : (1 : ℝ) ≤ (2 * H₁) ^ (2 * r) := one_le_pow₀ (by linarith)
  have hs1 : ∀ v, 1 ≤ sg v := fun v => by rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  have hs0 : ∀ v, 0 < sg v := fun v => lt_of_lt_of_le one_pos (hs1 v)
  have hDe0 : ∀ v, 0 ≤ De v := fun v => by
    rw [hDe v]; exact (Finset.le_fold_max _).2 (Or.inl zero_le_one)
  have hprod := prod_fold_inv_le _ hP Dm De sg hD hDe hsg
  have hprod2 : ∏ v, De v ^ (8 * r ^ 2 + 2) ≤ ∏ v, ((2 * H₁) ^ (2 * r) * sg v) ^ ((r + 1) * (8 * r ^ 2 + 2)) := by
    simp only [pow_mul _ (r + 1)]
    rw [Finset.prod_pow, Finset.prod_pow _ (8 * r ^ 2 + 2)]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => hDe0 v) hprod _
  have hB : 8 * Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ) ≤ 16 * Real.pi * Real.exp 1 / k := by
    have h1 : k ≤ 2 * (k - 1 - j) := by omega
    have h2 : 0 < k - 1 - j := by omega
    have h1' : (k : ℝ) ≤ 2 * ((k - 1 - j : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : (0 : ℝ) < ((k - 1 - j : ℕ) : ℝ) := by exact_mod_cast h2
    have h3 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have h4 : 0 < Real.pi * Real.exp 1 := by positivity
    rw [div_le_div_iff₀ h2' h3]
    nlinarith
  have hA := const_loss_le r hr H₁ hH
  set A : ℝ := 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  set B : ℝ := 8 * Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set e : ℝ := -(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r) with he
  have hrest : ∀ v, 0 ≤ A * B ^ (j * (k - 1 - j)) * (D v ^ (k - 1 - j))⁻¹ * sg v ^ e := fun v => by
    have := hD0 v; have := hs0 v; positivity
  calc ∏ v, degBd k r j q H₁ (De v) (D v) (sg v)
      = (∏ v, De v ^ (8 * r ^ 2 + 2)) * ∏ v, A * B ^ (j * (k - 1 - j)) * (D v ^ (k - 1 - j))⁻¹ * sg v ^ e := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        unfold degBd
        rw [← hAdef, ← hBdef, ← he]; ring
    _ ≤ (∏ v, ((2 * H₁) ^ (2 * r) * sg v) ^ ((r + 1) * (8 * r ^ 2 + 2))) *
          ∏ v, A * B ^ (j * (k - 1 - j)) * (D v ^ (k - 1 - j))⁻¹ * sg v ^ e :=
        mul_le_mul_of_nonneg_right hprod2 (Finset.prod_nonneg fun v _ => hrest v)
    _ = ∏ v, B ^ (j * (k - 1 - j)) * (D v ^ (k - 1 - j))⁻¹ * (A * ((2 * H₁) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2))) *
          (sg v ^ ((r + 1) * (8 * r ^ 2 + 2)) * sg v ^ e) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [mul_pow ((2 * H₁) ^ (2 * r))]; ring
    _ ≤ ∏ v, (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j)) * (D v ^ (k - 1 - j))⁻¹ * (8 * r * H₁) ^ (80 * r ^ 4) *
          sg v ^ (-(C' * k)) := by
        refine Finset.prod_le_prod (fun v _ => ?_) fun v _ => ?_
        · have := hD0 v; have := hs0 v; positivity
        · have h1 := hD0 v
          have h2 := hs0 v
          have h3 : sg v ^ ((r + 1) * (8 * r ^ 2 + 2)) * sg v ^ e ≤ sg v ^ (-(C' * k)) := by
            rw [he, hq]; exact size_loss_le C' _ k r hC hr hk _ (hs1 v)
          have h4 : B ^ (j * (k - 1 - j)) ≤ (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j)) :=
            pow_le_pow_left₀ hB0 hB _
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h4 (by positivity)) hA (by positivity) (by positivity))
            h3 (by positivity) (by positivity)
    _ = _ := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, Finset.prod_inv_distrib,
          Finset.prod_pow]

theorem frameExp_int (r l : ℕ) (hl : l ≤ r + 1) :
    ((frameExp r l : ℕ) : ℤ) = ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    have h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l := by omega
    rw [h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]

theorem nloc_norm (D : D7) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) =
      |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by
  unfold Nloc
  rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀,
    show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) from rfl,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

theorem norm_of_star (D : D7) (x : D.host.E) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x := by
  have := Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x
  simpa using this

theorem one_le_nloc {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word} (hS : Std D large₂)
    {t : GTu Y u} (ht : t ∈ relSet Y u) (l : ℕ) (hl : l ≤ D.R.rS)
    (h0 : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l ≠ 0) :
    1 ≤ ((Nloc (ddS D) D.R.rS l (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l) : ℚ) : ℝ) := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := by
    obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := hS
    exact hH.2.2.2.2.2.2.2
  obtain ⟨N, hN, -, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS t ht
  have hT : N.IsTerm (gS D) t.lam := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hS t N hN
  obtain ⟨-, -, -, -, -, hDl, hz, -, -⟩ :=
    GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN
  have hl' : l ≤ D.R.rS + 1 := by omega
  have hnf : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl') :=
    nf_Dl _ _ _ _ l hl'
  have hlj : l ≤ N.j := by
    by_contra hlt
    apply h0
    rw [hnf, hz l hl' (by omega) hl, star_zero]
  have hd : N.𝔡 = dI D := hN.1
  have hdne : dI D ≠ ⊥ := hd ▸ N.𝔡_ne
  have key : N.nD l = ((Nloc (ddS D) D.R.rS l (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l) : ℚ) : ℝ) := by
    unfold GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl', hDl l hl', nloc_norm, hnf, norm_of_star, hd, frameExp_int _ _ hl']
  have hne : N.nD l ≠ 0 := by
    rw [key, nloc_norm]
    have hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hdne)
    refine mul_ne_zero ?_ (zpow_ne_zero _ hA)
    rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
    exact h0
  rw [← key]
  exact (GlobalTheory.DegCnt.FlagDisc.main D.host.E (VS D).V (HV D) hK D.R.rS N (gS D) t.lam (Formalism.MainNotions.LatticeGluingRadicals.d_gS_pos D) hT l
    hlj hne).2

end GlobalTheory.TypeAsm.CompatibleChartOperations

namespace GlobalTheory.TypeAsm
open GlobalTheory.TypeAsm.CompatibleChartOperations
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prodC_holds : ProdC := by
  intro Cs hCs
  refine ⟨⌈Cs⌉₊ + 2, by omega, ?_⟩
  intro D large₂ X Y u C CH hS hCH hk4 hk5 t ht hj hj1
  obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := id hS
  have hPF : PFHost D := PFHost_of_data D hH.1.2.1
  have hrd := pf_rd_pos D
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨Dm, hDm⟩ : ∃ Dm : D.what₂.Tau → Fin (D.R.rS + 1) → ℝ, ∀ τ l, Dm τ l =
      ‖Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) l.castSucc‖ :=
    ⟨fun τ l => _, fun _ _ => rfl⟩
  have hgram : ∀ τ (l : Fin (D.R.rS + 1)),
      Dm τ l = absReal D.host.rdE (embS D τ) D.R.rS l.val (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l.val) := by
    intro τ l
    rw [hDm]
    exact ((GlobalTheory.T.realPointGramMinorsAgree_proof D X Y u C τ).2 t).2.2 l
  have hD : ∀ l : Fin (D.R.rS + 1), (∀ v, Dm v l = 0) ∨ ((∀ v, 0 < Dm v l) ∧ 1 ≤ ∏ v, Dm v l) := by
    intro l
    by_cases h0 : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l.val = 0
    · left
      intro v
      rw [hgram, h0]
      simp [absReal]
    · right
      have hpos : ∀ v, 0 < Dm v l := fun v => by
        rw [hgram]
        unfold absReal
        exact mul_pos (norm_pos_iff.2 ((map_ne_zero _).2 h0)) (Real.rpow_pos_of_pos hrd _)
      refine ⟨hpos, ?_⟩
      have h1 := one_le_nloc hS ht l.val (by omega) h0
      rw [hPF] at h1
      have h2 : (∏ v, Dm v l) ^ 2 =
          ∏ v, absReal D.host.rdE (embS D v) D.R.rS l.val (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l.val) ^ 2 := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun v _ => by rw [hgram]
      have h3 : 0 ≤ ∏ v, Dm v l := Finset.prod_nonneg fun v _ => (hpos v).le
      nlinarith
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj', c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hDj0 : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl (jT t) ≠ 0 := by
    rw [hjT]; exact (nf_gen _ _ _ _ j hj' c hN).2.2.2.1
  have hjr : jT t < D.R.rS + 1 := by omega
  have hDjpos : ∀ τ, 0 < Dm τ ⟨jT t, hjr⟩ := fun τ => by
    rw [hgram]
    unfold absReal
    exact mul_pos (norm_pos_iff.2 ((map_ne_zero _).2 hDj0)) (Real.rpow_pos_of_pos hrd _)
  have hDjEq : ∀ τ, GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) =
      Dm τ ⟨jT t, hjr⟩ := by
    intro τ; rw [hDm]; rfl
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∏ τ, Dm τ ⟨jT t, hjr⟩ := ⟨_, rfl⟩
  have hP : 0 < P := by rw [hPdef]; exact Finset.prod_pos fun τ _ => hDjpos τ
  have hdel : k2Del D (jT t) (labT t) = P ^ 2 := by
    unfold k2Del
    rw [hPF, hPdef, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hgram τ ⟨jT t, hjr⟩]
    simp only [labT, if_pos le_rfl]
  set De : D.what₂.Tau → ℝ := fun τ => Finset.univ.fold max 1 fun l => (Dm τ l)⁻¹ with hDedef
  have hDeOK : ∀ τ, GlobalTheory.Amp.DeOK D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (De τ) := by
    intro τ
    refine ⟨(Finset.le_fold_max _).2 (Or.inl le_rfl), fun l hl hne => ?_⟩
    have hl' : l = (⟨l.val, by omega⟩ : Fin (D.R.rS + 1)).castSucc := Fin.ext rfl
    refine (Finset.le_fold_max _).2 (Or.inr ⟨⟨l.val, by omega⟩, Finset.mem_univ _, le_of_eq ?_⟩)
    rw [hDm, ← hl']
  have hmain := prod_degBd_le_explicit Cs D.what₂.Tau D.R.k D.R.rS (jT t) ((⌈Cs⌉₊ + 2) * D.R.k * D.R.rS) (H1C large₂ CH)
    Dm De (fun τ => GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ))
    (fun τ => GlobalTheory.Amp.sgV D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (H1C large₂ CH))
    hj1 hj hk5 hk4 rfl hH1 hD (fun v => rfl) (fun v => by unfold GlobalTheory.Amp.sgV; simp only [hDm])
    (fun v => by rw [hDjEq]; exact hDjpos v)
  have hcard := Formalism.MainNotions.BridgeLemma.szf_card_Tau D
  have hprodD : ∏ τ, GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) = P := by
    rw [hPdef]; exact Finset.prod_congr rfl fun τ _ => hDjEq τ
  rw [hcard, hprodD] at hmain
  refine ⟨De, P, hP, hdel, hDeOK, hmain.trans ?_⟩
  have hsgle : ∏ τ, GlobalTheory.Amp.sgV D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (H1C large₂ CH) ^
      (-(Cs * D.R.k)) ≤ k2S D (H1C large₂ CH) (jT t) (labT t) ^ (-(Cs * (D.R.k : ℝ))) := by
    unfold k2S
    rw [← Real.finset_prod_rpow _ _ (fun τ _ => zero_le_one.trans (one_le_minor_sigma _ _ _ τ))]
    refine Finset.prod_le_prod (fun τ _ => ?_) fun τ _ => ?_
    · refine Real.rpow_nonneg ?_ _
      unfold GlobalTheory.Amp.sgV
      exact (Finset.le_fold_max _).2 (Or.inl zero_le_one)
    · refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (one_le_minor_sigma _ _ _ τ)) ?_
        (neg_nonpos.2 (mul_nonneg hCs (Nat.cast_nonneg _)))
      unfold k2sg
      refine (Finset.fold_max_le _).2 ⟨?_, fun l hl => ?_⟩
      · unfold GlobalTheory.Amp.sgV
        exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
      · have hlj : l ≤ jT t := by
          unfold k2ends at hl
          exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hl).1).2
        have hlr : l < D.R.rS + 1 := by omega
        unfold GlobalTheory.Amp.sgV
        refine (Finset.le_fold_max _).2 (Or.inr ⟨⟨l, hlr⟩, Finset.mem_univ _, le_of_eq ?_⟩)
        rw [← hDm, hgram τ ⟨l, hlr⟩]
        simp only [labT, if_pos hlj]
  have hA : 0 ≤ (16 * Real.pi * Real.exp 1 / D.R.k) ^ (jT t * (D.R.k - 1 - jT t) * D.R.f) * (P ^ (D.R.k - 1 - jT t))⁻¹ *
      (8 * D.R.rS * H1C large₂ CH) ^ (80 * D.R.rS ^ 4 * D.R.f) := by
    have := hP.le
    have : 0 ≤ H1C large₂ CH := by linarith
    positivity
  exact mul_le_mul_of_nonneg_left hsgle hA

end GlobalTheory.TypeAsm
