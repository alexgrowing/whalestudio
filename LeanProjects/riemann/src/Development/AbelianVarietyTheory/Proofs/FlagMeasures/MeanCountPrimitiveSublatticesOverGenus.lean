import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatInIsLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherrStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrimeStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanRow

theorem num_mid (a b mk M de N C f : ℝ) (j s : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hmk : 0 < mk) (hde : 1 ≤ de)
    (hN : 1 ≤ N) (hC : 16 ≤ C) (hf : 1 ≤ f) (hs : 2 ≤ s) (hM : mk * N ^ (j + s - 1) ≤ M) :
    a * b * (de ^ 2) ^ ((j : ℝ) / 2) * (de ^ 2 * N ^ 2) ^ ((9 * (s : ℝ) + 8 + 4 * Real.logb 2 (2 * f)) / 2) ≤
      M * ((de / N) ^ (j + s) * (de * N) ^ (C * s + C * Real.log f) * (b * a / mk)) := by
  have hd0 : 0 < de := by linarith
  have hN0 : 0 < N := by linarith
  have hx : 1 ≤ de * N := by nlinarith
  have hx0 : 0 < de * N := by linarith
  have e1 : (de ^ 2) ^ ((j : ℝ) / 2) = de ^ j := by
    rw [← Real.rpow_natCast de 2, ← Real.rpow_mul hd0.le, ← Real.rpow_natCast de j]
    congr 1; push_cast; ring
  have e2 : ∀ E : ℝ, (de ^ 2 * N ^ 2) ^ (E / 2) = (de * N) ^ E := fun E => by
    rw [← mul_pow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have hl : 0 ≤ Real.log f := Real.log_nonneg hf
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hlb : Real.logb 2 (2 * f) ≤ 1 + 2 * Real.log f := by
    have h2 := Real.log_two_gt_d9
    rw [Real.logb, Real.log_mul (by norm_num) (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  have hE : (9 * (s : ℝ) + 8 + 4 * Real.logb 2 (2 * f)) + 1 ≤ C * s + C * Real.log f := by nlinarith
  have h3 := Real.rpow_le_rpow_of_exponent_le hx hE
  rw [Real.rpow_add_one hx0.ne'] at h3
  rw [e1, e2]
  set X := (de * N) ^ (9 * (s : ℝ) + 8 + 4 * Real.logb 2 (2 * f))
  set Y := (de * N) ^ (C * s + C * Real.log f)
  have hX : 0 ≤ X := Real.rpow_nonneg hx0.le _
  have hY : 0 ≤ Y := Real.rpow_nonneg hx0.le _
  have h4 : X * N ≤ Y := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hX) h3
  have h5 : de ^ j ≤ de ^ (j + s) := pow_le_pow_right₀ hde (by omega)
  have e3 : N ^ (j + s) = N ^ (j + s - 1) * N := by rw [← pow_succ]; congr 1; omega
  calc a * b * de ^ j * X ≤ a * b * de ^ (j + s) * (Y / N) := by
        have : X ≤ Y / N := (le_div_iff₀ hN0).2 h4
        gcongr
    _ = (mk * N ^ (j + s - 1)) * ((de / N) ^ (j + s) * Y * (b * a / mk)) := by
        rw [div_pow, e3]; field_simp
    _ ≤ _ := by gcongr

theorem num_top (c₀ C L rd HH de N E : ℝ) (k m f : ℕ) (hc : 0 < c₀) (hC : 16 ≤ C) (hC' : 1 / c₀ ≤ C) (hL : 0 ≤ L)
    (hrd : 1 ≤ rd) (hrd' : Real.log rd ≤ L / c₀) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hH : Real.exp L ^ (C * (m : ℝ) ^ 2 * f) ≤ HH) (hde : 1 ≤ de) (hN : 1 ≤ N) (hE : 0 ≤ E) :
    (9 * rd) ^ (k * f) * de ^ k ≤ (de / N) ^ k * (de * N) ^ E * ((C * k) ^ (k * f) * (HH * N) ^ (C * k)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf' : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hN0 : 0 < N := by linarith
  have h1 : rd ^ f ≤ HH := by
    refine le_trans ?_ hH
    rw [← Real.exp_mul, ← Real.exp_log (show 0 < rd by linarith), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have a1 : L / c₀ ≤ L * C := by
      rw [div_eq_mul_one_div]; gcongr
    have a2 : L * C ≤ L * C * (m : ℝ) ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
    calc (f : ℝ) * Real.log rd ≤ f * (L * C * (m : ℝ) ^ 2) := by gcongr; linarith
      _ = _ := by ring
  have h0 : 1 ≤ rd ^ f := one_le_pow₀ hrd
  have h2 : (rd ^ f * N) ^ k ≤ (HH * N) ^ (C * k) := by
    calc (rd ^ f * N) ^ k ≤ (HH * N) ^ k := by gcongr
      _ = (HH * N) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by nlinarith)
  have h3 : 1 ≤ (de * N) ^ E := Real.one_le_rpow (by nlinarith) hE
  have h4 : (9 : ℝ) ^ (k * f) ≤ (C * k) ^ (k * f) := by gcongr; nlinarith
  calc (9 * rd) ^ (k * f) * de ^ k = (de / N) ^ k * 1 * (9 ^ (k * f) * (rd ^ f * N) ^ k) := by
        rw [div_pow, mul_pow, mul_pow, ← pow_mul, mul_comm f k]; field_simp
    _ ≤ _ := by gcongr

section General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in

theorem disc_of_equiv (h : V →ₗ⋆[K] V →ₗ[K] K) (N : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    discN h N = T ^ Module.finrank ℚ K ∧ Cnt.DiscGen h N 1 := by
  constructor
  · have e1 : discN h N = Nat.card (↥(dual h N) ⧸ N.comap (dual h N).subtype) := rfl
    rw [e1, Nat.card_congr e.toEquiv, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_singleton, Algebra.norm_natCast, RingOfIntegers.rank]
    simp
  · refine ⟨{e.symm 1}, by simp, ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e x)
    rw [Finset.coe_singleton, Submodule.mem_span_singleton]
    refine ⟨r, e.injective ?_⟩
    rw [map_smul, e.apply_symm_apply, ← hr, Algebra.smul_def, mul_one]
    rfl

end General

theorem finrank_E {R : Ranks} (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  simp only [Ranks.f, Ranks.n]
  ring

theorem fDeg_E (D : D7) : fDeg D.host.E = D.R.f := by
  let _ := D.host.cmStar
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := D.host.E)
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 := by
    rw [NumberField.nrRealPlaces_eq_zero_iff]; infer_instance
  have h4 := finrank_E D.host
  unfold fDeg
  omega

theorem vInv_E (D : D7) : 2 * vInv D.host.E = D.host.rdE := by
  unfold vInv Host.rdE
  rw [fDeg_E, finrank_E]
  push_cast
  ring

theorem one_le_rdE (D : D7) : 1 ≤ D.host.rdE := by
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

theorem main : ∀ c₀ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), c₀ ≤ Cl → UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro c₀ hc₀
  refine ⟨max 16 (1 / c₀), fun C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl => ?_⟩
  letI := D.host.cmStar
  intro hyp F0 he hz Λ hΛ reps hreps s hs2 hsk de hde HH hHH
  have hC1 : 16 ≤ C := le_trans (le_max_left _ _) hC
  have hC2 : 1 / c₀ ≤ C := le_trans (le_max_right _ _) hC
  have hK : IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨⟨hS0, -, -⟩, ⟨-, hTp, -, -, -, hTs, -⟩, -⟩ := hyp
  have hrd : Real.log D.host.rdE ≤ large₂.sc.L / Cl := hS0.2.2.2.2.2.2.2.2.2.2.1
  have hL : 0 ≤ large₂.sc.L := Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hrd' : Real.log D.host.rdE ≤ large₂.sc.L / c₀ := hrd.trans (by gcongr)
  obtain ⟨⟨hPD, hrk⟩, hrow⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hint, hcyc⟩ := hrow Λ hΛ
  have hM := (GlobalTheory.T.mass_rowLattice_orthogonal_split_prime D u F0 he hz hTp hTs Λ hΛ).2
  have hs := (D.sp.X 0).herm
  have hgen := (GlobalTheory.Mass.CyclicGenus.main _ _ _ hK hs (D.sp.X 0).nondeg _ hTp hTs).2
  generalize Lat.L0X D Λ (lf D F0) = L₀ at *
  set h := (D.sp.X 0).hT with hh
  obtain ⟨hm1, hm2, hst, -, hsum⟩ := GlobalTheory.Mass.GenusOrb.main _ _ h hK hs hPD L₀ hint.1
  have hmem : ∀ L ∈ genus h L₀, IsIntLat h L ∧ discN h L = Lat.Tu D u ^ (2 * D.R.f) ∧
      (∃ t : Finset (D.sp.X 0).V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 D.host.E) (t : Set (D.sp.X 0).V)) := fun L hL => by
    obtain ⟨a, ⟨e⟩⟩ := (hgen L₀ L hint hcyc).1 hL
    obtain ⟨b, c⟩ := disc_of_equiv h L _ e
    exact ⟨a, by rw [b, finrank_E], ((GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD L a).2.2.2.1 1).1 c⟩
  have hlhs : (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h L') : ℝ))⁻¹ *
      (Cnt.cntPrim h L' (D.R.k - s) de : ℝ≥0∞)) =
      orbSum (isom h) (genus h L₀) (fun L => (((primSp h L (D.R.k - s) (de ^ 2)).encard : ℕ∞) : ℝ≥0∞)) := by
    rw [← hsum reps _ hreps fun g M => by
      rw [(GlobalTheory.Mass.PrimMove.main _ _ h hK hs (D.sp.X 0).nondeg g M ⊥ _ _).2]]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [(GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD M (hmem M (hreps.1 M hM)).1).2.2.1]
  rw [hlhs]
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.n := D.R.ord_pos
    have h1 : D.R.f = 2 * D.R.n := rfl
    omega
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hde' : (1 : ℝ) ≤ de := by exact_mod_cast hde
  have hde2 : 1 ≤ de ^ 2 := Nat.one_le_pow _ _ hde
  have hN : 1 ≤ Cnt.NT D u := one_le_pow₀ (by exact_mod_cast hTp.one_le)
  have hU := GlobalTheory.Mass.StdMass.main _ hK
  by_cases hmid : s ≤ D.R.k - 2
  · have H := GlobalTheory.Mass.PrimMean.main GlobalTheory.T.maximalHermitianLattice_massRatio _ _ h hK hs hPD (GlobalTheory.T.exists_orthonormalLattice_of_unimodular_landherr _ hK) (D.R.k - s) s (by omega)
      (by omega) (by omega) _ _ _ (hU (D.R.k - s)).1 (hU (D.R.k - s)).2.1 _ _ _ (hU s).1 (hU s).2.1 (de ^ 2) _ hde2
      (Nat.one_le_pow _ _ hTp.pos) _ hst hmem
    refine H.trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : D.R.k - s + s = D.R.k := by omega
    have H2 := num_mid _ _ _ (mass h L₀) de _ C D.R.f (D.R.k - s) s (hU (D.R.k - s)).2.2.1.le (hU s).2.2.1.le
      (hU D.R.k).2.2.1 hde' hN hC1 hf' hs2 (by rw [e1]; exact hM)
    rw [e1] at H2
    have e2 : ((Lat.Tu D u ^ (2 * D.R.f) : ℕ) : ℝ) = Cnt.NT D u ^ 2 := by
      rw [Cnt.NT, ← pow_mul, mul_comm D.R.f]; push_cast; rfl
    rw [e2, finrank_E, Cnt.XiS, Cnt.Xi, if_pos ⟨hs2, hmid⟩]
    push_cast
    exact H2
  · have hk : 1 ≤ D.R.k := by omega
    have H2 := num_top c₀ C large₂.sc.L D.host.rdE HH de (Cnt.NT D u) (C * s + C * Real.log D.R.f) D.R.k D.R.m D.R.f
      hc₀ hC1 hC2 hL (one_le_rdE D) hrd' hk (le_trans one_le_two D.R.two_le_m) hHH hde' hN
      (by have := Real.log_nonneg hf'; positivity)
    obtain ⟨o1, o2, -⟩ := GlobalTheory.Mass.OrbMono.main (isom h) (Submodule (𝓞 D.host.E) (D.sp.X 0).V)
    refine (o1 _ _ _ (fun _ => ENNReal.ofReal ((9 * D.host.rdE) ^ (D.R.k * D.R.f) * (de : ℝ) ^ D.R.k))
      subset_rfl fun L hL => ?_).trans ?_
    · obtain ⟨p1, p0⟩ := GlobalTheory.Mass.PrimCount.main _ _ h hK hs hPD L (hmem L hL).1 _ hde2
      rcases (by omega : D.R.k - s = 1 ∨ D.R.k - s = 0) with e | e
      · rw [e]
        refine p1.trans (le_of_eq ?_)
        rw [vInv_E, fDeg_E, hrk]
        congr 2
        push_cast
        rw [← Real.rpow_natCast (de : ℝ) 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast (de : ℝ) D.R.k]
        congr 1; push_cast; ring
      · rw [e]
        refine le_trans (b := 1) (by exact_mod_cast p0) (ENNReal.one_le_ofReal.2 ?_)
        have := one_le_rdE D
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hde')
    · rw [o2, ← hm1, mul_comm, ← ENNReal.ofReal_mul hm2.le]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hm2.le)
      rw [Cnt.XiS, Cnt.Xi, if_neg (fun a => hmid a.2), if_pos (by omega)]
      exact H2

end GlobalTheory.Mass.PrimMeanRow
