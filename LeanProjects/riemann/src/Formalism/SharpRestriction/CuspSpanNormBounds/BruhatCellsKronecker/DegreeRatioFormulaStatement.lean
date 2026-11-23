import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.HermitianLattices.FinalMass
import Formalism.GL3MeanSquares.GlobalBoundRefinementResults
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MassRatioFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryAOfPropositionA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField IsDedekindDomain Finset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sza_finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.natCard_GG
  rw [← h2, ← h1, h4]
  simp only [Ranks.f, Ranks.n]
  ring

theorem sza_fDeg_host (D : D7) : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := by
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := D.host.E)
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 := by
    rw [NumberField.nrRealPlaces_eq_zero_iff]; infer_instance
  have h4 := sza_finrank_host D
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem sza_vInv_host (D : D7) : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := by
  unfold Formalism.HermitianLatticesTheory.vInv Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  rw [sza_fDeg_host, sza_finrank_host, Nat.cast_mul, Nat.cast_ofNat]

theorem sza_v_pos (D : D7) : 0 < D.host.v := by
  unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  have h : ((NumberField.discr D.host.E : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero (K := D.host.E)
  exact half_pos (Real.rpow_pos_of_pos (abs_pos.mpr h) _)

theorem sza_card_Tau (D : D7) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
  exact (factCardPsi D.R D.host).1

theorem sza_m_eq (D : D7) : 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.rS
  omega

def szaMass (D : D7) (M : ℕ) : ℝ :=
  Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form D.host.E M) (Formalism.HermitianLatticesTheory.massTelescope_lat D.host.E M)

theorem szaMass_pos (D : D7) (M : ℕ) : 0 < szaMass D M :=
  Formalism.HermitianLatticesTheory.massTelescope_std_pos D.host.E D.sp.cm.cmUnram M

def szaData (D : D7) (u : D.what₂.Word) : Formalism.FourierDecayAlt.Sz.SizeData D.what₂.Tau where
  k := D.R.k
  r := D.R.rS
  v := D.host.v
  dF := (2 * D.host.v) ^ D.R.f
  Lv := fun M => Formalism.HermitianLatticesTheory.lValEta D.host.E M
  vol := szaMass D
  g1 := D.host.g 0
  g2 := D.host.g 1
  T := (D.mem u).A.T
  dsig := D.dsig
  Vu := fun τ => vand (uS D u τ)
  du := (D.duS u : ℝ)

theorem szaData_f (D : D7) (u : D.what₂.Word) : (szaData D u).f = D.R.f := by
  show Fintype.card D.what₂.Tau = D.R.f
  exact sza_card_Tau D
theorem szaData_n (D : D7) (u : D.what₂.Word) : (szaData D u).n = D.R.r := by
  have h := sza_m_eq D
  show D.R.k + (2 * D.R.rS + 2) - 1 = D.R.r
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem sza_u_anti (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : StrictAnti (uS D u τ) := by
  have step : ∀ (i : ℕ) (h : i + 1 < D.R.k),
      uS D u τ ⟨i + 1, h⟩ < uS D u τ ⟨i, by omega⟩ := by
    intro i h
    have h1 := (D.hcW u τ).u_gt_v ⟨i, by omega⟩
    have h2 := (D.hcW u τ).v_gt_u ⟨i, by omega⟩
    unfold Formalism.MainNotions.S.uS
    exact_mod_cast h2.trans h1
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  replace hab : a + 1 ≤ b := hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; exact step a hb
  | succ n hn ih => intro hb; exact (step n hb).trans (ih (by omega))

theorem sza_vand_pos (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 < vand (uS D u τ) := by
  unfold Formalism.MainNotions.S.vand
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b hb
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_pos.mpr (sza_u_anti D u τ hab)

theorem szaData_ok (D : D7) (u : D.what₂.Word) : (szaData D u).Ok where
  hk := by have := D.R.m_add_three_le_k; show 1 ≤ D.R.k; omega
  hv := sza_v_pos D
  hdF := by show (2 * D.host.v) ^ D.R.f = (2 * D.host.v) ^ (szaData D u).f; rw [szaData_f]
  hg1 := (D.host.g_prime 0).two_le
  hg2 := (D.host.g_prime 1).two_le
  hT := (D.mem u).A.T_prime.two_le
  hvol := szaMass_pos D _
  hVu := sza_vand_pos D u

theorem szaData_LBound (D : D7) (u : D.what₂.Word) : (szaData D u).LBound := by
  intro M hk _
  have hk' : D.R.k < M := hk
  have h3 := D.R.m_add_three_le_k
  have h := Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound D.host.E D.sp.cm.cmUnram M (by omega)
  refine ⟨h.2.1, ?_⟩
  have h2 := h.2.2
  rw [sza_fDeg_host] at h2
  rw [szaData_f]
  exact h2

theorem szaData_MassRatios (D : D7) (u : D.what₂.Word) (hM : LocalBesselAndTopKernel.FamilySchurFormalDegree D) : (szaData D u).MassRatios := by
  intro M hk _
  have hk' : D.R.k < M := hk
  have h3 := D.R.m_add_three_le_k
  have h := hM M (by omega) (Fin M → D.host.E) (Fin (M - 1) → D.host.E)
    (Formalism.HermitianLatticesTheory.massTelescope_form D.host.E M) (Formalism.HermitianLatticesTheory.massTelescope_form D.host.E (M - 1))
    (Formalism.HermitianLatticesTheory.massTelescope_lat D.host.E M) (Formalism.HermitianLatticesTheory.massTelescope_lat D.host.E (M - 1))
    (Formalism.HermitianLatticesTheory.massTelescope_symm D.host.E M) (Formalism.HermitianLatticesTheory.massTelescope_symm D.host.E (M - 1))
    (Formalism.HermitianLatticesTheory.massTelescope_ortho D.host.E M) (Formalism.HermitianLatticesTheory.massTelescope_ortho D.host.E (M - 1))
  have h' : szaMass D M / szaMass D (M - 1) = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E M := h
  rw [div_eq_iff (szaMass_pos D (M - 1)).ne'] at h'
  show szaMass D M = _
  rw [h']
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [sza_vInv_host, sza_fDeg_host, szaData_f]
  show _ = (((M - 1).factorial : ℝ) * (D.host.v / Real.pi) ^ M) ^ D.R.f *
      ((2 * D.host.v) ^ D.R.f) ^ (-(1 / 2 : ℝ)) * Formalism.HermitianLatticesTheory.lValEta D.host.E M * szaMass D (M - 1)
  have hp : (0 : ℝ) ≤ (2 * D.host.v) ^ D.R.f := by have := sza_v_pos D; positivity
  rw [Real.rpow_neg hp, ← Real.sqrt_eq_rpow]
  ring

def SzaSpl (D : D7) : Prop :=
  ∀ φ : ℝ → ℝ, ∏ᶠ p ∈ typedPl D, φ (Ideal.absNorm p.asIdeal : ℝ) =
    φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f

theorem sza_prod_Icc (g : ℕ → ℝ) (k : ℕ) : ∏ i ∈ Icc 1 k, g i = ∏ j ∈ range k, g (j + 1) := by
  induction k with
  | zero => simp [Finset.Icc_eq_empty]
  | succ n ih => rw [Finset.prod_Icc_succ_top (Nat.le_add_left 1 n), ih, Finset.prod_range_succ]

theorem sza_glCard (k : ℕ) (q : ℝ) :
    Formalism.FourierDecayAlt.Sz.glCard k q = q ^ (k * (k - 1) / 2) * ∏ i ∈ Icc 1 k, (q ^ i - 1) := by
  have e : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ j ∈ range k, (q ^ (j + 1) - 1) :=
    sza_prod_Icc (fun i => q ^ i - 1) k
  unfold Formalism.FourierDecayAlt.Sz.glCard
  rw [e, ← Finset.sum_range_id, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) k, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j < k := Finset.mem_range.mp hj
  show q ^ k - q ^ j = q ^ j * (q ^ (k - 1 - j + 1) - 1)
  rw [show k - 1 - j + 1 = k - j by omega, mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hj'.le]

theorem sza_gaG (D : D7) (u : D.what₂.Word) (hs : SzaSpl D) : gaG D = (szaData D u).idxCol := by
  have h := hs (fun q => ∏ i ∈ Icc 1 D.R.k, (q ^ i - 1))
  unfold gaG
  rw [h]
  unfold Formalism.FourierDecayAlt.Sz.SizeData.idxCol Formalism.FourierDecayAlt.Sz.colIdx
  rw [szaData_f, sza_glCard, sza_glCard]
  have h0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have h1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  show _ = ((((D.host.g 0 : ℕ) : ℝ) ^ (D.R.k * (D.R.k - 1) / 2) * _) / ((D.host.g 0 : ℕ) : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) ^ D.R.f *
    ((((D.host.g 1 : ℕ) : ℝ) ^ (D.R.k * (D.R.k - 1) / 2) * _) / ((D.host.g 1 : ℕ) : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) ^ D.R.f
  rw [mul_div_cancel_left₀ _ (pow_ne_zero _ h0), mul_div_cancel_left₀ _ (pow_ne_zero _ h1)]
  rfl

theorem sza_r_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  have h := sza_m_eq D
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem sza_idxRows (D : D7) (u : D.what₂.Word) (hs : SzaSpl D) : LocalBesselAndTopKernel.idxRows D = (szaData D u).idxRow := by
  have h := hs (fun q => LocalBesselAndTopKernel.cardGL q D.R.r / (q ^ LocalBesselAndTopKernel.dimNS D * q ^ (D.R.k * (D.R.k - 1) / 2)))
  unfold LocalBesselAndTopKernel.idxRows
  rw [h]
  unfold Formalism.FourierDecayAlt.Sz.SizeData.idxRow Formalism.FourierDecayAlt.Sz.rowIdx
  rw [szaData_f]
  show _ = (Formalism.FourierDecayAlt.Sz.glCard (D.R.k + 2 * D.R.rS + 1) _ / _) ^ D.R.f * (Formalism.FourierDecayAlt.Sz.glCard (D.R.k + 2 * D.R.rS + 1) _ / _) ^ D.R.f
  rw [← sza_r_eq]
  rfl

theorem szaData_ColumnCount (D : D7) (u : D.what₂.Word) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hs : SzaSpl D) :
    (szaData D u).ColumnCount := by
  have h := (hR (Fin D.R.k → D.host.E) (Formalism.HermitianLatticesTheory.massTelescope_form D.host.E D.R.k)
    (Formalism.HermitianLatticesTheory.massTelescope_lat D.host.E D.R.k) (Formalism.HermitianLatticesTheory.massTelescope_symm D.host.E D.R.k)).1
    (Formalism.HermitianLatticesTheory.massTelescope_ortho D.host.E D.R.k) u
  unfold Formalism.FourierDecayAlt.Sz.SizeData.ColumnCount
  rw [← sza_gaG D u hs, szaData_f]
  show (D.duS u : ℝ) = szaMass D D.R.k * gaG D * (∏ w, vand (uS D u w) / ((Formalism.FourierDecayAlt.Sz.sfac D.R.k : ℕ) : ℝ)) *
    ((((D.mem u).A.T : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f
  rw [h]
  unfold Formalism.FourierDecayAlt.Sz.sfac szaMass Tr
  push_cast
  rfl

theorem szaData_Dstar (D : D7) (u : D.what₂.Word) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hs : SzaSpl D) :
    (szaData D u).Dstar = D.what₂.Dstar := by
  have h := (hR (Fin D.R.r → D.host.E) (Formalism.HermitianLatticesTheory.massTelescope_form D.host.E D.R.r)
    (Formalism.HermitianLatticesTheory.massTelescope_lat D.host.E D.R.r) (Formalism.HermitianLatticesTheory.massTelescope_symm D.host.E D.R.r)).2
    (Formalism.HermitianLatticesTheory.massTelescope_ortho D.host.E D.R.r)
  unfold Formalism.FourierDecayAlt.Sz.SizeData.Dstar
  rw [← sza_idxRows D u hs, szaData_n, h]
  rfl

theorem sza_cast_exp (D : D7) :
    (((D.R.m - 1) * D.R.k + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) =
      ((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 ∧
    ((D.R.k * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) =
      (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 := by
  have hm := sza_m_eq D
  have hm1 : 1 ≤ D.R.m := by omega
  have hdiv : 2 ∣ D.R.m * (D.R.m - 1) := by
    refine ⟨(D.R.rS + 1) * (2 * D.R.rS + 1), ?_⟩
    rw [← hm, show 2 * D.R.rS + 2 - 1 = 2 * D.R.rS + 1 by omega]
    ring
  have hc : ((D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) = (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 := by
    rw [Nat.cast_div hdiv (by norm_num), Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one, Nat.cast_ofNat]
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one, hc]
  · rw [Nat.cast_add, Nat.cast_mul, hc]

theorem sza_ka_pos (D : D7) : 0 < D.host.ka := by
  unfold Formalism.BasicNotions.Host.ka
  exact div_pos Real.pi_pos (sza_v_pos D)

theorem sza_gg_pos (D : D7) : 0 < gg D := by
  unfold Formalism.MainNotions.S.gg
  have h0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
  have h1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
  exact mul_pos h0 h1

theorem sza_tcritPow (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Tcrit D u τ ^ D.R.k = (szaData D u).TcritPow τ := by
  have hk0 : (D.R.k : ℝ) ≠ 0 := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.k ≠ 0)
  have hka := sza_ka_pos D
  have hv := sza_v_pos D
  have hrv : D.host.rdE = 2 * D.host.v := by unfold Formalism.BasicNotions.Host.v; ring
  have hrd : 0 < D.host.rdE := by rw [hrv]; linarith
  have hgg := sza_gg_pos D
  have hvand := sza_vand_pos D u τ
  have hds : 0 ≤ D.dsig τ := by
    first
    | exact (D.dsig_pos τ).le
    | exact D.dsig_nonneg τ
    | exact (D.dsig_pos' τ).le
    | exact (D.hdsig τ).le
    | exact (D.dsig_spec τ).le
  have hVV : 0 ≤ VV D τ := by
    unfold Formalism.MainNotions.S.VV
    exact mul_nonneg hds (Finset.prod_nonneg fun i _ => by positivity)
  obtain ⟨c1, c2⟩ := sza_cast_exp D
  have hX : 0 ≤ D.host.ka ^ (-(((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2)) *
      D.host.rdE ^ (-(((D.R.m : ℝ) - 1) / 2)) *
      gg D ^ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) *
      VV D τ / vand (uS D u τ) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hka.le _)
      (Real.rpow_nonneg hrd.le _)) (Real.rpow_nonneg hgg.le _)) hVV) hvand.le
  unfold Formalism.MainNotions.S.Tcrit
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX, one_div, inv_mul_cancel₀ hk0, Real.rpow_one]
  simp only [Formalism.FourierDecayAlt.Sz.SizeData.TcritPow, Formalism.FourierDecayAlt.Sz.TcritPow, Formalism.FourierDecayAlt.Sz.SizeData.ka,
    Formalism.FourierDecayAlt.Sz.SizeData.rd, Formalism.FourierDecayAlt.Sz.SizeData.g, Formalism.FourierDecayAlt.Sz.SizeData.VV,
    Formalism.FourierDecayAlt.Sz.SizeData.m, Formalism.FourierDecayAlt.Sz.SizeData.n, szaData]
  rw [sza_m_eq D, ← c1, ← c2, Real.rpow_neg hka.le, Real.rpow_natCast, Real.rpow_natCast, hrv]
  unfold Formalism.BasicNotions.Host.ka Formalism.MainNotions.S.gg Formalism.MainNotions.S.VV Formalism.FourierDecayAlt.Sz.sfac Formalism.BasicNotions.Ranks.r
  push_cast
  try ring

theorem degree_ratio_product_formula (D : D7) (hM : LocalBesselAndTopKernel.FamilySchurFormalDegree D) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hs : SzaSpl D)
    (hg : ∀ i, 4 ≤ D.host.g i) : LocalBesselAndTopKernel.projection_sandwich_lattice D := by
  intro u
  have hk5 := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hA := Formalism.FourierDecayAlt.P.massRatioFormula D.what₂.Tau (szaData D u) (szaData_ok D u) (szaData_MassRatios D u hM)
    (szaData_ColumnCount D u hR hs)
  have hE := Formalism.FourierDecayAlt.P.exponent_sizes D.what₂.Tau (szaData D u) (szaData_ok D u) (szaData_LBound D u)
    (show 2 ≤ D.R.k by omega) (hg 0) (hg 1)
  rw [szaData_Dstar D u hR hs] at hA
  have hP : ∏ w, ((szaData D u).TcritPow w / (((szaData D u).T : ℕ) : ℝ) ^ (szaData D u).k) =
      ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [div_pow, sza_tcritPow]
    rfl
  rw [hP] at hA
  have hA' : D.what₂.Dstar / (D.duS u : ℝ) = (szaData D u).Ea * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := hA
  rw [hA']
  have h2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
    norm_num
  rw [h2]
  have hP0 : 0 ≤ ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k :=
    Finset.prod_nonneg fun τ _ => D.R.k_even.pow_nonneg _
  obtain ⟨hpos, hlog⟩ := hE
  rw [szaData_f] at hlog
  have hlog' : |Real.log (szaData D u).Ea| ≤ (D.R.f : ℝ) * (8 / 2 ^ D.R.k) := hlog
  rw [abs_le] at hlog'
  constructor
  · refine mul_le_mul_of_nonneg_right ?_ hP0
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hlog'.1
  · refine mul_le_mul_of_nonneg_right ?_ hP0
    conv_lhs => rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hlog'.2

theorem sza_spl_of_data {D : D7} {C0 : ℝ} (h : StandingNumericalData D C0) : SzaSpl D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h0, h1, _⟩ := h
  exact finprod_typedPl D h0 h1

theorem sza_b_ge_one {D : D7} (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.b := by
  unfold Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.L
  have hx : 0 < large₂.sc.x := lt_trans zero_lt_one large₂.sc.one_lt_alt
  exact Real.one_le_exp (Real.rpow_pos_of_pos hx _).le

theorem sza_g_ge {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) :
    ∀ i, 4 ≤ D.host.g i := by
  have hb : (1 : ℝ) ≤ large₂.sc.b := sza_b_ge_one large₂
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hkb : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have h8 : (4 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    calc (4 : ℝ) ≤ 5 ^ 8 := by norm_num
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by gcongr
  simp only [StandingHypotheses] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -, h14, -⟩ := h
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · exact_mod_cast h8.trans h12
  · exact_mod_cast h8.trans h14

theorem degree_ratio_formula_statement (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) :
    LocalBesselAndTopKernel.FamilyExpansionSecond D large₂ C0 C' Cl Cg cb Cu cT CT := by
  intro hM _ hR hH
  obtain ⟨hD, hH0, _⟩ := hH
  exact degree_ratio_product_formula D hM hR (sza_spl_of_data hD) (sza_g_ge hH0)

theorem level_formula_family {eps : ℝ} (Fm : FamP eps) (C0 Cg cb Cu cT CT : ℝ) :
    LocalBesselAndTopKernel.FamilyUnfoldingCount Fm C0 Cg cb Cu cT CT := by
  intro hM1 hM2 hR
  obtain ⟨x0, h0⟩ := hR
  refine Exists.intro x0 ?_
  intro x hx i hH
  exact degree_ratio_formula_statement (Fm.D x i) (Fm.L x i) C0 _ _ Cg cb Cu cT CT (hM1 x i) (hM2 x i)
    (h0 x hx i hH) hH

theorem sza_tcrit_pos (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 < Tcrit D u τ := by
  have hka := sza_ka_pos D
  have hrd : 0 < D.host.rdE := by
    have hv := sza_v_pos D
    unfold Formalism.BasicNotions.Host.v at hv
    linarith
  have hgg := sza_gg_pos D
  have hvand := sza_vand_pos D u τ
  have hds : 0 < D.dsig τ := by
    first
    | exact D.dsig_pos τ
    | exact D.hdsig τ
    | exact D.dsig_pos' τ
    | exact D.dsig_spec τ
  have hVV : 0 < VV D τ := by
    unfold Formalism.MainNotions.S.VV
    exact mul_pos hds (Finset.prod_pos fun i _ => by positivity)
  unfold Formalism.MainNotions.S.Tcrit
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hka _) (Real.rpow_pos_of_pos hrd _))
    (Real.rpow_pos_of_pos hgg _)) hVV) hvand

theorem sza_Tr_pos (D : D7) (u : D.what₂.Word) : 0 < Tr D u := by
  have h : 2 ≤ (D.mem u).A.T := (szaData_ok D u).hT
  unfold Formalism.MainNotions.S.Tr
  exact_mod_cast (by omega : 0 < (D.mem u).A.T)

theorem level_ratio_bound (D : D7) (C0 C1 : ℝ) (hD : StandingNumericalData D C0) (hC0 : 1 ≤ C0) (ha : LocalBesselAndTopKernel.projection_sandwich_lattice D) (hb : LocalBesselAndTopKernel.MassRatio₂ D C1) :
    LocalBesselAndTopKernel.kernel_index_full_lattice D (C1 * (C0 * Real.exp 1)) := by
  intro u u'
  have hk5 : 5 ≤ D.R.k := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    omega
  have hf1 : 1 ≤ D.R.f := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    unfold Ranks.f; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, hwin, _⟩ := hD
  set x : ℝ := (D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k) with hx
  set A : D.what₂.Word → ℝ := fun w => ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k with hA
  set P : D.what₂.Word → ℝ := fun w => ∏ τ, Tcrit D w τ ^ D.R.k with hP
  have hApos : ∀ w, 0 < A w := fun w =>
    Finset.prod_pos fun τ _ => pow_pos (div_pos (sza_tcrit_pos D w τ) (sza_Tr_pos D w)) _
  have hPpos : ∀ w, 0 < P w := fun w => Finset.prod_pos fun τ _ => pow_pos (sza_tcrit_pos D w τ) _
  have hAP : ∀ w, Tr D w ^ (D.R.k * D.R.f) * A w = P w := by
    intro w
    simp only [hA, hP, div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, sza_card_Tau, ← pow_mul]
    field_simp [(pow_pos (sza_Tr_pos D w) (D.R.k * D.R.f)).ne']
  have hR : ∀ w, 0 < D.what₂.Dstar / (D.duS w : ℝ) := fun w =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) (hApos w)) (ha w).1
  have hd0 : ∀ w, (0 : ℝ) ≤ (D.duS w : ℝ) := fun w => Nat.cast_nonneg _
  have hdpos : ∀ w, (0 : ℝ) < (D.duS w : ℝ) := by
    intro w
    rcases (hd0 w).lt_or_eq with h | h
    · exact h
    · have := hR w; rw [← h, div_zero] at this; exact absurd this (lt_irrefl _)
  have hDs : 0 < D.what₂.Dstar := by
    have := hR u
    rwa [div_pos_iff_of_pos_right (hdpos u)] at this

  have hdd : (D.duS u : ℝ) ≤ C0 ^ 2 * (D.duS u' : ℝ) := by
    have h1 := (hwin u).2
    have h2 := (hwin u').1
    rw [D.GamP_eq u] at h1
    rw [D.GamP_eq u'] at h2
    rw [div_le_iff₀ (by linarith)] at h2
    calc (D.duS u : ℝ) ≤ (D.mem D.u₀).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0 := h1
      _ ≤ ((D.duS u' : ℝ) * C0) * C0 := mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = C0 ^ 2 * (D.duS u' : ℝ) := by ring
  have hRR : D.what₂.Dstar / (D.duS u' : ℝ) ≤ C0 ^ 2 * (D.what₂.Dstar / (D.duS u : ℝ)) := by
    rw [div_le_iff₀ (hdpos u')]
    have : C0 ^ 2 * (D.what₂.Dstar / (D.duS u : ℝ)) * (D.duS u' : ℝ) =
        D.what₂.Dstar * ((C0 ^ 2 * (D.duS u' : ℝ)) / (D.duS u : ℝ)) := by ring
    rw [this]
    have h1 : 1 ≤ (C0 ^ 2 * (D.duS u' : ℝ)) / (D.duS u : ℝ) := by
      rw [le_div_iff₀ (hdpos u)]; linarith
    nlinarith
  have hAA : A u' ≤ Real.exp (2 * x) * C0 ^ 2 * A u := by
    have h1 : A u' ≤ Real.exp x * (D.what₂.Dstar / (D.duS u' : ℝ)) := by
      have := (ha u').1
      have h2 : Real.exp x * (Real.exp (-x) * A u') = A u' := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [← h2]
      exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    have h3 := (ha u).2
    calc A u' ≤ Real.exp x * (D.what₂.Dstar / (D.duS u' : ℝ)) := h1
      _ ≤ Real.exp x * (C0 ^ 2 * (D.what₂.Dstar / (D.duS u : ℝ))) :=
          mul_le_mul_of_nonneg_left hRR (Real.exp_pos _).le
      _ ≤ Real.exp x * (C0 ^ 2 * (Real.exp x * A u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (Real.exp_pos _).le
      _ = Real.exp (2 * x) * C0 ^ 2 * A u := by
          rw [two_mul, Real.exp_add]; ring
  have hC1 : 0 < C1 := by
    have hne : Nonempty D.what₂.Tau := by
      rw [← Fintype.card_pos_iff, sza_card_Tau]; omega
    obtain ⟨τ⟩ := hne
    have := hb u u τ
    rw [div_self (sza_tcrit_pos D u τ).ne'] at this
    linarith
  have hPP : P u ≤ C1 ^ (D.R.k * D.R.f) * P u' := by
    have h1 : ∀ τ, Tcrit D u τ ^ D.R.k ≤ C1 ^ D.R.k * Tcrit D u' τ ^ D.R.k := by
      intro τ
      have := hb u u' τ
      rw [div_le_iff₀ (sza_tcrit_pos D u' τ)] at this
      rw [← mul_pow]
      exact pow_le_pow_left₀ (sza_tcrit_pos D u τ).le this _
    calc P u ≤ ∏ τ, (C1 ^ D.R.k * Tcrit D u' τ ^ D.R.k) :=
          Finset.prod_le_prod (fun τ _ => (pow_pos (sza_tcrit_pos D u τ) _).le) (fun τ _ => h1 τ)
      _ = C1 ^ (D.R.k * D.R.f) * P u' := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, sza_card_Tau, ← pow_mul]

  have hkf2 : 2 ≤ D.R.k * D.R.f := by nlinarith
  have hx2 : 2 * x ≤ ((D.R.k * D.R.f : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
      linarith
    have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
    have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    push_cast
    rw [hx]
    nlinarith
  have hsm : Real.exp (2 * x) * C0 ^ 2 ≤ (C0 * Real.exp 1) ^ (D.R.k * D.R.f) := by
    rw [mul_pow, mul_comm]
    apply mul_le_mul (pow_le_pow_right₀ hC0 hkf2) _ (Real.exp_pos _).le (by positivity)
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.exp_le_exp.2 hx2
  have hmain : Tr D u ^ (D.R.k * D.R.f) ≤ (C1 * (C0 * Real.exp 1) * Tr D u') ^ (D.R.k * D.R.f) := by
    have h1 : Tr D u ^ (D.R.k * D.R.f) * A u ≤ (C1 * (C0 * Real.exp 1) * Tr D u') ^ (D.R.k * D.R.f) * A u := by
      calc Tr D u ^ (D.R.k * D.R.f) * A u = P u := hAP u
        _ ≤ C1 ^ (D.R.k * D.R.f) * P u' := hPP
        _ = C1 ^ (D.R.k * D.R.f) * (Tr D u' ^ (D.R.k * D.R.f) * A u') := by rw [hAP u']
        _ ≤ C1 ^ (D.R.k * D.R.f) * (Tr D u' ^ (D.R.k * D.R.f) * (Real.exp (2 * x) * C0 ^ 2 * A u)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hAA (pow_pos (sza_Tr_pos D u') _).le
        _ = C1 ^ (D.R.k * D.R.f) * Tr D u' ^ (D.R.k * D.R.f) * A u * (Real.exp (2 * x) * C0 ^ 2) := by ring
        _ ≤ C1 ^ (D.R.k * D.R.f) * Tr D u' ^ (D.R.k * D.R.f) * A u * (C0 * Real.exp 1) ^ (D.R.k * D.R.f) := by
            apply mul_le_mul_of_nonneg_left hsm
            have := hApos u
            have := sza_Tr_pos D u'
            positivity
        _ = (C1 * (C0 * Real.exp 1) * Tr D u') ^ (D.R.k * D.R.f) * A u := by
            simp only [mul_pow]; ring
    exact le_of_mul_le_mul_right h1 (hApos u)
  have hle : Tr D u ≤ C1 * (C0 * Real.exp 1) * Tr D u' := by
    have hpos : 0 ≤ C1 * (C0 * Real.exp 1) * Tr D u' := by
      have := sza_Tr_pos D u'
      have : 0 < C0 := by linarith
      positivity
    exact (pow_le_pow_iff_left₀ (sza_Tr_pos D u).le hpos (by omega)).1 hmain
  rw [div_le_iff₀ (sza_Tr_pos D u')]
  exact hle

theorem level_ratio_bound_mono {D : D7} {C2 C2' : ℝ} (h : LocalBesselAndTopKernel.kernel_index_full_lattice D C2) (hC : C2 ≤ C2') : LocalBesselAndTopKernel.kernel_index_full_lattice D C2' := by
  intro u u'
  exact (h u u').trans hC

theorem family_level_ratio_bound {eps : ℝ} (Fm : FamP eps) (C0 Cg cb Cu cT CT C1 C2 : ℝ)
    (hC2 : C1 * (C0 * Real.exp 1) ≤ C2) (ha : LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT)
    (hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT C1) : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT C2 := by
  obtain ⟨x1, h1⟩ := ha
  obtain ⟨x2, h2⟩ := hb
  refine Exists.intro (max x1 x2) ?_
  intro x hx i hH
  have hx1 : x ≥ x1 := le_trans (le_max_left _ _) hx
  have hx2 : x ≥ x2 := le_trans (le_max_right _ _) hx
  have ha' := h1 x hx1 i hH
  have hb' := h2 x hx2 i hH
  obtain ⟨hD, -, hC0⟩ := hH
  exact level_ratio_bound_mono (level_ratio_bound (Fm.D x i) C0 C1 hD hC0 ha' hb') hC2

theorem sza_zeta (M : ℕ) (hM : 2 ≤ M) : (riemannZeta (M : ℂ)).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M := by
  have h1 : 1 < ((M : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < M)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  have e : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (M : ℂ) = (((1 : ℝ) / ((n : ℝ) + 1) ^ M : ℝ) : ℂ) := by
    intro n
    rw [Complex.cpow_natCast]
    push_cast
    try ring
  simp_rw [e]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

theorem sza_stMassL (D : D7) : UnitaryVolumeMass.stMassL D := by
  intro M hM
  have h := (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound D.host.E D.sp.cm.cmUnram M hM).2.2
  rw [sza_fDeg_host] at h
  rw [sza_zeta M hM]
  exact h

theorem mass_two_bound_single_holds (D : D7) : LocalBesselAndTopKernel.GL5LogLValueBoundByZeta D := by
  intro i hi
  exact sza_stMassL D i (by omega)

theorem mass_two_bound_family_holds {eps : ℝ} (Fm : FamP eps) : LocalBesselAndTopKernel.BesselFormLine Fm := by
  intro x i
  exact mass_two_bound_single_holds _

end Formalism.MainNotions.BridgeLemma

end
