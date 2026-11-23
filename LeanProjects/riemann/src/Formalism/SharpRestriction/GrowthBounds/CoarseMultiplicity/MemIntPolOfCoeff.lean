import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem mem_intPol_of_coeff {O : Type} [CommRing O] [IsDomain O] {σ : Type} (P : MvPolynomial σ (KK O))
    (h : ∀ μ, ∃ c : O, P.coeff μ = algebraMap O (KK O) c) : P ∈ IntPol O σ := by
  have hx : P ∈ Set.range (MvPolynomial.map (algebraMap O (KK O))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨μ, -, rfl⟩ := (MvPolynomial.mem_coeffs_iff).1 ha
    obtain ⟨c, hc⟩ := h μ
    exact ⟨c, hc.symm⟩
  obtain ⟨Q, rfl⟩ := hx
  exact ⟨Q, rfl⟩

private theorem padicValNat_le_vK_natCast {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (S : UniformizedDVR p O) (m : ℕ) : (((padicValNat p m : ℚ)) : WithTop ℚ) ≤ vK p (m : KK O) := by
  obtain ⟨r, hr⟩ := pow_padicValNat_dvd (p := p) (n := m)
  have hp0 : (p : O) ≠ 0 := S.p_ne
  have hcast : (m : KK O) = algebraMap O (KK O) ((p : O) ^ padicValNat p m) * algebraMap O (KK O) (r : O) := by
    conv_lhs => rw [hr]
    simp [map_pow, map_natCast]
  have hr0 : 0 ≤ vK p (algebraMap O (KK O) (r : O)) := (GLWeightTheory.valuation_nonneg_iff_integral S _).2 ⟨_, rfl⟩
  have hE : ramE p O = GLWeightTheory.dvrOrderNat (p : O) := by
    unfold ramE
    rw [← GLWeightTheory.dvr_order_coe_addVal hp0]
    rfl
  have hE0 := GLWeightTheory.ramification_index_ne_zero S
  rw [hcast, GLWeightTheory.valuation_mul_alt, GLWeightTheory.valuation_algebraMap_eq_alt p _ (pow_ne_zero _ hp0), GLWeightTheory.dvr_order_pow hp0]
  have hq : (((padicValNat p m * GLWeightTheory.dvrOrderNat (p : O) : ℕ) : ℚ) / (ramE p O : ℚ)) = (padicValNat p m : ℚ) := by
    rw [hE] at hE0 ⊢
    have : ((GLWeightTheory.dvrOrderNat (p : O) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hE0
    push_cast
    field_simp
  rw [hq]
  exact le_add_of_nonneg_right hr0

private theorem vK_coeff_add_half_padicVal_nonneg_of_bbSpec {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (S : UniformizedDVR p O) {σ : Type} (sp : ℕ) (u : MvPolynomial σ (KK O)) (hu : u ∈ bbSpec O p σ sp)
    (μ : σ →₀ ℕ) :
    0 ≤ vK p (u.coeff μ) +
      ((((padicValNat p (expFact μ) : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 : ℚ)) : WithTop ℚ) := by
  classical
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, c, hc, rfl⟩ := hx
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      exact hc
    · rw [GLWeightTheory.valuation_zero_alt]
      simp
  | zero =>
    rw [MvPolynomial.coeff_zero, GLWeightTheory.valuation_zero_alt]
    simp
  | add x y _ _ hx hy =>
    rw [MvPolynomial.coeff_add]
    calc (0 : WithTop ℚ) ≤ min (vK p (x.coeff μ) + _) (vK p (y.coeff μ) + _) := le_min hx hy
      _ = min (vK p (x.coeff μ)) (vK p (y.coeff μ)) + _ := (min_add_add_right _ _ _)
      _ ≤ _ := add_le_add (GLWeightTheory.valuation_add_ge_min _ _ _) le_rfl
  | smul a x _ hx =>
    rw [MvPolynomial.coeff_smul, Algebra.smul_def, GLWeightTheory.valuation_mul_alt, add_assoc]
    exact add_nonneg ((GLWeightTheory.valuation_nonneg_iff_integral S _).2 ⟨a, rfl⟩) hx

theorem bb_pair {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} (S : UniformizedDVR p O)
    (h2 : S.w ^ 2 = (p : O)) {σ : Type} (sp : ℕ) (u u' : MvPolynomial σ (KK O)) (hu : u ∈ bbSpec O p σ sp)
    (hu' : u' ∈ bbSpec O p σ sp) (μ : σ →₀ ℕ) :
    ∃ y : O, u.coeff μ * u'.coeff μ * ((expFact μ : KK O) * (sp : KK O)) = algebraMap O (KK O) y := by
  have hA := vK_coeff_add_half_padicVal_nonneg_of_bbSpec S sp u hu μ
  have hB := vK_coeff_add_half_padicVal_nonneg_of_bbSpec S sp u' hu' μ
  have h1 := padicValNat_le_vK_natCast S (expFact μ)
  have h2 := padicValNat_le_vK_natCast S sp
  rw [← GLWeightTheory.valuation_nonneg_iff_integral S, GLWeightTheory.valuation_mul_alt, GLWeightTheory.valuation_mul_alt, GLWeightTheory.valuation_mul_alt]
  set T : ℚ := (padicValNat p (expFact μ) : ℚ) / 2 + (padicValNat p sp : ℚ) / 2
  have hT : (T : WithTop ℚ) + T = ((padicValNat p (expFact μ) : ℚ) : WithTop ℚ) + ((padicValNat p sp : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    simp only [T]
    ring
  calc (0 : WithTop ℚ) ≤ (vK p (u.coeff μ) + T) + (vK p (u'.coeff μ) + T) := add_nonneg hA hB
    _ = vK p (u.coeff μ) + vK p (u'.coeff μ) + ((T : WithTop ℚ) + T) := by ac_rfl
    _ ≤ _ := by
      rw [hT]
      exact add_le_add le_rfl (add_le_add h1 h2)

theorem specConst_ne (p : ℕ) {s r : ℕ} (S : SegData s) (b : SegBlock s r) : specConst p S b ≠ 0 := by
  unfold specConst
  rw [Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  · exact one_ne_zero

private theorem gOp_smul (hEig : EigAt) {O : Type} [CommRing O] [IsDomain O] {σ : Type}
    (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O) (k : KK O) (u : MvPolynomial σ (KK O)) :
    gOp T q (k • u) = k • gOp T q u := by
  ext μ
  rw [hEig, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, hEig, smul_eq_mul, smul_eq_mul]
  ring

private theorem gOp_add (hEig : EigAt) {O : Type} [CommRing O] [IsDomain O] {σ : Type}
    (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O) (u v : MvPolynomial σ (KK O)) :
    gOp T q (u + v) = gOp T q u + gOp T q v := by
  ext μ
  rw [hEig, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hEig, hEig]
  ring

private theorem gOp_mem_span_of_mem_span (hEig : EigAt) {O : Type} [CommRing O] [IsDomain O] {σ : Type}
    (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O) (A B : Submodule O (MvPolynomial σ (KK O)))
    (hAB : ∀ x ∈ A, gOp T q x ∈ B) (u : MvPolynomial σ (KK O))
    (hu : u ∈ Submodule.span (KK O) (A : Set (MvPolynomial σ (KK O)))) :
    gOp T q u ∈ Submodule.span (KK O) (B : Set (MvPolynomial σ (KK O))) := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hAB x hx)
  | zero =>
    have h0 : gOp T q (0 : MvPolynomial σ (KK O)) = 0 := by
      ext μ
      rw [hEig, MvPolynomial.coeff_zero, mul_zero]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [gOp_add hEig]
    exact add_mem hx hy
  | smul k x _ hx =>
    rw [gOp_smul hEig]
    exact Submodule.smul_mem _ k hx

private theorem exists_algebraMap_eq_of_w_pow_padicVal_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp : p.Prime) (DS : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O)) (N E d : ℕ) (hN : N ≠ 0)
    (hNE : N = E * d) (z c : KK O) (hz : z = algebraMap O (KK O) (w ^ padicValNat p N) * c)
    (hc : ∃ y, c * c * (E : KK O) = algebraMap O (KK O) y) : ∃ o, z = algebraMap O (KK O) o := by
  obtain ⟨y, hy⟩ := hc
  obtain ⟨e, N', hndvd, hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hN'0 : N' ≠ 0 := by
    rintro rfl
    exact hndvd (dvd_zero p)
  have hv : padicValNat p N = e := by
    haveI := Fact.mk hp
    rw [hN', padicValNat.mul (pow_ne_zero _ hp.ne_zero) hN'0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hndvd, add_zero]
  rw [hv] at hz
  obtain ⟨uu, huu⟩ := GLWeightTheory.natCast_isUnit_of_coprime hp DS N' hndvd
  have hpw : (algebraMap O (KK O) w ^ e) ^ 2 = (p : KK O) ^ e := by
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hw2, map_natCast]
  have hcast : (p : KK O) ^ e * (N' : KK O) = (E : KK O) * (d : KK O) := by
    have h1 : ((p ^ e * N' : ℕ) : KK O) = ((E * d : ℕ) : KK O) := by rw [← hN', hNE]
    push_cast at h1
    exact h1
  have hz2 : z ^ 2 * algebraMap O (KK O) (uu : O) = algebraMap O (KK O) (y * d) := by
    rw [huu, map_natCast, map_mul, map_natCast, ← hy, hz, map_pow]
    linear_combination (c ^ 2 * (N' : KK O)) * hpw + c ^ 2 * hcast
  have hz3 : z ^ 2 = algebraMap O (KK O) (y * d * ↑uu⁻¹) := by
    rw [map_mul (algebraMap O (KK O)) (y * d), ← hz2, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hint : IsIntegral O z := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hz3]
    exact isIntegral_algebraMap
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨o, ho.symm⟩

theorem Nblk_ne (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    Nblk C0 CE1 CE2 X j b ≠ 0 := by
  unfold Nblk
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _) (specConst_ne _ _ _)

private theorem yCond_mono {K : Type} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ)
    {M M' : WithTop ℤ} (h : M ≤ M') : YCond K (r := r) LL j M ≤ YCond K (r := r) LL j M' := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨h1, h2⟩
  refine ⟨h1.trans ?_, h2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  intro m hm
  exact (show _ ≤ M from hx hm).trans h

private theorem yjtZ_mono' {O : Type} [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (LL : ChainLetters N)
    {q : ℕ} (J : Fin q → ℕ) {M M' : Fin q → WithTop ℤ} (h : ∀ k, M k ≤ M' k) :
    YjtZ O (r := r) LL J M ≤ YjtZ O (r := r) LL J M' := by
  unfold YjtZ Yjt
  intro x hx
  refine ⟨?_, hx.2⟩
  have hx1 : x ∈ chPol (KK O) r LL ⊓ ⨅ k, YCond (KK O) LL (J k) (M k) := hx.1
  show x ∈ chPol (KK O) r LL ⊓ ⨅ k, YCond (KK O) LL (J k) (M' k)
  refine ⟨hx1.1, ?_⟩
  have h2 : x ∈ ⨅ k, YCond (KK O) LL (J k) (M k) := hx1.2
  show x ∈ ⨅ k, YCond (KK O) LL (J k) (M' k)
  rw [Submodule.mem_iInf] at h2 ⊢
  exact fun k => yCond_mono LL (J k) (h k) (h2 k)

private theorem ssz_antitone_of_le {s r : ℕ} [NeZero r] (O : Type) [CommRing O] [IsDomain O] (p : ℕ) (S : SegData s)
    (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) {m1 m2 : ℝ} (hm : m1 ≤ m2) :
    BlockData.SSZ O (r := r) (blockData p S aTop aPlus m2 b) ≤ BlockData.SSZ O (r := r) (blockData p S aTop aPlus m1 b) := by
  unfold BlockData.SSZ
  apply Submodule.span_mono
  refine Set.iUnion_mono fun jj => Set.iUnion_mono fun jp => Set.iUnion_mono fun hL => ?_
  rintro x ⟨y, hy, g, hg, rfl⟩
  refine ⟨y, yjtZ_mono' _ _ ?_ hy, g, hg, rfl⟩
  intro k
  show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m2⌋) (segmentCapacities p S b k) ≤
    WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m1⌋) (segmentCapacities p S b k)
  generalize segmentCapacities p S b k = t
  induction t using WithTop.recTopCoe with
  | top => simp
  | coe z =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

theorem blockFormAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc H : ℝ} (hCm : 17 ≤ Cm)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (hIo : IoFockAt) (hEig : EigAt) (hHom : HomAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hDvd : DvdAt) (hSat : SatAt)
    (hG : GThetaAt) (hF : FactAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    BlockFormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC hc j b hK
  classical
  obtain ⟨hSet, hw, -, -⟩ := hS
  have hD1 : D1num X := ⟨hSet.prime, hSet.five_le, hSet.two_le, hSet.even⟩
  have hwsq : w ^ 2 = (X.p : O) := hSet.w_sq
  have hpP : X.p.Prime := hSet.prime
  have hN1 : 1 ≤ X.N1 := (hstd X hD1 hH hC).N1pos
  have hw0 : w ≠ 0 := hw.ne_zero
  let DS : UniformizedDVR X.p O :=
    { w := w, w_irr := hw,
      p_mem := by
        rw [← hwsq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_pow_iff (by norm_num)]
        exact hw.not_isUnit
      p_ne := by
        rw [← hwsq]
        exact pow_ne_zero 2 hw0
      complete := hSet.complete_O }
  haveI : CharZero (KK O) := GLWeightTheory.dvr_fraction_field_char_zero hpP DS
  obtain ⟨κ, T, q, hκ0, hκv, hT, hfac⟩ := hF X O w hw hwsq hD1 hH hC j b hK
  set v := padicValNat X.p (Nblk C0 CE1 CE2 X j b) with hv
  set sc : KK O := algebraMap O (KK O) (w ^ v) with hsc_def
  have hsc : sc * sc = (X.p : KK O) ^ v := by
    rw [hsc_def, ← map_mul, ← mul_pow, ← sq, hwsq, map_pow, map_natCast]
  have hmle : X.m0 13 ≤ X.m0 Cm - 4 * (X.c : ℝ) := by
    unfold Loc.m0 m0G4 m1G4
    have hk1 : (1 : ℝ) ≤ X.k := by
      unfold Loc.k
      have := (Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)
      linarith
    have hN1r : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hN1
    have hQ : (1 : ℝ) ≤ X.Q := by
      unfold Loc.Q
      exact one_le_pow₀ (by exact_mod_cast hpP.one_lt.le)
    have hP : (1 : ℝ) ≤ X.k * X.N1 * X.Q := by
      have h1 := mul_le_mul hk1 hN1r zero_le_one (by linarith)
      have h2 := mul_le_mul h1 hQ zero_le_one (by positivity)
      linarith
    have hc0 : (0 : ℝ) ≤ X.c := Nat.cast_nonneg _
    have h4 : 4 ≤ (Cm - 13) * (X.k * X.N1 * X.Q) := by nlinarith
    have := mul_le_mul_of_nonneg_right h4 hc0
    nlinarith
  have hmle2 : X.m0 13 ≤ X.m0 Cm := by
    have : (0 : ℝ) ≤ 4 * X.c := by positivity
    linarith
  have hint : ∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
      ∀ μ, ∃ o : O, sc * u.coeff μ = algebraMap O (KK O) o := by
    intro u hu μ
    by_cases hμ : μ ∈ u.support
    · have hHE := hHom X O hD1 hH hC j b hK (X.m0 Cm) u hu.1 μ hμ
      obtain ⟨d, hd⟩ := hDvd C0 CE1 CE2 X j b hK μ hHE
      obtain ⟨o, ho⟩ := exists_algebraMap_eq_of_w_pow_padicVal_mul hpP DS w hwsq _ _ d (Nblk_ne C0 CE1 CE2 X j b) hd (sc * u.coeff μ) (u.coeff μ) rfl (by
        obtain ⟨y, hy⟩ := bb_pair DS hwsq _ u u hu.2 hu.2 μ
        exact ⟨y, by rw [← hy]; push_cast; ring⟩)
      exact ⟨o, ho⟩
    · rw [MvPolynomial.notMem_support_iff.1 hμ, mul_zero]
      exact ⟨0, (map_zero _).symm⟩
  refine ⟨κ, fun u => sc • gOp T q u, fun u => sc • u, hκ0, hκv, ?_, ?_⟩
  · intro u hu
    have hsp := hu.1
    constructor
    · apply hSat
      · apply Submodule.smul_mem
        apply Submodule.span_mono (ssz_antitone_of_le O X.p _ _ _ b hmle)
        exact gOp_mem_span_of_mem_span hEig T q _ _ (fun x hx => hG C0 CE1 CE2 X O j b hK X.c T q hT (X.m0 Cm) x hx) u hsp
      · refine mem_intPol_of_coeff (σ := BV C0 CE1 CE2 X j) _ fun μ => ?_
        obtain ⟨o, ho⟩ := hint u hu μ
        refine ⟨gEv T q μ * o, ?_⟩
        show (sc • gOp T q u).coeff μ = _
        rw [MvPolynomial.coeff_smul, hEig, smul_eq_mul, map_mul, ← ho]
        ring
    · apply hSat
      · exact Submodule.smul_mem _ _ (Submodule.span_mono (ssz_antitone_of_le O X.p _ _ _ b hmle2) hsp)
      · refine mem_intPol_of_coeff (σ := BV C0 CE1 CE2 X j) _ fun μ => ?_
        obtain ⟨o, ho⟩ := hint u hu μ
        exact ⟨o, by
          show (sc • u).coeff μ = _
          rw [MvPolynomial.coeff_smul, smul_eq_mul, ho]⟩
  · intro u hu u' hu' a ha
    beta_reduce
    have hio := hIo C0 CE1 CE2 X (KK O) hpP.pos j b (sc • gOp T q u) (sc • u')
    have key : ∀ μ ∈ u.support, ∃ t : O,
        zSeg (KK O) X j * ((sc • gOp T q u).coeff μ * (sc • u').coeff μ * (expFact (ioExp C0 CE1 CE2 X j b μ) : KK O)) =
          algebraMap O (KK O) κ * ((specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) * (u.coeff μ * u'.coeff μ * (expFact μ : KK O))) +
          algebraMap O (KK O) (κ * w ^ X.c * t) := by
      intro μ hμ
      have hHE := hHom X O hD1 hH hC j b hK (X.m0 Cm) u hu.1 μ hμ
      obtain ⟨h, hh⟩ := hfac μ hHE
      obtain ⟨y, hy⟩ := bb_pair DS hwsq _ u u' hu.2 hu'.2 μ
      refine ⟨h * y, ?_⟩
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, hEig, smul_eq_mul, smul_eq_mul]
      simp only [map_mul, map_add, map_one, map_pow] at hh hy ⊢
      linear_combination (u.coeff μ * u'.coeff μ * zSeg (KK O) X j * (expFact (ioExp C0 CE1 CE2 X j b μ) : KK O) *
          algebraMap O (KK O) (gEv T q μ)) * hsc + (u.coeff μ * u'.coeff μ) * hh +
        (algebraMap O (KK O) κ * algebraMap O (KK O) w ^ X.c * algebraMap O (KK O) h) * hy
    choose! t ht using key
    refine ⟨∑ μ ∈ u.support, t μ, ?_⟩
    have hsub : (sc • gOp T q u).support ⊆ u.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      intro h0
      apply hμ
      rw [MvPolynomial.coeff_smul, hEig, h0, mul_zero, smul_zero]
    rw [hio, Finset.sum_subset hsub (fun μ _ hμ => by rw [MvPolynomial.notMem_support_iff.1 hμ, zero_mul, zero_mul]),
      Finset.mul_sum, Finset.sum_congr rfl ht, Finset.sum_add_distrib]
    have hf : ∑ μ ∈ u.support, algebraMap O (KK O) κ * ((specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
        (u.coeff μ * u'.coeff μ * (expFact μ : KK O))) = algebraMap O (KK O) κ * algebraMap O (KK O) a := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← ha]
      rfl
    rw [hf, ← map_sum, ← map_mul, ← map_add]
    congr 1
    simp only [Finset.mul_sum, mul_add]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring

end Formalism.MainNotions.ColumnSystems.Pf
