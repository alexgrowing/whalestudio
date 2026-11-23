import Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

section LemGA0

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGA0_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (R := Qp) (M := T.V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lemGA0_one_root (l : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (l ^ j) := ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem lemGA0_cc_letπ (W : LocWach PD LL O v n) (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (lemGA0_one_root PD.p)
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add, map_one, hE0, one_mul] at h
  linear_combination h

theorem lemGA0_cc_π₀₁ (W : LocWach PD LL O v n) (hcard : W.DelF.card = PD.p - 1) (hp : 1 ≤ PD.p) :
    PowerSeries.constantCoeff W.π₀₁ = 0 := by
  unfold LocWach.π₀₁
  have h2 : ∀ δ, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = (0 : O) := fun δ => (W.γ₀_X δ).1
  simp only [map_add, map_sub, map_one, map_natCast, map_sum, h2, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, hcard]
  push_cast [Nat.cast_sub hp]
  ring

theorem lemGA0_cc_π₀ (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 W.π₀) = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr h0
  have e : W.π₀ = (letπ : LetA O n) * (fun _ => g) := by
    funext j
    show W.π₀₁ = PowerSeries.X * g
    exact hg
  rw [e, map_mul, map_mul, lemGA0_cc_letπ, zero_mul]

theorem lemGA0_cc_qp (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W)) = (PD.p : LL) := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add, map_natCast, map_add, lemGA0_cc_π₀ W i h0, map_natCast, zero_add]

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

theorem lemGA0_cc_pk (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.pk W 1)) = (PD.p : LL) := by
  have e : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA (Formalism.MainNotions.LiftingTheory.qp W) := by
    unfold Formalism.MainNotions.LiftingTheory.pk; rw [pow_one]
  rw [e, C.lev_φ i 1 (lemGA0_one_root PD.p) (Formalism.MainNotions.LiftingTheory.qp W), one_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, lemGA0_cc_qp W (i - 1) h0]

theorem lemGA0_conv_vanish {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hsupp : ∃ m : ℤ, ∀ k < m, d k = 0)
    (hneg : ∀ r : ℤ, r < 0 → ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) = 0) :
    ∀ r : ℤ, r < 0 → d r = 0 := by
  obtain ⟨m, hm⟩ := hsupp
  have key : ∀ t : ℕ, ∀ r : ℤ, r < m + t → r < 0 → d r = 0 := by
    intro t
    induction t with
    | zero => intro r hr _; exact hm r (by simpa using hr)
    | succ t ih =>
      intro r hr hr0
      by_cases hlt : r < m + t
      · exact ih r hlt hr0
      · have hs : ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) =
            PowerSeries.coeff 0 f • d (r - ((0 : ℕ) : ℤ)) := by
          apply finsum_eq_single _ 0
          intro j hj
          rw [ih (r - j) (by push_cast at hr; omega) (by omega), smul_zero]
        have h := hneg r hr0
        rw [hs, Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
        have h' := congrArg (fun z => (PowerSeries.constantCoeff f)⁻¹ • z) h
        simpa [inv_smul_smul₀ hf] using h'
  intro r hr
  by_cases h : r < m
  · exact hm r h
  · apply key (r - m + 1).toNat r _ hr
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem lemGA0_conv_zero {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hd : ∀ r : ℤ, r < 0 → d r = 0) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (0 - j) = PowerSeries.constantCoeff f • d 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hd _ (by have : (0 : ℕ) < j := Nat.pos_of_ne_zero hj; omega), smul_zero]

theorem lemGA0_of_tools [NeZero n] (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (hT : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    LemGA_0 W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD la hla x hx hxD hxe
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hcr : IsCrys PD T₂.ρ := by unfold Formalism.MainNotions.LiftingTheory.Sur at hsur; exact hsur.2.1
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
    have hpos : 0 < PD.p := by omega
    have : NeZero PD.p := ⟨hpos.ne'⟩
    exact (hζ.neZero').out

  have hfr : finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨hcard, -, h9K⟩ := h9 T₂ hcr hA.2.1 hA.2.2
  rw [hfr, Nat.div_one] at hcard
  have h0 : PowerSeries.constantCoeff W.π₀₁ = 0 := lemGA0_cc_π₀₁ W hcard (by omega)
  obtain ⟨-, hmod⟩ := h9K hfr
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := hmod.2 y ⟨hy, hyD.2⟩
    exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la ∈ W.N T₂ := by
    rw [pow_zero, one_mul, ← hxe]
    exact Submodule.smul_mem _ _ hx
  have hTH := hT hA hp11 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η))
    (Or.inr ⟨rfl, rfl, rfl⟩) T₂ hcr (i - 2) y la hy hyI hla.1 1 ((PD.p - 1) * 1) 0
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) hk (Or.inr ⟨rfl, rfl⟩)
  have hneg := hTH.1
  have h0v := hTH.2 0 (by omega)
  have hi2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by rw [Nat.cast_ofNat, sub_add_cancel]
  have hsub : (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la, hk⟩ : ↥(W.N T₂)) =
      (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, pow_zero, one_mul]
    exact hxe.symm
  rw [hi2, hsub] at hneg h0v
  rw [Nat.cast_zero] at h0v

  have hsm : ∀ r : ℤ, W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) r =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) •
        W.levN T₂ i 1 ⟨x, hx⟩ (r - j) :=
    fun r => W.levN_smul T₂ i 1 _ _ r
  have hccb : PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) = (PD.p : LL) ^ b i := by
    rw [map_pow, map_pow, lemGA0_cc_qp W i h0]
  have hxneg : ∀ r : ℤ, r < 0 → W.levN T₂ i 1 ⟨x, hx⟩ r = 0 :=
    lemGA0_conv_vanish (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) (W.levN T₂ i 1 ⟨x, hx⟩)
      (by rw [hccb]; exact pow_ne_zero _ hp0) (W.levN_supp T₂ i 1 _)
      (fun r hr => by rw [← hsm r]; exact hneg r hr)
  have he : ((letE i : LetA O n) • (⟨x, hx⟩ : ↥(W.N T₂))) = ⟨x, hx⟩ := Subtype.ext hxD.1
  have hL : W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) 0 =
      (PD.p : LL) ^ b i • ιV PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨x, hx⟩) := by
    rw [hsm, lemGA0_conv_zero _ _ hxneg, hccb, C.levN_eq, ← C.cmp_eq T₂ hcr i, he]
  have hcch : PowerSeries.coeff 0 (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S))) =
      (PD.p : LL) ^ (b (i - 1) + S) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_mul, map_pow, map_pow,
      lemGA0_cc_pk W C i h0]
  have hmain : (PD.p : LL) ^ b i • W.cmp T₂ ⟨x, hx⟩ =
      (PD.p : LL) ^ (b (i - 1) + S) • ((PD.p : LL) ^ lemG_sig PD.p (hpar n b S + η) •
        (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) := by
    apply lemGA0_ιV_inj (PD := PD) T₂
    rw [map_smul, map_smul, map_smul, ← hL, h0v, hcch]
  rw [← inv_smul_smul₀ (pow_ne_zero (b i) hp0) (W.cmp T₂ ⟨x, hx⟩), hmain, smul_smul, smul_smul,
    zpow_sub₀ hp0, zpow_add₀ hp0, zpow_natCast, zpow_natCast, zpow_natCast]
  congr 1
  ring

end LemGA0

end Formalism.MainNotions.RamifiedCoefficientChains.S9
