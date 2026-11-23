import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Coeff

variable {R : Type} [CommRing R]

theorem framepf_coeff_pow_lt (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m j : ℕ)
    (hj : j < m) : PowerSeries.coeff j (f ^ m) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem framepf_coeff_pow_self (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m : ℕ) :
    PowerSeries.coeff m (f ^ m) = PowerSeries.coeff 1 f ^ m := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end Coeff

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

theorem framepf_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem framepf_levB_gam (hc : IsCrys PD T.ρ) (g : W.Gam)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - 1)) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Ct.levB T i 1 ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Ct.levB T i 1 x k :=
  Ct.levB_Γ T hc g i 1 1 0 1 (by simpa using IsPrimitiveRoot.one) (by simpa using hv) (by simp) x hx k

theorem framepf_levB_zero (hc : IsCrys PD T.ρ) (i : ZMod n)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1))
    (hχ : ∀ r : ℤ, 1 ≤ r → (algebraMap O LL (W.χΓ W.gam : O)) ^ r ≠ 1)
    (a : LetA O n) (R : ℕ) (ha : ∀ j < R, PowerSeries.coeff j (W.lev i 1 a) = 0)
    (x w : ↥(W.N T)) (hxw : W.γD T W.gam (x : W.DD T) - x = a • (w : W.DD T))
    (hw : ∀ r : ℤ, r < 0 → W.levN T i 1 w r = 0) (r : ℤ) (h1 : 1 ≤ r) (hR : r < R) :
    Ct.levB T i 1 x r = 0 := by
  have hx : W.γD T W.gam (x : W.DD T) ∈ W.N T := W.N_Γ T W.gam x x.2
  have haw : a • (w : W.DD T) ∈ W.N T := (W.N T).smul_mem a w.2
  have hsub : (⟨_, hx⟩ : ↥(W.N T)) - x = ⟨_, haw⟩ := Subtype.ext (by simp [hxw])
  have hlev := congrArg (fun y => Ct.levB T i 1 y r) hsub
  simp only [map_sub, Pi.sub_apply] at hlev
  rw [framepf_levB_gam Ct T hc W.gam hv i x hx r] at hlev
  have hzero : Ct.levB T i 1 ⟨_, haw⟩ r = 0 := by
    refine framepf_ιV_inj (PD := PD) T ?_
    rw [map_zero, ← Ct.levN_eq]
    have : (⟨_, haw⟩ : ↥(W.N T)) = a • w := rfl
    rw [this, W.levN_smul]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < R
    · rw [ha j hj, zero_smul]
    · simp only [hw (r - (j : ℤ)) (by omega), smul_zero]
  rw [hzero] at hlev
  have h2 : ((algebraMap O LL (W.χΓ W.gam : O)) ^ r - 1) • Ct.levB T i 1 x r = 0 := by
    rw [sub_smul, one_smul]; exact hlev
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hχ r h1))

theorem framepf_levB_phi (hc : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hQ : ∀ j < m, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (i - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (i - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    Ct.levB T i ζ ⟨_, hm⟩ k =
      serC (W.lev i ζ (W.Q ^ m)) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (i - 1) 1 x 0)) k := by
  rw [Ct.levB_φ T hc i ζ hζ x m hm k, hζ1]
  unfold serC
  split_ifs with hk0
  · rw [finsum_eq_single _ k.toNat]
    · have : k - (k.toNat : ℤ) = 0 := by omega
      rw [this, zpow_zero, one_smul]
    · intro j hj
      by_cases hjm : j < m
      · rw [hQ j hjm, zero_smul]
      · by_cases hjk : (j : ℤ) < k
        · rw [hmid (k - (j : ℤ)) (by omega) (by omega), map_zero, smul_zero, smul_zero]
        · have : (j : ℤ) ≠ k := fun h => hj (by omega)
          rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]

theorem framepf_valAt (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hex : ∃ k : ℕ, W.Q ^ k • W.φD T (x : W.DD T) ∈ W.N T) :
    valAt W T c ζ (x : W.DD T) = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := by
  classical
  unfold valAt
  rw [dif_pos hex]
  have hm := Nat.find_spec hex
  have hC := framepf_levB_phi Ct T hc c ζ hζ hζ1 x (Nat.find hex) 1 hm
    (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg
    (fun r h1 h2 => by omega) (Nat.find hex : ℤ) (by omega)
  rw [Ct.levN_eq, hC]
  unfold serC
  rw [if_pos (by omega), map_smul, map_pow, Int.toNat_natCast, framepf_coeff_pow_self _ hQ0, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hQ1), one_smul]

theorem framepf_levN_phi (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (c - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    W.levN T c ζ ⟨_, hm⟩ k = serC (W.lev c ζ (W.Q ^ m)) (valAt W T c ζ (x : W.DD T)) k := by
  rw [framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x hneg ⟨m, hm⟩, Ct.levN_eq,
    framepf_levB_phi Ct T hc c ζ hζ hζ1 x m R hm
      (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg hmid k hk]
  unfold serC
  split_ifs
  · rw [map_smul]
  · rw [map_zero]

end Local

end Formalism.MainNotions.N.Ln34

end
