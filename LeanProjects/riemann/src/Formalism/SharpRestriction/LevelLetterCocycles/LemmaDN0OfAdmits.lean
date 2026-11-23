import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.XDvdLevCQ
import Formalism.SharpRestriction.LevelLetterCocycles.ConvEqSum
import Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfMemSum
import Formalism.SharpRestriction.LevelLetterCocycles.CardBasisEq
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 TensorProduct

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem φA_letE (i : ZMod n) : W.φA (letE (i - 1) : LetA O n) = letE i := by
  funext j
  show W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  simp only [letE, Pi.single_apply, sub_left_inj]
  split_ifs <;> simp

theorem lev_letE (i : ZMod n) (ζ : LL) : W.lev i ζ (letE i : LetA O n) = 1 := by
  have h0 : W.lev i ζ (1 - letE i) = 0 := W.lev_letter i ζ _ (by simp [letE])
  rw [map_sub, map_one] at h0
  exact (sub_eq_zero.mp h0).symm

theorem levN_letE (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (h : (letE i : LetA O n) • (x : W.DD T) ∈ W.N T) :
    W.levN T i ζ ⟨_, h⟩ = W.levN T i ζ x := by
  have e : (⟨(letE i : LetA O n) • (x : W.DD T), h⟩ : ↥(W.N T)) = (letE i : LetA O n) • x := rfl
  rw [e]
  funext k
  rw [W.levN_smul, lev_letE W i ζ]
  rw [finsum_eq_single _ 0 (fun j hj => by simp [PowerSeries.coeff_one, hj])]
  simp

end SlopeTestRemainingChoices

section Jumps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem fd_DdRE (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    (i : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) :
    FiniteDimensional LL ↥(DdRE PD T₂.ρ τ) := by
  have := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS i
  rw [← Formalism.MainNotions.N.Pv.LocalLengthBound.rk_DcrisL_map W hS.1.1 hQ T₂ hS.2.2.2.2.2.1.2.1 τ]
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ
  rw [hτ]
  infer_instance

theorem jumps_le (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    (hm : m = 0) (i : ZMod n) (hi : (i.val + d) % 2 = 0) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) : JumpsInV PD T₂.ρ τ (Set.Iic (-((b i : ℕ) : ℤ))) := by
  have := fd_DdRE W hQ hS i τ hτ
  intro a ha
  have hw := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a ha
  simp only [JumpWinS, hi, if_true, Set.mem_union, Set.mem_Icc] at hw
  rcases hw with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · exfalso
    have hsum := hS.2.2.2.2.2.2.2.1 i τ hτ
    rw [hm] at hsum
    have hnn : ∀ a' ∈ Finset.Icc (-(η : ℤ)) η, 0 ≤ multV PD T₂.ρ τ a' := fun a' _ =>
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_nonneg (O := O) T₂ τ a'
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
      (le_antisymm (by exact_mod_cast hsum) (Finset.sum_nonneg hnn)) a (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    unfold multV at h0
    have hlt : FildR PD T₂.ρ τ (a + 1) < FildR PD T₂.ρ τ a :=
      lt_of_le_of_ne (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti PD T₂.ρ τ (by omega)) ha
    have : FiniteDimensional LL ↥(FildR PD T₂.ρ τ a) :=
      Submodule.finiteDimensional_of_le (inf_le_left : FildR PD T₂.ρ τ a ≤ DdRE PD T₂.ρ τ)
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

end Jumps

section Root

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem ιDi_eq (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i = DdRE PD T.ρ τ := by
  rw [← Formalism.MainNotions.N.Pv.LocalLengthBound.rk_DcrisL_map W hK hQ T hT τ]
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ
  rw [hτ]
  rfl

theorem levN_vanish (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (ζ : LL)
    (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) (hPt : Pt i ζ τ)
    [FiniteDimensional LL ↥(DdRE PD T.ρ τ)] (b : ℕ)
    (hj : JumpsInV PD T.ρ τ (Set.Iic (-(b : ℤ)))) (x : ↥(W.N T))
    (hx : (letE i : LetA O n) • (x : W.DD T) = x) : ∀ k : ℤ, k < b → W.levN T i ζ x k = 0 := by
  intro k hk
  have h1 := (hP4.2 i ζ τ hPt).2.1 x k
  rw [ιDi_eq W hK hQ T hT i τ hτ] at h1
  obtain ⟨hD, hF⟩ := Submodule.mem_inf.mp h1
  have h2 := Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge.mem_of_mem_filC PD T.ρ τ (FildR PD T.ρ τ (-k)) inf_le_left hD hF
  rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge.fildR_eq_bot PD T.ρ τ b hj (-k) (by omega)] at h2
  have h3 : ((letE i : LetA O n) • x : ↥(W.N T)) = x := Subtype.ext hx
  rw [h3] at h2
  exact (Submodule.mem_bot LL).mp h2

end Root

section Lq

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_q_X_mul (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (hp2 : 2 ≤ PD.p)
    (hp0 : ((PD.p : ℕ) : LL) ≠ 0) :
    ∃ u : PowerSeries LL, W.lev i ζ W.q = PowerSeries.X * u ∧ PowerSeries.constantCoeff u ≠ 0 := by
  have hpi : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    unfold letπ LocWach.q
    funext j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hL := congrArg (W.lev i ζ) hpi
  rw [map_mul, map_sub, map_pow, map_add, map_one] at hL
  obtain ⟨E, hE0, hED, hEπ⟩ := W.lev_π i ζ ⟨1, by rwa [pow_one]⟩
  have hζp : (PowerSeries.C ζ : PowerSeries LL) ^ PD.p = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  rw [hEπ, mul_pow, hζp, one_mul] at hL
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have ht0 : PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ - 1 := by
    have h := congrArg PowerSeries.constantCoeff hEπ
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hq0 : PowerSeries.constantCoeff (W.lev i ζ W.q) = 0 := by
    have h := congrArg PowerSeries.constantCoeff hL
    rw [map_mul, map_sub, map_pow, hE0, one_pow, map_one, sub_self, ht0] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ1)
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hq0
  refine ⟨u, hu, ?_⟩
  intro hu0
  have hX1 : ∀ g : PowerSeries LL, PowerSeries.coeff 1 (PowerSeries.X * g) = PowerSeries.constantCoeff g := by
    intro g
    first
      | simpa using PowerSeries.coeff_succ_X_mul (n := 0) (φ := g)
      | simpa using PowerSeries.coeff_succ_X_mul (R := LL) 0 g
      | simp [PowerSeries.coeff_X_mul]
      | simp [mul_comm PowerSeries.X g, PowerSeries.coeff_succ_mul_X]
  have hd : ∀ f : PowerSeries LL, PowerSeries.constantCoeff (PowerSeries.derivative LL f) = PowerSeries.coeff 1 f := by
    intro f
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    first
      | (rw [PowerSeries.derivative_coe, PowerSeries.coeff_derivativeFun]; simp)
      | (rw [PowerSeries.coeff_derivative]; simp)
      | simp [PowerSeries.derivative, PowerSeries.coeff_derivativeFun]
  have hD : PowerSeries.derivative LL (E ^ PD.p) = (PD.p : PowerSeries LL) * E ^ PD.p := by
    rw [Derivation.leibniz_pow, hED, smul_eq_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ PD.p), nsmul_eq_mul]
  have h1 : PowerSeries.coeff 1 (E ^ PD.p) = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hL
    rw [hu, mul_left_comm, hX1, map_mul, ht0, hu0, mul_zero, map_sub, PowerSeries.coeff_one] at h
    simpa using h.symm
  have h2 := congrArg PowerSeries.constantCoeff hD
  rw [hd, h1, map_mul, map_natCast, map_pow, hE0, one_pow, mul_one] at h2
  exact hp0 h2.symm

end Lq

section Indep

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [LocWach.Q, LocWach.q, hs]

theorem coeff_Xpow_mul_lt (k j : ℕ) (hj : j < k) (f : PowerSeries LL) :
    PowerSeries.coeff j (PowerSeries.X ^ k * f) = 0 := by
  first
    | (rw [PowerSeries.coeff_X_pow_mul']; exact if_neg (by omega))
    | simp [PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hj]

theorem lead_indep [IsDomain O] [IsFractionRing O LL] (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (ζ : LL)
    (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) (hPt : Pt i ζ τ)
    (hζ : IsPrimitiveRoot ζ PD.p) (hp2 : 2 ≤ PD.p) (hp0 : ((PD.p : ℕ) : LL) ≠ 0) (hs : W.s = 1)
    {r : ℕ} (bb : Fin r → W.DD T) (hbN : ∀ a, bb a ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! c : Fin r → LetA O n, x = ∑ a, c a • bb a) (M : ℕ)
    (hpa : ∀ a, W.Q ^ M • W.φD T ((letE (i - 1) : LetA O n) • bb a) ∈ W.N T) :
    LinearIndependent LL (fun a => W.levN T i ζ ⟨_, hpa a⟩ (M : ℤ)) := by
  classical
  obtain ⟨u, hu, hu0⟩ := lev_q_X_mul W i ζ hζ hp2 hp0
  have hlevQ : ∀ k : ℕ, W.lev i ζ (W.Q ^ k) = PowerSeries.X ^ k * u ^ k := by
    intro k; rw [map_pow, Q_eq_q W hs, hu, mul_pow]
  set d : Fin r → T.V ⊗[Qp] BdR := fun a => W.levN T i ζ ⟨_, hpa a⟩ (M : ℤ) with hd
  have hxa : ∀ a, ((letE (i - 1) : LetA O n) • bb a) ∈ W.N T := fun a => (W.N T).smul_mem _ (hbN a)
  have hDa : ∀ a (j : ℤ), W.levN T i ζ ⟨_, hpa a⟩ j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ∧
      (j < M → W.levN T i ζ ⟨_, hpa a⟩ j = 0) :=
    fun a j => (hP4.2 i ζ τ hPt).1.1 ⟨_, hxa a⟩ M (hpa a) j
  have hspan : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ≤ Submodule.span LL (Set.range d) := by
    rw [← (hP4.2 i ζ τ hPt).1.2, Submodule.span_le]
    rintro w ⟨x, k, hk, rfl⟩
    obtain ⟨c, hc, -⟩ := huniq x x.2
    have hz : W.Q ^ M • (W.Q ^ k • W.φD T x) ∈ W.N T := (W.N T).smul_mem _ hk

    have e1 : W.levN T i ζ ⟨_, hz⟩ ((M : ℤ) + k) =
        (PowerSeries.constantCoeff u) ^ M • W.levN T i ζ ⟨_, hk⟩ k := by
      have hsub : (⟨_, hz⟩ : ↥(W.N T)) = W.Q ^ M • (⟨_, hk⟩ : ↥(W.N T)) := rfl
      rw [hsub, W.levN_smul]
      have := Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.conv_lead (W.lev i ζ (W.Q ^ M)) (W.levN T i ζ ⟨_, hk⟩) k
        (fun j hj => ((hP4.2 i ζ τ hPt).1.1 x k hk j).2 hj) M
        (fun j hj => by rw [hlevQ]; exact coeff_Xpow_mul_lt M j hj _)
      rw [add_comm] at this
      unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.conv at this
      rw [this, hlevQ, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]

    have hsum : (letE i : LetA O n) • (W.Q ^ M • (W.Q ^ k • W.φD T x)) =
        ∑ a, (W.Q ^ k * W.φA (c a)) • (W.Q ^ M • W.φD T ((letE (i - 1) : LetA O n) • bb a)) := by
      have hφ : (letE i : LetA O n) • W.φD T x =
          ∑ a, W.φA (c a) • W.φD T ((letE (i - 1) : LetA O n) • bb a) := by
        rw [← φA_letE W i, ← φD_smulA, hc, Finset.smul_sum, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul, mul_comm, ← smul_smul, φD_smulA]
      rw [smul_comm _ (W.Q ^ M), smul_comm _ (W.Q ^ k), hφ, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [smul_smul]
      congr 1
      ring
    have hz' : (letE i : LetA O n) • (W.Q ^ M • (W.Q ^ k • W.φD T x)) ∈ W.N T := (W.N T).smul_mem _ hz
    have e2 : W.levN T i ζ ⟨_, hz⟩ ((M : ℤ) + k) =
        ∑ a, PowerSeries.coeff k (W.lev i ζ (W.Q ^ k * W.φA (c a))) • d a := by
      rw [← levN_letE W T i ζ ⟨_, hz⟩ hz']
      have hsub : (⟨_, hz'⟩ : ↥(W.N T)) = ∑ a, (W.Q ^ k * W.φA (c a)) • (⟨_, hpa a⟩ : ↥(W.N T)) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact hsum
      rw [hsub, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [W.levN_smul]
      have := Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.conv_lead (W.lev i ζ (W.Q ^ k * W.φA (c a))) (W.levN T i ζ ⟨_, hpa a⟩) M
        (fun j hj => (hDa a j).2 hj) k
        (fun j hj => by rw [map_mul, hlevQ, mul_assoc]; exact coeff_Xpow_mul_lt k j hj _)
      unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.conv at this
      rw [this]
    have hne : (PowerSeries.constantCoeff u) ^ M ≠ 0 := pow_ne_zero _ hu0
    have : W.levN T i ζ ⟨_, hk⟩ (k : ℤ) = ((PowerSeries.constantCoeff u) ^ M)⁻¹ •
        ∑ a, PowerSeries.coeff k (W.lev i ζ (W.Q ^ k * W.φA (c a))) • d a := by
      rw [← e2, e1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  have hcard : Fintype.card (Fin r) = finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i) := by
    rw [Fintype.card_fin, Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN.card_basis_eq W T hT bb hbN huniq,
      Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN.finrank_lat, Formalism.MainNotions.DeltaInvariantLattices.ιDi,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_ιV_inj PD) _),
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_finrank_DcrisL W hK hQ T hT]
  let d' : Fin r → ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i) := fun a => ⟨d a, (hDa a M).1⟩
  have hsp' : ⊤ ≤ Submodule.span LL (Set.range d') := by
    rintro ⟨y, hy⟩ -
    have h1 := hspan hy
    have h2 : Set.range d = (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i).subtype '' Set.range d' := by
      rw [← Set.range_comp]; rfl
    rw [h2, ← Submodule.map_span] at h1
    obtain ⟨y', hy', hyy⟩ := h1
    have : y' = ⟨y, hy⟩ := Subtype.ext hyy
    rw [← this]; exact hy'
  exact (linearIndependent_of_top_le_span_of_card_eq_finrank hsp' hcard).map'
    (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i).subtype (Submodule.ker_subtype _)

end Indep

section Avg

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem delF_mul {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  obtain ⟨k, hk, hgk⟩ := (W.DelF_def g).1 hg
  obtain ⟨m, hm, hhm⟩ := (W.DelF_def h).1 hh
  refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  calc (g * h) ^ (k * m) = (g ^ k) ^ m * (h ^ m) ^ k := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m k]
    _ = 1 := by rw [hgk, hhm, one_pow, one_pow, one_mul]

theorem delF_inv {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hgk⟩ := (W.DelF_def g).1 hg
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩

theorem γA_mul (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext j
  show W.γ₀ (g * h) (a j) = W.γ₀ g (W.γ₀ h (a j))
  rw [map_mul]
  rfl

theorem sum_γA_mem (c : LetA O n) : (∑ δ ∈ W.DelF, W.γA δ c) ∈ W.AΔ := by
  unfold LocWach.AΔ
  show ∀ δ ∈ W.DelF, W.γA δ (∑ δ' ∈ W.DelF, W.γA δ' c) = ∑ δ' ∈ W.DelF, W.γA δ' c
  intro δ hδ
  rw [map_sum]
  simp only [← γA_mul]
  exact Finset.sum_nbij' (fun x => δ * x) (fun x => δ⁻¹ * x)
    (fun a ha => delF_mul W hδ ha) (fun a ha => delF_mul W (delF_inv W hδ) ha)
    (fun a _ => inv_mul_cancel_left δ a) (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)

theorem sum_γD_eq (T : LocLat G Qp LL O) (x : W.DD T) (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    (∑ δ ∈ W.DelF, W.γD T δ x) = W.DelF.card • x := by
  rw [Finset.sum_congr rfl hx, Finset.sum_const]

end Avg

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem phispan_le (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (bb : Fin r → W.DD T)
    (huniq : ∀ x ∈ W.N T, ∃! c : Fin r → LetA O n, x = ∑ a, c a • bb a) :
    Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤
      Submodule.span (LetA O n) (Set.range fun a => W.φD T ((letE (i - 1) : LetA O n) • bb a)) := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan LocWach.Nl
  rw [Submodule.span_le]
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  obtain ⟨c, hc, -⟩ := huniq x hx
  rw [SetLike.mem_coe, LinearMap.smul_apply, LinearMap.id_apply, hc, Finset.smul_sum, map_sum]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  rw [smul_smul, mul_comm, ← smul_smul, φD_smulA W T]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem coeff_vanish [IsDomain O] [IsFractionRing O LL] (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (ζ : LL)
    (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) (hPt : Pt i ζ τ)
    [FiniteDimensional LL ↥(DdRE PD T.ρ τ)]
    (hζ : IsPrimitiveRoot ζ PD.p) (hp2 : 2 ≤ PD.p) (hp0 : ((PD.p : ℕ) : LL) ≠ 0) (hs : W.s = 1)
    {r : ℕ} (bb : Fin r → W.DD T) (hbN : ∀ a, bb a ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! c : Fin r → LetA O n, x = ∑ a, c a • bb a) (M : ℕ)
    (hpa : ∀ a, W.Q ^ M • W.φD T ((letE (i - 1) : LetA O n) • bb a) ∈ W.N T) (b : ℕ)
    (hj : JumpsInV PD T.ρ τ (Set.Iic (-(b : ℤ)))) (x : W.DD T) (hxN : x ∈ W.N T)
    (hxl : (letE i : LetA O n) • x = x) (g : Fin r → LetA O n)
    (hg : ∑ a, g a • W.φD T ((letE (i - 1) : LetA O n) • bb a) = x) :
    ∀ a, (PowerSeries.X : PowerSeries LL) ^ b ∣ W.lev i ζ (g a) := by
  classical
  obtain ⟨u, hu, -⟩ := lev_q_X_mul W i ζ hζ hp2 hp0
  have hlevQ : W.lev i ζ (W.Q ^ M) = PowerSeries.X ^ M * u ^ M := by
    rw [map_pow, Q_eq_q W hs, hu, mul_pow]
  have hind := lead_indep W Pt hK hQ T hT hP4 i ζ τ hτ hPt hζ hp2 hp0 hs bb hbN huniq M hpa
  have hxa : ∀ a, ((letE (i - 1) : LetA O n) • bb a) ∈ W.N T := fun a => (W.N T).smul_mem _ (hbN a)
  have hD : ∀ a, ∀ k < (M : ℤ), W.levN T i ζ ⟨_, hpa a⟩ k = 0 :=
    fun a k hk => ((hP4.2 i ζ τ hPt).1.1 ⟨_, hxa a⟩ M (hpa a) k).2 hk
  refine Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.triangular (fun a => W.levN T i ζ ⟨_, hpa a⟩) (M : ℤ) hD hind
    (fun a => W.lev i ζ (g a)) b (fun k hk => ?_)
  have hyN : W.Q ^ M • x ∈ W.N T := (W.N T).smul_mem _ hxN
  have hsub : (⟨_, hyN⟩ : ↥(W.N T)) = ∑ a, g a • (⟨_, hpa a⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm]
  have e1 : W.levN T i ζ ⟨_, hyN⟩ k =
      ∑ a, Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.conv (W.lev i ζ (g a)) (W.levN T i ζ ⟨_, hpa a⟩) k := by
    rw [hsub, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [W.levN_smul]; rfl
  rw [← e1]
  have hsub2 : (⟨_, hyN⟩ : ↥(W.N T)) = W.Q ^ M • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
  rw [hsub2, W.levN_smul]
  have hv := levN_vanish W Pt hK hQ T hT hP4 i ζ τ hτ hPt b hj ⟨x, hxN⟩ hxl
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv.conv_vanish (W.lev i ζ (W.Q ^ M)) (W.levN T i ζ ⟨x, hxN⟩) b hv M
    (by rw [hlevQ]; exact dvd_mul_right _ _) k (by omega)

end Main

section Recon

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  simp only [letE]
  rw [← Pi.single_mul, one_mul]

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  simp only [letE, Pi.single_apply]
  split_ifs <;> simp

theorem reconstruct (T : LocLat G Qp LL O) (i : ZMod n) (hπ : W.π₀ ∈ W.AΔ)
    (w : (LetA O n)ˣ) (hw : W.q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W)
    (κ : O) (hκ : κ * (W.DelF.card : O) = 1)
    {r : ℕ} (bb : Fin r → W.DD T) (hbΔ : ∀ a, bb a ∈ W.NΔ T)
    (x : W.DD T) (hx : x ∈ NDl W T i) (g : Fin r → LetA O n)
    (hg : ∑ a, g a • W.φD T ((letE (i - 1) : LetA O n) • bb a) = x) (b : ℕ) (h : Fin r → PowerSeries O)
    (hh : ∀ a, g a i = W.q₀ ^ b * h a) :
    x ∈ (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b) • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) := by
  have hx' : x ∈ W.N T ∧ ((letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x) := hx
  obtain ⟨-, hxe, hxΔ⟩ := hx'
  have hb : ∀ a, bb a ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (bb a) = bb a := hbΔ
  have hqpΔ : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
    have hqp : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
      unfold Formalism.MainNotions.LiftingTheory.qp
      exact W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
    exact hqp
  have hzN : ∀ a, (letE (i - 1) : LetA O n) • bb a ∈ NDl W T (i - 1) := by
    intro a
    show _ ∈ W.N T ∧ ((letE (i - 1) : LetA O n) • ((letE (i - 1) : LetA O n) • bb a) =
      (letE (i - 1) : LetA O n) • bb a ∧ ∀ δ ∈ W.DelF, W.γD T δ ((letE (i - 1) : LetA O n) • bb a) =
      (letE (i - 1) : LetA O n) • bb a)
    refine ⟨(W.N T).smul_mem _ (hb a).1, ?_, fun δ hδ => ?_⟩
    · rw [smul_smul, letE_mul_self]
    · rw [γD_smulA W T, γA_letE W, (hb a).2 δ hδ]
  obtain ⟨c, hc⟩ : ∃ c : Fin r → LetA O n,
      ∀ a, c a = (w : LetA O n) ^ b * ((letE i : LetA O n) * (fun _ => h a : LetA O n)) :=
    ⟨_, fun a => rfl⟩
  have hcoef : ∀ a, (letE i : LetA O n) * g a = Formalism.MainNotions.LiftingTheory.qp W ^ b * c a := by
    intro a
    rw [hc a, ← mul_assoc (Formalism.MainNotions.LiftingTheory.qp W ^ b), ← mul_pow, mul_comm (Formalism.MainNotions.LiftingTheory.qp W), ← hw]
    unfold LocWach.q
    funext j
    simp only [Pi.mul_apply, Pi.pow_apply, letE, Pi.single_apply]
    split_ifs with hj
    · subst hj
      rw [hh a]
      ring
    · simp
  have hxy : x = Formalism.MainNotions.LiftingTheory.qp W ^ b • ∑ a, c a • W.φD T ((letE (i - 1) : LetA O n) • bb a) := by
    rw [← hxe, ← hg, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [smul_smul, smul_smul, hcoef a]
  have hγ : ∀ δ ∈ W.DelF, W.γD T δ x =
      Formalism.MainNotions.LiftingTheory.qp W ^ b • ∑ a, W.γA δ (c a) • W.φD T ((letE (i - 1) : LetA O n) • bb a) := by
    intro δ hδ
    rw [hxy, γD_smulA W T, map_pow, hqpΔ δ hδ, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [γD_smulA W T, ← W.φγ_comm, γD_smulA W T, γA_letE W, (hb a).2 δ hδ]
  have hxavg : x = κ • ∑ δ ∈ W.DelF, W.γD T δ x := by
    rw [sum_γD_eq W T x hxΔ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hκ, one_smul]
  have hx2 : x = Formalism.MainNotions.LiftingTheory.qp W ^ b • ∑ a, (κ • ∑ δ ∈ W.DelF, W.γA δ (c a)) •
      W.φD T ((letE (i - 1) : LetA O n) • bb a) := by
    rw [hxavg, Finset.sum_congr rfl hγ, ← Finset.smul_sum, smul_comm κ, Finset.sum_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_smul, smul_assoc]
  refine Submodule.mem_map.mpr ⟨∑ a, (κ • ∑ δ ∈ W.DelF, W.γA δ (c a)) •
      W.φD T ((letE (i - 1) : LetA O n) • bb a), ?_, ?_⟩
  · show _ ∈ Submodule.span O {y | ∃ a ∈ W.AΔ, ∃ x ∈ NDl W T (i - 1), y = a • (W.φD T) x}
    exact Submodule.sum_mem _ (fun a _ =>
      Submodule.subset_span ⟨_, W.AΔ.smul_mem (sum_γA_mem W (c a)) κ, _, hzN a, rfl⟩)
  · rw [LinearMap.smul_apply, LinearMap.id_apply, ← hx2]

end Recon

section Final

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem ninQbP_of [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hPt : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Pt i ζ τ)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) : Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.NinQbP W := by
  intro d T₁ T₂ F b S η m hS hm i hi x hx
  classical
  have hK : Function.Bijective (algebraMap K₀ K) := hS.1.1
  have hs1 : W.s = 1 := hS.1.2.1
  have hp2' : PD.p ≠ 2 := hS.1.2.2
  obtain ⟨hdom, hdvr, hfrac⟩ := hS.2.2.2.1
  obtain ⟨ζ₀, hζ₀⟩ := hS.2.2.2.2.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.mp hi).2
  have hpp := PD.hp
  have hp2 : 2 ≤ PD.p := hpp.two_le
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h2 := W.v_l
    rw [h0, AddValuation.map_zero] at h2
    simp at h2
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hK).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨hcardΔ, -, h9⟩ := hP9 T₂ hT hs1 hp2'
  obtain ⟨hring, hmod⟩ := h9 hfin1
  obtain ⟨⟨r, bb, hbΔ, huniq, -⟩, -⟩ := hmod
  have hbN : ∀ a, bb a ∈ W.N T₂ := fun a => (hbΔ a).1
  obtain ⟨w, hw⟩ := hring.2.2.2.2.1
  have hw' : W.q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [hw]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp]
  have hcard : W.DelF.card = PD.p - 1 := by rw [hcardΔ, hfin1, Nat.div_one]
  have hunit : IsUnit ((W.DelF.card : ℕ) : O) := by
    by_contra hnu
    have h1 : ((W.DelF.card : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hnu
    have h2 : ((PD.p : ℕ) : O) - ((W.DelF.card : ℕ) : O) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hpm h1
    rw [h2] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  obtain ⟨κ, hκ⟩ := hunit.exists_left_inv
  obtain ⟨τ, hτ⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_lift hK (W.emb i)
  have hfd := fd_DdRE W hQ hS i τ hτ
  have hjτ := jumps_le W hE hC hQ hS hm i hie τ hτ
  let Mf : ZMod n → ℕ := fun j => b j + S + η
  let hf : ZMod n → ℕ := fun j => if j = i then 0 else b j + S + η
  have hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mf hf := by
    intro τ' j hτ' a ha
    have hw2 := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS j τ' hτ' a ha
    have hbound : -((b j + S + η : ℕ) : ℤ) ≤ a ∧ a ≤ ((b j + S + η : ℕ) : ℤ) := by
      unfold JumpWinS at hw2
      split_ifs at hw2 <;> (simp only [Set.mem_union, Set.mem_Icc] at hw2; push_cast; omega)
    simp only [Mf, hf, Set.mem_Icc]
    split_ifs with hji
    · subst hji
      have := jumps_le W hE hC hQ hS hm j hie τ' hτ' a ha
      simp only [Set.mem_Iic] at this
      push_cast at hbound ⊢
      omega
    · push_cast at hbound ⊢
      omega
  have h5 := hP5 T₂ Mf hf hT hJL
  have hxNl : x ∈ W.Nl T₂ i := ⟨x, hx.1, by simpa using hx.2.1⟩
  have h52 := h5.2.1 i x hxNl
  simp only [hf, if_true, pow_zero, one_smul] at h52
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (phispan_le W T₂ i bb huniq h52)
  have hpa : ∀ a, W.Q ^ (Mf i) • W.φD T₂ ((letE (i - 1) : LetA O n) • bb a) ∈ W.N T₂ :=
    fun a => h5.1 i _ ⟨bb a, hbN a, rfl⟩
  have hroot : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∀ a,
      (PowerSeries.X : PowerSeries LL) ^ (b i) ∣ W.lev i ζ (g a) := by
    intro ζ hζ
    obtain ⟨τζ, hτζ, hPtζ⟩ := hPt hS.1 hS.2.1 i ζ hζ
    have := fd_DdRE W hQ hS i τζ hτζ
    exact coeff_vanish W Pt hK hQ T₂ hT (hP4 T₂ hT) i ζ τζ hτζ hPtζ hζ hp2 hp0 hs1 bb hbN huniq
      (Mf i) hpa (b i) (jumps_le W hE hC hQ hS hm i hie τζ hτζ) x hx.1 hx.2.1 g hg
  have hdiv : ∀ a, ∃ h : PowerSeries O, g a i = W.q₀ ^ (b i) * h := fun a =>
    Formalism.MainNotions.RamifiedCoefficientChains.S9.LevW.q_pow_dvd W hpp hpm hinj hζ₀ i (b i) (g a i)
      (fun ζ hζ => by rw [← Formalism.MainNotions.RamifiedCoefficientChains.S9.LevW.lev_eq_levC]; exact hroot ζ hζ a)
  choose h hh using hdiv
  exact reconstruct W T₂ i (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) w hw' κ hκ bb hbΔ x hx g hg (b i) h hh

theorem lemmaDN0_of_admits [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hPt : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Pt i ζ τ)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) : Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 W := by
  unfold Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0
  intro d T₁ T₂ F b S η m hS hm i hi x hx
  have hπ : W.π₀ ∈ W.AΔ := by
    unfold LocWach.AΔ
    show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
    intro δ hδ
    unfold LocWach.π₀ LocWach.π₀₁
    funext j
    show W.γ₀ δ (1 - (PD.p : PowerSeries O) + ∑ δ' ∈ W.DelF, W.γ₀ δ' (1 + PowerSeries.X)) =
      1 - (PD.p : PowerSeries O) + ∑ δ' ∈ W.DelF, W.γ₀ δ' (1 + PowerSeries.X)
    rw [map_add, map_sub, map_one, map_natCast, map_sum]
    congr 1
    simp only [← AlgHom.mul_apply, ← map_mul]
    exact Finset.sum_nbij' (fun x => δ * x) (fun x => δ⁻¹ * x)
      (fun a ha => delF_mul W hδ ha) (fun a ha => delF_mul W (delF_inv W hδ) ha)
      (fun a _ => inv_mul_cancel_left δ a) (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)
  have hqp : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
    unfold Formalism.MainNotions.LiftingTheory.qp
    exact W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
  have hN := ninQbP_of W hE hC hQ Pt hP4 hP5 hP9 hPt hpm
  unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.NinQbP at hN
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hN d T₁ T₂ F b S η m hS hm i hi x hx)
  rw [LinearMap.smul_apply, LinearMap.id_apply] at hyx
  have hx' : x ∈ W.N T₂ ∧ ((letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T₂ δ x = x) := hx
  obtain ⟨hxN, hxe, hxΔ⟩ := hx'
  obtain ⟨t, ht⟩ : ∃ t : LetA O n,
      t = ∑ k ∈ Finset.range S, (PD.p : LetA O n) ^ k * Formalism.MainNotions.LiftingTheory.qp W ^ (S - 1 - k) := ⟨_, rfl⟩
  have hgeom : (PD.p : LetA O n) ^ S = Formalism.MainNotions.LiftingTheory.qp W ^ S - t * W.π₀ := by
    have h1 := geom_sum₂_mul (PD.p : LetA O n) (Formalism.MainNotions.LiftingTheory.qp W) S
    have h2 : (PD.p : LetA O n) - Formalism.MainNotions.LiftingTheory.qp W = -W.π₀ := by
      unfold Formalism.MainNotions.LiftingTheory.qp
      ring
    rw [h2, ← ht] at h1
    linear_combination (-1 : LetA O n) * h1
  have htA : t ∈ W.AΔ := by
    rw [ht]
    exact W.AΔ.sum_mem (fun k _ => W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) (W.AΔ.pow_mem hqp _))
  have htΔ : ∀ δ ∈ W.DelF, W.γA δ t = t := by
    exact htA
  have hz : -(t • x) ∈ NDl W T₂ i := by
    show _ ∈ W.N T₂ ∧ ((letE i : LetA O n) • -(t • x) = -(t • x) ∧
      ∀ δ ∈ W.DelF, W.γD T₂ δ (-(t • x)) = -(t • x))
    refine ⟨(W.N T₂).neg_mem ((W.N T₂).smul_mem t hxN), ?_, fun δ hδ => ?_⟩
    · rw [smul_neg, smul_comm, hxe]
    · rw [map_neg, γD_smulA W T₂, htΔ δ hδ, hxΔ δ hδ]
  have heq : ((PD.p : O) ^ S) • x = W.π₀ • (-(t • x)) + Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S) • y := by
    rw [← algebraMap_smul (LetA O n) ((PD.p : O) ^ S) x, map_pow, map_natCast, hgeom, ← hyx]
    simp only [smul_neg, smul_smul, ← neg_smul, ← add_smul]
    congr 1
    ring
  rw [heq]
  exact Submodule.add_mem_sup
    (Submodule.mem_map.mpr ⟨_, hz, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩)
    (Submodule.mem_map.mpr ⟨y, hy, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩)

end Final

end Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ
