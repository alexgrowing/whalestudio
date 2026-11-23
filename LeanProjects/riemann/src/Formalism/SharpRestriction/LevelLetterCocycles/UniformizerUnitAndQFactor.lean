import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DualLemmaOfDeterminant

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB TensorProduct

theorem dvd_of_mul_pow {O : Type} [CommRing O] [IsDomain O] (x c l : O) (hl : l ≠ 0) (hc : IsUnit c)
    (A B : ℕ) (hAB : A ≤ B) (h : x * l ^ A = c * l ^ B) : x ∣ l ^ (B - A) := by
  have hB : l ^ B = l ^ (B - A) * l ^ A := by rw [← pow_add, Nat.sub_add_cancel hAB]
  rw [hB, ← mul_assoc] at h
  have hx : x = c * l ^ (B - A) := mul_right_cancel₀ (pow_ne_zero A hl) h
  obtain ⟨v, rfl⟩ := hc
  exact ⟨↑v⁻¹, by rw [hx, mul_comm (v : O), mul_assoc, Units.mul_inv, mul_one]⟩

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem qp_unit (hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  have := W.EE_complete
  obtain ⟨u, hu⟩ := hπu
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _
    (Ideal.mem_span_singleton_self ((PD.p : ℕ) : W.EE)))) (↑u⁻¹ : W.EE)
  have : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) =
      (u : W.EE) * (((PD.p : ℕ) : W.EE) * ↑u⁻¹ + 1) := by
    rw [Formalism.MainNotions.LiftingTheory.qp, map_add, ← hu, map_natCast]
    rw [mul_add, mul_one, mul_comm ((PD.p : ℕ) : W.EE), ← mul_assoc, Units.mul_inv, one_mul, add_comm]
  rw [this]
  exact u.isUnit.mul hj

end

section Red

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem uniformizer_unit_and_q_factor (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (hp : 2 ≤ PD.p) :
    PowerSeries.constantCoeff W.π₀₁ = 0 ∧ IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧
      ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, -⟩ := h9' hfin1
  obtain ⟨w, hw⟩ := hring.2.2.1
  obtain ⟨w', hw'⟩ := hring.2.2.2.2.1
  refine ⟨?_, ?_, w', ?_⟩
  · have h1 := congrFun hw 0
    simp only [LocWach.π₀, Pi.mul_apply, Pi.pow_apply, letπ] at h1
    rw [h1, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  · rw [hw, map_mul, map_pow]
    exact ((w.isUnit.map _)).mul (W.EE_π.pow _)
  · rw [hw']
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp]

theorem red_exists (T : LocLat G Qp LL O) (i : ZMod n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0)
    (hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {r : ℕ} (e : Fin r → W.DD T)
    (he : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) :
    ∃ red : ↥(NDl W T i) →ₗ[O] (Fin r → O), IsRed W T i red ∧
      ∀ (x : ↥(NDl W T i)) (a : Fin r → PowerSeries O),
        (x : W.DD T) = ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a k) • e k → red x = fun k => PowerSeries.constantCoeff (a k) := by
  classical
  have hinjπ : ∀ y : W.DD T, W.π₀ • y = 0 → y = 0 := by
    intro y hy
    rw [← algebraMap_smul W.EE W.π₀ y] at hy
    obtain ⟨u, hu⟩ := hπu
    have := congrArg (fun z => (↑u⁻¹ : W.EE) • z) hy
    simp only [smul_zero, ← hu, smul_smul, Units.inv_mul, one_smul] at this
    exact this
  have hex : ∀ x : ↥(NDl W T i), ∃! a : Fin r → PowerSeries O,
      (x : W.DD T) = ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a k) • e k := fun x => he.2 x x.2.1 x.2.2
  let coord : ↥(NDl W T i) → Fin r → PowerSeries O := fun x => (hex x).exists.choose
  have hcoord : ∀ x : ↥(NDl W T i), (x : W.DD T) = ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (coord x k) • e k :=
    fun x => (hex x).exists.choose_spec
  have huniq : ∀ (x : ↥(NDl W T i)) (a : Fin r → PowerSeries O),
      (x : W.DD T) = ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a k) • e k → coord x = a :=
    fun x a ha => (hex x).unique (hcoord x) ha
  let red : ↥(NDl W T i) →ₗ[O] (Fin r → O) :=
    { toFun := fun x k => PowerSeries.constantCoeff (coord x k)
      map_add' := by
        intro x y
        have h := huniq (x + y) (coord x + coord y) (by
          rw [Submodule.coe_add, hcoord x, hcoord y, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Pi.add_apply, ShB.evaluation_add W hz, add_smul])
        funext k; rw [h]; simp
      map_smul' := by
        intro c x
        have h := huniq (c • x) (fun k => PowerSeries.C c * coord x k) (by
          rw [Submodule.coe_smul, hcoord x, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ShB.evalZero_mul W hz, ShB.evalZero_C, mul_smul, algebraMap_smul])
        funext k; rw [h]; simp }
  refine ⟨red, ⟨?_, ?_⟩, fun x a ha => by
    funext k; show PowerSeries.constantCoeff (coord x k) = _; rw [huniq x a ha]⟩
  · intro lam
    have hmem : (∑ k, lam k • e k : W.DD T) ∈ NDl W T i := Submodule.sum_mem _ fun k _ =>
      (NDl W T i).smul_mem (lam k) (show e k ∈ NDl W T i from ⟨(he.1 k).1, (he.1 k).2⟩)
    refine ⟨⟨_, hmem⟩, ?_⟩
    have h := huniq ⟨_, hmem⟩ (fun k => PowerSeries.C (lam k)) (by
      show (∑ k, lam k • e k : W.DD T) = _
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ShB.evalZero_C, algebraMap_smul])
    funext k
    show PowerSeries.constantCoeff (coord ⟨_, hmem⟩ k) = lam k
    rw [h]; simp
  · ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx0
      have hdv : ∀ k, ∃ a', coord x k = PowerSeries.X * a' := fun k =>
        PowerSeries.X_dvd_iff.mpr (congrFun hx0 k)
      choose a' ha' using hdv
      let y : W.DD T := ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a' k) • e k
      have hxy : (x : W.DD T) = W.π₀ • y := by
        rw [hcoord x, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ha' k, ShB.evalZero_mul W hz, ShB.evalZero_X_eq_pi0 W hz, mul_smul]
      have hyN : y ∈ W.N T := Submodule.sum_mem _ fun k _ => (W.N T).smul_mem _ (he.1 k).1
      have hyl : (letE i : LetA O n) • y = y := by
        simp only [y, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_comm, (he.1 k).2.1]
      have hyΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y := by
        intro δ hδ
        have h2 := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T δ W.π₀ y
        rw [uniformizer_mem_delta_invariants W δ hδ, ← hxy, x.2.2.2 δ hδ, hxy] at h2
        have h1 : W.π₀ • (W.γD T δ y - y) = 0 := by rw [smul_sub, ← h2, sub_self]
        exact sub_eq_zero.mp (hinjπ _ h1)
      exact ⟨y, ⟨hyN, hyl, hyΔ⟩, by simp [hxy]⟩
    · rintro ⟨y, hy, hxy⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      have h := huniq x (fun k => PowerSeries.X * coord ⟨y, hy⟩ k) (by
        rw [Submodule.subtype_apply] at hxy
        have hy' : y = ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (coord ⟨y, hy⟩ k) • e k := hcoord ⟨y, hy⟩
        rw [← hxy]
        conv_lhs => rw [hy']
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ShB.evalZero_mul W hz, ShB.evalZero_X_eq_pi0 W hz, mul_smul])
      funext k
      show PowerSeries.constantCoeff (coord x k) = 0
      rw [h]; simp

end Red

section Split

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def ftE (T : LocLat G Qp LL O) {r : ℕ} (e' : Fin r → W.DD T) (Z : Matrix (Fin r) (Fin r) (PowerSeries O))
    (k : Fin r) : W.DD T :=
  ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m k) • ((W.φD T) ^ 1) (e' m)

def gE (T : LocLat G Qp LL O) (h c : ℕ) {r : ℕ} (e' : Fin r → W.DD T)
    (Z : Matrix (Fin r) (Fin r) (PowerSeries O)) (k : Fin r) : W.DD T :=
  (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c •
    (Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T e' Z k)

def ZProps (T : LocLat G Qp LL O) (i : ZMod n) (X σ : ℕ) {r : ℕ} (e' : Fin r → W.DD T)
    (he' : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T (i - 1) e') (Z : Matrix (Fin r) (Fin r) (PowerSeries O)) : Prop :=
  (∀ m k, PowerSeries.constantCoeff (Z m k) = if m = k then ((PD.p : ℕ) : O) ^ σ else 0) ∧
  ∀ k (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ d,
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T (i - 1 + ((1 : ℕ) : ZMod n)) ζ (ftE W T e' Z k) d →
    ∀ s : ℤ, s < X → d s = if s = 0 then (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
      ((φVB PD (LL := LL) (V := T.V))^[1] (W.cmp T ⟨e' k, (he'.1 k).1⟩)) else 0

def GMem : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∀ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ)
        (had : AdaptData W T₂ i (b i + S) η m e' m' u) (σ : ℕ) (Z : Matrix _ _ (PowerSeries O)),
        ZProps W T₂ i (b i + S + η) σ e' had.1 Z →
        ∀ (j : Fin m') (hmr : m' ≤ finrank LL T₂.V),
          gE W T₂ (b i + S) ((b i + S : ℕ) + u j).toNat e' Z (Fin.castLE hmr j) ∈ NDl W T₂ i

def DetAlg : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∀ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ)
        (had : AdaptData W T₂ i (b i + S) η m e' m' u) (σ : ℕ) (Z : Matrix _ _ (PowerSeries O)),
        σ ≤ 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ →
        (∀ m₁ k, PowerSeries.constantCoeff (Z m₁ k) = if m₁ = k then ((PD.p : ℕ) : O) ^ σ else 0) →
        (∀ (j : Fin m') (hmr : m' ≤ finrank LL T₂.V),
          gE W T₂ (b i + S) ((b i + S : ℕ) + u j).toNat e' Z (Fin.castLE hmr j) ∈ NDl W T₂ i) →
        ∃ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)) (_ : IsRed W T₂ i red)
          (m'' : ℕ) (_ : m'' ≤ m) (g : Fin m'' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
          (cols : Fin r → ↥(NDl W T₂ i)),
          (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
            ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
          ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
            (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

theorem sigma_le {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) :
    ⌈((1 : ℕ) + (b i + S + η : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1⌉₊ ≤ 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ := by
  have hl11 : (11 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hS.2.1
  have hl1 : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
  have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
  have hX : ((1 : ℕ) + (b i + S + η : ℕ) : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) + 1 := by
    unfold hpar; push_cast
    have : (b i : ℝ) ≤ (Finset.univ.sup b : ℕ) := by exact_mod_cast hbi
    linarith
  have hcD1 : (1 : ℝ) ≤ cD PD.p (hpar n b S + η) := by
    unfold cD
    have : 0 ≤ (((hpar n b S + η : ℕ) : ℝ) + 1) / ((PD.p : ℝ) - 1) := by positivity
    linarith
  have hx : ((1 : ℕ) + (b i + S + η : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1 ≤ cD PD.p (hpar n b S + η) := by
    unfold cD
    have := div_le_div_of_nonneg_right hX hl1.le
    linarith
  have hfl1 : 1 ≤ ⌊cD PD.p (hpar n b S + η)⌋₊ := Nat.le_floor (by exact_mod_cast hcD1)
  have hlt : cD PD.p (hpar n b S + η) < (⌊cD PD.p (hpar n b S + η)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [Nat.ceil_le]
  have : ((⌊cD PD.p (hpar n b S + η)⌋₊ : ℝ) + 1) ≤ ((2 * ⌊cD PD.p (hpar n b S + η)⌋₊ : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ (⌊cD PD.p (hpar n b S + η)⌋₊ : ℝ) := by exact_mod_cast hfl1
    linarith
  linarith

theorem detColsE_of (hZ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZTool W) (hA : AdaptBas W) (ha : GMem W) (hb : DetAlg W) :
    DetColsE W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨e', m', u, had⟩ := hA d T₁ T₂ F b S η m hS i hi
  set σ := ⌈((1 : ℕ) + (b i + S + η : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1⌉₊ with hσ
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  obtain ⟨Z, Z', R, hZ0, -, hZk⟩ := hZ hS.1 hS.2.1 1 (b i + S + η) σ
    (Or.inl ⟨rfl, le_rfl, by rw [hσ]⟩) T₂ hT (i - 1) _ e' had.1
  have hZP : ZProps W T₂ i (b i + S + η) σ e' had.1 Z :=
    ⟨hZ0, fun k ζ hζ d' hd' => (hZk k).2 ζ hζ d' hd'⟩
  exact hb d T₁ T₂ F b S η m hS i hi e' m' u had σ Z (sigma_le W hS i) hZ0
    (fun j hmr => ha d T₁ T₂ F b S η m hS i hi e' m' u had σ Z hZP j hmr)

theorem lemmaDN_of_S1E (hZ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZTool W) (hA : AdaptBas W) (ha : GMem W) (hb : DetAlg W) :
    LemmaDN W :=
  lemmaDN_of_detE W (detColsE_of W hZ hA ha hb)

end Split

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS
