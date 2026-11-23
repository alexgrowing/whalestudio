import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem absV_mul (x y : Cv v) : absV v (x * y) = absV v x * absV v y := by simp [absV]

theorem absV_nonneg (x : Cv v) : 0 ≤ absV v x := NNReal.coe_nonneg _

theorem absV_one : absV v (1 : Cv v) = 1 := by simp [absV]

theorem absV_pow (x : Cv v) (j : ℕ) : absV v (x ^ j) = absV v x ^ j := by simp [absV]

theorem absV_inv (x : Cv v) : absV v x⁻¹ = (absV v x)⁻¹ := by simp [absV]

theorem absV_unif {ϖ : Cv v} (h : IsUnifV K v ϖ) : absV v ϖ = ((qV K v : ℝ))⁻¹ := by
  unfold absV
  rw [h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe,
    toAdd_ofAdd, _root_.zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
  rfl

theorem absV_unit (u : (𝒪)ˣ) : absV v (algebraMap 𝒪 (Cv v) u) = 1 := by
  have h : Valued.v (algebraMap 𝒪 (Cv v) u) = 1 :=
    (Valuation.Integers.one_of_isUnit (Valuation.valuationSubring.integers _) u.isUnit)
  rw [absV, h, map_one, NNReal.coe_one]

def wt (s : ℝ) {m : ℕ} (g : GL (Fin m) (Cv v)) : ℂ := ((absV v g.1.det ^ s : ℝ) : ℂ)

theorem wt_one (s : ℝ) {m : ℕ} : wt s (1 : GL (Fin m) (Cv v)) = 1 := by simp [wt, absV_one]

theorem wt_mul (s : ℝ) {m : ℕ} (g h : GL (Fin m) (Cv v)) : wt s (g * h) = wt s g * wt s h := by
  simp only [wt, Units.val_mul, det_mul, absV_mul, Real.mul_rpow (absV_nonneg _) (absV_nonneg _),
    Complex.ofReal_mul]

def rep {X : Type} {m : ℕ} (s : ℝ) (a : X → GL (Fin m) (Cv v) → X) (a1 : ∀ y, a y 1 = y)
    (am : ∀ y g h, a y (g * h) = a (a y g) h) : Representation ℂ (GL (Fin m) (Cv v)) (X → ℂ) where
  toFun g :=
    { toFun := fun Φ y => wt s g * Φ (a y g)
      map_add' := fun Φ Ψ => funext fun y => by simp [mul_add]
      map_smul' := fun c Φ => funext fun y => by simp [mul_left_comm] }
  map_one' := by ext Φ y; simp [wt_one, a1]
  map_mul' g h := by ext Φ y; simp [wt_mul, am, mul_assoc]

variable (v) in

def rS (n c : ℕ) : Representation ℂ (GL (Fin c) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  rep ((n : ℝ) / 2) (fun y g => y * g.1) (by simp) (by simp [Matrix.mul_assoc])

variable (v) in

def rT (n c : ℕ) : Representation ℂ (GL (Fin n) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  rep ((c : ℝ) / 2) (fun y z => z.1ᵀ * y) (by simp)
    (by simp [Matrix.mul_assoc, Matrix.transpose_mul])

theorem rS_apply {n c : ℕ} (g : GL (Fin c) (Cv v)) (Φ) (y) :
    rS v n c g Φ y = wt ((n : ℝ) / 2) g * Φ (y * g.1) := rfl

theorem rT_apply {n c : ℕ} (z : GL (Fin n) (Cv v)) (Φ) (y) :
    rT v n c z Φ y = wt ((c : ℝ) / 2) z * Φ (z.1ᵀ * y) := rfl

theorem rS_rT {n c : ℕ} (g : GL (Fin c) (Cv v)) (z : GL (Fin n) (Cv v)) (Φ) :
    rS v n c g (rT v n c z Φ) = rT v n c z (rS v n c g Φ) := by
  funext y
  simp only [rS_apply, rT_apply, Matrix.mul_assoc]
  ring

variable (v) in

def phi0 (n c : ℕ) : Matrix (Fin n) (Fin c) (Cv v) → ℂ :=
  Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1

theorem intM_iff' {n c : ℕ} {y : Matrix (Fin n) (Fin c) (Cv v)} :
    IntM 𝒪 y ↔ ∀ i j, Valued.v (y i j) ≤ 1 :=
  forall₂_congr fun _ _ => ⟨fun ⟨o, h⟩ => h ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

open Classical in
theorem characteristic_function_integral_apply {n c : ℕ} (y : Matrix (Fin n) (Fin c) (Cv v)) :
    phi0 v n c y = if IntM 𝒪 y then 1 else 0 := by
  unfold phi0
  by_cases h : IntM 𝒪 y
  · rw [if_pos h, Set.indicator_of_mem (show y ∈ {x | ∀ i j, Valued.v (x i j) ≤ 1} from intM_iff'.1 h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem
      (show y ∉ {x | ∀ i j, Valued.v (x i j) ≤ 1} from fun h' => h (intM_iff'.2 h'))]

theorem mem_KGL {m : ℕ} {g : GL (Fin m) (Cv v)} : g ∈ KGL v m ↔ GInt 𝒪 g :=
  ⟨fun h => ⟨intM_iff'.2 fun i j => P.cartan_entries_of_mem _ _ h i j,
    intM_iff'.2 fun i j => P.cartan_entries_of_mem _ _ (inv_mem h) i j⟩,
    fun h => P.cartan_mem_of_entries _ _ (intM_iff'.1 h.1) (intM_iff'.1 h.2)⟩

theorem wt_of_mem (s : ℝ) {m : ℕ} {g : GL (Fin m) (Cv v)} (h : g ∈ KGL v m) : wt s g = 1 := by
  obtain ⟨u, hu⟩ := (mem_KGL.1 h).det
  rw [wt, hu, absV_unit, Real.one_rpow, Complex.ofReal_one]

theorem intM_mul_iff {n c : ℕ} {g : GL (Fin c) (Cv v)} (h : GInt 𝒪 g)
    (y : Matrix (Fin n) (Fin c) (Cv v)) : IntM 𝒪 (y * g.1) ↔ IntM 𝒪 y :=
  ⟨fun hy => by simpa [Matrix.mul_assoc] using hy.mul h.2, fun hy => hy.mul h.1⟩

theorem intM_tr_iff {n c : ℕ} (z : Matrix (Fin n) (Fin n) (Cv v))
    (y : Matrix (Fin n) (Fin c) (Cv v)) : IntM 𝒪 (zᵀ * y) ↔ IntM 𝒪 (yᵀ * z) :=
  ⟨fun h => by simpa [Matrix.transpose_mul] using h.transpose,
    fun h => by simpa [Matrix.transpose_mul] using h.transpose⟩

theorem sphericalVector_fixed_right (n c : ℕ) : phi0 v n c ∈ fixed (rS v n c) (KGL v c) :=
  mem_fixed.2 fun k hk => funext fun y => by
    rw [rS_apply, wt_of_mem _ hk, one_mul, characteristic_function_integral_apply, characteristic_function_integral_apply, intM_mul_iff (mem_KGL.1 hk)]

theorem sphericalVector_fixed_left (n c : ℕ) : phi0 v n c ∈ fixed (rT v n c) (KGL v n) :=
  mem_fixed.2 fun k hk => funext fun y => by
    rw [rT_apply, wt_of_mem _ hk, one_mul, characteristic_function_integral_apply, characteristic_function_integral_apply, intM_tr_iff,
      intM_mul_iff (mem_KGL.1 hk)]
    classical
    exact if_congr ⟨fun h => h.transpose, fun h => h.transpose⟩ rfl rfl

theorem heckeVec_apply {G X : Type} [Group G] {J : Subgroup G} (hJ : IsCommensurated J)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ J) (ρ : Representation ℂ G (X → ℂ)) (Φ : X → ℂ) (y : X) :
    heckeVec ρ J h Φ y = ∑ᶠ c : G ⧸ J, h c.out * ρ c.out Φ y :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) y).toAddMonoidHom.map_finsum
    (finite_heckeVec hJ hh ρ Φ)

theorem hk_tor {p : 𝒪} (h0 : (p : Cv v) ≠ 0) {m j : ℕ} (hj : j ≤ m) :
    Hk 𝒪 p j (tor h0 fun i : Fin m => if (i : ℕ) < j then 1 else 0) := by
  refine ⟨intM_iff'.2 fun a b => ?_, intM_iff'.2 fun a b => ?_, 1, ?_⟩
  · rw [tor_val, diagonal_apply]
    split_ifs
    · rw [zpow_one]; exact p.2
    · simp
    · simp
  · change Valued.v ((p : Cv v) * diagonal (fun i : Fin m =>
      (p : Cv v) ^ (-(if (i : ℕ) < j then 1 else 0 : ℤ))) a b) ≤ 1
    rw [diagonal_apply]
    split_ifs
    · simp [h0]
    · rw [neg_zero, zpow_zero, mul_one]; exact p.2
    · simp
  · rw [tor_val, det_diagonal]
    simp only [apply_ite (fun e : ℤ => (p : Cv v) ^ e), zpow_one, zpow_zero]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Fin.card_filter_val_lt,
      min_eq_right hj]
    simp

open Classical in

theorem Tj_count {X : Type} {m j : ℕ} (hj : j ≤ m) {p : 𝒪} (hp : IsUnifV K v (p : Cv v))
    (h0 : (p : Cv v) ≠ 0) : ∃ R : Finset (GL (Fin m) (Cv v) ⧸ KGL v m),
      Reps 𝒪 (tor h0 fun i : Fin m => if (i : ℕ) < j then 1 else 0) R Quotient.out ∧
      ∀ (s : ℝ) (ρ : Representation ℂ (GL (Fin m) (Cv v)) (X → ℂ)) (Φ : X → ℂ) (y : X)
        (Q : GL (Fin m) (Cv v) → Prop), (∀ g, ρ g Φ y = wt s g * if Q g then 1 else 0) →
        heckeVec ρ (KGL v m) (Tj ℂ m (Ov K v) p j) Φ y =
          ((((qV K v : ℝ)⁻¹ ^ j) ^ s : ℝ) : ℂ) * Nat.card {γ // γ ∈ R ∧ Q γ.out} := by
  have hK : IsCommensurated (KGL v m) := Final.GLintComm K v m
  set α := tor h0 fun i : Fin m => if (i : ℕ) < j then (1 : ℤ) else 0
  have hf := P.finite_support_cosets hK (Final.DosetIndMem _ (KGL v m) ℂ α).2
  have hR : ∀ γ, γ ∈ hf.toFinset ↔ ∃ a ∈ KGL v m, ∃ b ∈ KGL v m, γ.out = a * α * b := fun γ => by
    rw [Set.Finite.mem_toFinset]
    refine ⟨fun h => by_contra fun h' => h (dosetInd_of_not h'), fun h => ?_⟩
    change dosetInd ℂ _ α γ.out ≠ 0
    rw [dosetInd_of_mem h]; exact one_ne_zero
  refine ⟨hf.toFinset, ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩, fun s ρ Φ y Q hQ => ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := (hR γ).1 hγ
    exact ⟨a, b, mem_KGL.1 ha, mem_KGL.1 hb, e⟩
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL v m) (k₁ * α * k₂)
    refine ⟨(k₁ * α * k₂ : GL (Fin m) (Cv v)), ⟨(hR _).2 ⟨k₁, mem_KGL.2 h₁, k₂ * k,
      mul_mem (mem_KGL.2 h₂) k.2, by rw [hk]; group⟩, mem_KGL.1 ?_⟩, fun γ hγ => ?_⟩
    · rw [hk]
      rw [show (k₁ * α * k₂ * k)⁻¹ * (k₁ * α * k₂) = (k : GL (Fin m) (Cv v))⁻¹ by group]
      exact inv_mem k.2
    · rw [← γ.out_eq']
      exact QuotientGroup.eq.2 (mem_KGL.2 hγ.2)
  · rw [heckeVec_apply hK (Tj_mem_hecke hp j), Tj_eq h0,
      finsum_eq_sum_of_support_subset (s := hf.toFinset) _ fun γ hγ => by
        rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hγ]
    have e : ∀ γ ∈ hf.toFinset, dosetInd ℂ (KGL v m) α γ.out * ρ γ.out Φ y =
        ((((qV K v : ℝ)⁻¹ ^ j) ^ s : ℝ) : ℂ) * if Q γ.out then 1 else 0 := fun γ hγ => by
      obtain ⟨a, ha, b, hb, e⟩ := (hR γ).1 hγ
      obtain ⟨u, hu⟩ := (hk_tor h0 hj).2.2
      rw [dosetInd_of_mem ⟨a, ha, b, hb, e⟩, one_mul, hQ]
      congr 1
      rw [e, wt_mul, wt_mul, wt_of_mem _ ha, wt_of_mem _ hb, one_mul, mul_one, wt, hu, map_mul,
        absV_mul, absV_unit, mul_one, map_pow, absV_pow]
      exact congrArg (fun t : ℝ => (((t ^ j) ^ s : ℝ) : ℂ)) (absV_unif hp)
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_boole,
      Nat.subtype_card (hf.toFinset.filter fun γ => Q γ.out) (by simp)]

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
