import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverseStatement
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.LatticePair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsInt (A : GL (Fin n) k) : Prop := ∀ i j, A.1 i j ∈ 𝒪[k]

theorem isInt_mul {A B : GL (Fin n) k} (hA : IsInt A) (hB : IsInt B) : IsInt (A * B) := fun i j => by
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isInt_mul_KO_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (A * κ) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul hA h.1⟩
  have := isInt_mul hA h.2
  rwa [mul_inv_cancel_right] at this

theorem isInt_KO_mul_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (κ * A) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul h.1 hA⟩
  have := isInt_mul h.2 hA
  rwa [inv_mul_cancel_left] at this

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨u, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det u : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem ord_det_mul (a b : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det (a * b)) =
    ord k (Matrix.GeneralLinearGroup.det a) + ord k (Matrix.GeneralLinearGroup.det b) := by
  rw [map_mul, ord_mul]

theorem ord_det_inv (a : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det a⁻¹) =
    -ord k (Matrix.GeneralLinearGroup.det a) := by
  have := ord_det_mul a a⁻¹
  rw [mul_inv_cancel, map_one, ord_eq_zero (by simp)] at this
  omega

theorem valuation_det_le_one {A : GL (Fin n) k} (hA : IsInt A) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := by
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨A.1 i j, hA i j⟩
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = A.1 := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← hB, ← RingHom.map_det]
  exact B.det.2

theorem ord_nonneg_of_le_one {x : kˣ} (hx : valuation k (x : k) ≤ 1) : 0 ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  have h1 : φ (valuation k (x : k)) ≤ φ 1 := φ.strictMono.monotone hx
  rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  show 0 ≤ -WithZero.log (φ (valuation k (x : k)))
  omega

theorem ord_det_torusElt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) :
    ord k (Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e)) = ∑ i, e i := by
  have h1 : Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_torusElt, Matrix.det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have := map_zpow o ϖ (∑ i, e i)
  rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
    smul_eq_mul, mul_one, ← h1] at this
  exact this

theorem isInt_and_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (A : GL (Fin n) k)
    (e : Fin n → ℤ) : IsInt A ∧ IsInt (A * torusElt k (Fin n) ϖ e) ↔
      IsInt (A * torusElt k (Fin n) ϖ fun i => min (e i) 0) := by
  have hle : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have hpow : ∀ m : ℤ, 0 ≤ m → (ϖ : k) ^ m ∈ 𝒪[k] := fun m hm => by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact pow_mem hle m
  have hent : ∀ (f : Fin n → ℤ) i j, (A * torusElt k (Fin n) ϖ f).1 i j = A.1 i j * (ϖ : k) ^ f j :=
    fun f i j => by rw [Units.val_mul, val_torusElt, Matrix.mul_diagonal]
  have key : ∀ (x : k) (m : ℤ), (x ∈ 𝒪[k] ∧ x * (ϖ : k) ^ m ∈ 𝒪[k]) ↔ x * (ϖ : k) ^ min m 0 ∈ 𝒪[k] := by
    intro x m
    have hz : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rcases le_total m 0 with h | h
    · rw [min_eq_left h]
      refine ⟨And.right, fun h2 => ⟨?_, h2⟩⟩
      have : x = x * (ϖ : k) ^ m * (ϖ : k) ^ (-m) := by
        rw [mul_assoc, ← zpow_add₀ hz, add_neg_cancel, zpow_zero, mul_one]
      rw [this]
      exact mul_mem h2 (hpow _ (by omega))
    · rw [min_eq_right h, zpow_zero, mul_one]
      exact ⟨And.left, fun h2 => ⟨h2, mul_mem h2 (hpow _ h)⟩⟩
  simp only [IsInt, hent]
  constructor
  · rintro ⟨h1, h2⟩ i j
    exact (key _ _).1 ⟨h1 i j, h2 i j⟩
  · intro h
    exact ⟨fun i j => ((key _ _).2 (h i j)).1, fun i j => ((key _ _).2 (h i j)).2⟩

theorem out_eq_mul {r : GL (Fin n) k} {c : GL (Fin n) k ⧸ KO k (Fin n)}
    (h : (r : GL (Fin n) k ⧸ KO k (Fin n)) = c) : ∃ κ ∈ KO k (Fin n), c.out = r * κ := by
  subst h
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) r
  exact ⟨κ, κ.2, hκ⟩

theorem smul_out (u : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), (u • c).out = u * c.out * κ := by
  apply out_eq_mul
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem hasSum_pair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) (g : GL (Fin n) k)
    (hg : g ∈ cell k (Fin n) ϖ e) (X : ℂ) (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) :
    HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat +
        (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat))
      (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  obtain ⟨x, hx, y, hy, hgxy⟩ := DoubleCoset.mem_doubleCoset.1 hg
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = x * torusElt k (Fin n) ϖ fun i => min (e i) 0 := ⟨_, rfl⟩
  have hP : ∀ h : GL (Fin n) k, (IsInt h⁻¹ ∧ IsInt (h⁻¹ * g)) ↔ IsInt (h⁻¹ * u) := fun h => by
    rw [hgxy, hu, ← mul_assoc, ← mul_assoc, ← mul_assoc, isInt_mul_KO_iff hy, ← isInt_and_mul_torus_iff hϖ,
      isInt_mul_KO_iff hx]
  let E : {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]} ≃
      {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    (MulAction.toPerm u).subtypeEquiv fun c => by
      obtain ⟨κ, hκ, h⟩ := smul_out u c
      refine Iff.trans ?_ (hP (u • c).out).symm
      have : (u * c.out * κ)⁻¹ * u = κ⁻¹ * c.out⁻¹ := by group
      rw [h, this, isInt_KO_mul_iff (inv_mem hκ)]
      rfl
  have hN := (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n (fun _ => 1) (fun _ => 1) (isBorelSph_one k) (fun _ => one_ne_zero) (X ^ 2)
    fun i => by simpa only [inv_one, mul_one] using hX i).mul_left (X ^ (∑ i, |e i|).toNat)
  simp only [inv_one, mul_one] at hN
  rw [← E.hasSum_iff]
  refine (congrArg (HasSum · _) (funext fun c => ?_)).mpr hN
  obtain ⟨κ, hκ, h⟩ := smul_out u c.1
  have hE : (E c).1.out = u * c.1.out * κ := h
  have hj := ord_nonneg_of_le_one (valuation_det_le_one (A := c.1.out⁻¹) c.2)
  have habs : ∑ i, |e i| = ∑ i, e i - 2 * ∑ i, min (e i) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  have h1 : ∑ i, min (e i) 0 ≤ 0 := Finset.sum_nonpos fun i _ => min_le_right _ _
  have h2 : ∑ i, min (e i) 0 ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => min_le_left _ _
  have hou : ord k (Matrix.GeneralLinearGroup.det u) = ∑ i, min (e i) 0 := by
    rw [hu, ord_det_mul, ord_det_of_mem_KO hx, ord_det_torusElt hϖ, zero_add]
  have hog : ord k (Matrix.GeneralLinearGroup.det g) = ∑ i, e i := by
    rw [hgxy, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hx, ord_det_of_mem_KO hy, ord_det_torusElt hϖ,
      zero_add, add_zero]
  rw [ord_det_inv] at hj
  simp only [Function.comp_apply]
  rw [ord_det_mul, ord_det_inv, hE, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hκ, hou, hog,
    ← pow_mul, ← pow_add, habs]
  congr 1
  omega

end GlobalTheory.LatticePair
