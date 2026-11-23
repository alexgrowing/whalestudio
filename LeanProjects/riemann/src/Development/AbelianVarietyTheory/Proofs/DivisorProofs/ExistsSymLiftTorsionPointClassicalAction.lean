import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEntireMulEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnTheta
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.InVVwIffOfNotTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.SymLiftCl

open GlobalTheory.ThetaFn GlobalTheory.SymLiftFrame GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

variable {g : ℕ}

theorem cv_dot (M N : Fin g → ℤ) : cv N ⬝ᵥ cv M = ((N ⬝ᵥ M : ℤ) : ℂ) := by
  simp [cv, dotProduct]

theorem half_dot {a : Fin g → ℂ} (ha : Half a) (M : Fin g → ℤ) : ∃ n : ℤ, 2 * (a ⬝ᵥ cv M) = n := by
  have h : ∀ i, ∃ e : ℤ, 2 * a i = e := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose e he using h
  refine ⟨e ⬝ᵥ M, ?_⟩
  simp only [dotProduct, cv, Finset.mul_sum, Int.cast_sum, Int.cast_mul, ← he, _root_.mul_assoc]

theorem perV_neg (τ : Matrix (Fin g) (Fin g) ℂ) (M N : Fin g → ℤ) : perV τ (-M) (-N) = -perV τ M N := by
  have h : ∀ K : Fin g → ℤ, cv (-K) = -cv K := fun K => funext fun i => by simp [cv]
  rw [perV, perV, h, h, Matrix.mulVec_neg, neg_add]

theorem dot_symm {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (v w : Fin g → ℂ) : v ⬝ᵥ τ *ᵥ w = w ⬝ᵥ τ *ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs.eq, dotProduct_comm]

theorem exp_eq_of_int {s t : ℂ} (n : ℤ) (h : s = t + n * (2 * Real.pi * Complex.I)) : Complex.exp s = Complex.exp t := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {u : HolUnif A L g}

theorem const_of_periodic {r : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ r) (h0 : ∀ z, r z ≠ 0)
    (hp : ∀ l ∈ u.Λ, ∀ z, r (z + l) = r z) (z : Fin g → ℂ) : r z = r 0 := by
  haveI := u.discrete
  refine (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 (fun _ => 1) r Matrix.isHermitian_zero
    (fun _ => norm_one) hd h0 (fun l z => ?_)).2.2 z
  rw [hp l l.2]
  simp [hermForm]

variable {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T}

def Reads (u : HolUnif A L g) (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) {m : T ⊗ A ⟶ A} {k : ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![k, -k])) (w : (Fin g → ℂ) → Fin g → ℂ)
    (r : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) → ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) →
    valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val * u.fr (j 1) (w z) ^ k =
      r z * u.fr (j 0) z ^ k

theorem Reads.period (hL : L.IsLB) {m : T ⊗ A ⟶ A} {k : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![k, -k])} {w : (Fin g → ℂ) → Fin g → ℂ}
    {r : (Fin g → ℂ) → ℂ} (h : Reads u p α w r) {z l l' : Fin g → ℂ} (hl : l ∈ u.Λ) (hl' : l' ∈ u.Λ)
    (hw : w (z + l) = w z + l') {s t : ℂ}
    (h0 : ∀ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = Complex.exp s * u.fr i (z + l))
    (h1 : ∀ i, ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U i → u.fr i (w z) = Complex.exp t * u.fr i (w z + l')) :
    r (z + l) = Complex.exp (k * s - k * t) * r z := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (w z)
  have e1 := h ![i, i'] z hi hi'
  have e2 := h ![i, i'] (z + l) (by rw [ex_add_period u _ _ hl]; exact hi)
    (by rw [hw, ex_add_period u _ _ hl']; exact hi')
  have n0 : u.fr i (z + l) ≠ 0 := u.fr_ne _ _ (by rw [ex_add_period u _ _ hl]; exact hi)
  rw [exAt_add_period u p z l hl, hw] at e2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
  rw [h0 i hi, h1 i' hi', mul_zpow, mul_zpow, ← Complex.exp_int_mul, ← Complex.exp_int_mul] at e1
  rw [Complex.exp_sub, div_mul_eq_mul_div, eq_div_iff (Complex.exp_ne_zero _)]
  refine mul_right_cancel₀ (zpow_ne_zero k n0) ?_
  linear_combination e1 - Complex.exp (k * t) * e2

variable {J : (Sp ℂ ⟶ A.left) → L.ι}

theorem Reads.cval (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {m : T ⊗ A ⟶ A} {k : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![k, -k])} {w : (Fin g → ℂ) → Fin g → ℂ}
    {r : (Fin g → ℂ) → ℂ} (h : Reads u p α w r) (hw : ∀ z, exAt u p z ≫ m.left = (u.ex (w z)).left) (z : Fin g → ℂ) :
    cval (L := L) α (exAt u p z) J * u.fr (J (u.ex (w z)).left) (w z) ^ k = r z * u.fr (J (u.ex z).left) z ^ k := by
  rw [cval_two α (hw z)]
  exact h ![J (u.ex z).left, J (u.ex (w z)).left] z (hJ _) (hJ _)

variable {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {r : (Fin g → ℂ) → ℂ}

theorem prod_mul_eq_one (hL : L.IsLB) (hx : p ≫ Θ.pt = u.ex x) (hr : Reads u p Θ.φ (fun z => z + x) r) {n : ℕ}
    (hl : (n : ℂ) • x ∈ u.Λ) {e : ℂ}
    (he : ∀ i, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i → u.fr i 0 = e * u.fr i (0 + (n : ℂ) • x))
    (h : LB.Gen.Corr L _ _ _ _ (powGen A L k Θ n) (LB.oneGen L)) :
    (∏ i ∈ Finset.range n, r ((i : ℂ) • x)) * e ^ k = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have ht : ∀ i : ℕ, exAt u p 0 ≫ (translT A (Θ.pt ^ i)).left = exAt u p ((i : ℂ) • x) := fun i => by
    rw [exAt_translT u (x := (i : ℂ) • x) (by rw [MonObj.comp_pow, hx, ex_natCast_smul]), zero_add]
  have key : ∀ m : ℕ, (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) *
      u.fr (J (u.ex ((m : ℂ) • x)).left) ((m : ℂ) • x) ^ k =
      (∏ i ∈ Finset.range m, r ((i : ℂ) • x)) * u.fr (J (u.ex 0).left) 0 ^ k := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      have e := hr.cval hJ (exAt_translPt u hx) ((m : ℂ) • x)
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, _root_.mul_assoc]
      refine (congrArg (_ * ·) e).trans ?_
      linear_combination r ((m : ℂ) • x) * ih
  have h1 := (cval_powGen hJ Θ n (exAt u p 0)).symm.trans (cval_corr_one hJ h _)
  simp only [ht] at h1
  have h2 := key n
  have h4 : u.ex ((n : ℂ) • x) = u.ex 0 := by rw [← ex_add_period u 0 _ hl, zero_add]
  have h6 : u.fr (J (u.ex 0).left) ((n : ℂ) • x) ≠ 0 := u.fr_ne _ _ (by rw [h4]; exact hJ _)
  rw [h1, h4, he _ (hJ _), zero_add, mul_zpow] at h2
  refine mul_right_cancel₀ (zpow_ne_zero k h6) ?_
  linear_combination -h2

theorem exAt_neg (z : Fin g → ℂ) : exAt u p z ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (u.ex (-z)).left := by
  rw [Over.comp_left, ← Category.assoc, exAt_snd, ex_neg_left]

theorem mul_eq_one_of_sym (hL : L.IsLB) (hx : p ≫ Θ.pt = u.ex x) (hr : Reads u p Θ.φ (fun z => z + x) r)
    {nu : LB.Gen (negLB A L k T)} {d : ℂ} (hν : Reads u p nu (fun z => -z) fun _ => d)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k Θ nu) (LB.oneGen L)) : r (-x) * r 0 = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hneg : ∀ z, u.ex (-z) = (u.ex z)⁻¹ := fun z => by
    rw [eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel, ex_zero]
  have t1 : exAt u p 0 ≫ (translT A Θ.pt⁻¹).left = exAt u p (-x) := by
    rw [exAt_translT u (x := -x) (by rw [GrpObj.comp_inv, hx, hneg]), zero_add]
  have t2 : exAt u p 0 ≫ (negT A T).left = exAt u p 0 := by
    refine (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left ?_)
    rw [negT, comp_lift, lift_fst, lift_snd_assoc, ← Hom.inv_def, ← hneg, neg_zero]
  have h1 := (cval_symGen hJ Θ nu (exAt u p 0)).symm.trans (cval_corr_one hJ h (exAt u p 0))
  rw [t1, t2] at h1
  have e1 : cval (L := L) Θ.φ (exAt u p (-x)) J * u.fr (J (u.ex (-x + x)).left) (-x + x) ^ k = _ :=
    hr.cval hJ (exAt_translPt u hx) (-x)
  have e2 : cval (L := L) Θ.φ (exAt u p 0) J * u.fr (J (u.ex (0 + x)).left) (0 + x) ^ k = _ :=
    hr.cval hJ (exAt_translPt u hx) 0
  have e3 : cval (L := L) nu (exAt u p 0) J * u.fr (J (u.ex (-0)).left) (-0) ^ k = d * _ := hν.cval hJ exAt_neg 0
  have e4 : cval (L := L) nu (exAt u p (-x)) J * u.fr (J (u.ex (- -x)).left) (- -x) ^ k = d * _ :=
    hν.cval hJ exAt_neg (-x)
  rw [neg_add_cancel] at e1
  rw [zero_add] at e2
  rw [neg_zero] at e3
  rw [neg_neg] at e4
  have n0 := zpow_ne_zero k (u.fr_ne _ _ (hJ (u.ex 0).left))
  have n1 := zpow_ne_zero k (u.fr_ne _ _ (hJ (u.ex (-x)).left))
  have n2 : cval (L := L) nu (exAt u p (-x)) J ≠ 0 := cval_ne_zero hJ _ _
  have n3 : cval (L := L) nu (exAt u p 0) J ≠ 0 := cval_ne_zero hJ _ _
  have e6 := mul_right_cancel₀ n0 e3
  rw [e6] at h1 n3
  generalize cval (L := L) nu (exAt u p (-x)) J = v at *
  rw [← _root_.mul_assoc, mul_inv_eq_one₀ n2] at h1
  refine mul_right_cancel₀ (mul_ne_zero n3 (mul_ne_zero n0 n1)) ?_
  linear_combination u.fr (J (u.ex 0).left) 0 ^ k * e4 +
    u.fr (J (u.ex 0).left) 0 ^ k * u.fr (J (u.ex x).left) x ^ k * h1 -
    d * (cval (L := L) Θ.φ (exAt u p 0) J * u.fr (J (u.ex x).left) x ^ k) * e1 -
    d * (r (-x) * u.fr (J (u.ex (-x)).left) (-x) ^ k) * e2

theorem Reads.act (hL : L.IsLB) (hx : p ≫ Θ.pt = u.ex x) (hr : Reads u p Θ.φ (fun z => z + x) r)
    {s s' : LB.Sec (LPow A L k T)} (hs : IsActOf A L k Θ s s') {θ : (Fin g → ℂ) → ℂ} (hθ : IsFnAt u p k s θ) :
    IsFnAt u p k s' fun z => r z * θ (z + x) := by
  have hθ' := isFnAt_fnAt u p hL k s'
  convert hθ' using 1
  funext z
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (z + x)
  have hj := (exAt_mem_twist_chart_iff u p (exAt_translPt u hx z) ![i, i']).2 ⟨hi, hi'⟩
  have e := hθ.twistPull hθ' hs (exAt_translT u hx z) ![i, i'] hj
  have e' := hr ![i, i'] z hi hi'
  refine mul_right_cancel₀ (zpow_ne_zero k (u.fr_ne (![i, i'] 0) _ hi)) ?_
  linear_combination -e - θ (z + x) * e'

theorem fnT_iff {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))))
    (f : (Fin g → ℂ) → ℂ) : FnT u k t f ↔ IsFnAt u basePt k t f := by
  constructor
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    rw [zpow_natCast]
    exact h i z ((exAt_mem_chart_iff u basePt _ _ z).1 hj)
  · intro h i z hi
    have := h (fun _ => i) z ((exAt_mem_chart_iff u basePt _ _ z).2 hi)
    rw [zpow_natCast] at this
    exact this

variable {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}

theorem exists_reads_neg (hL : L.IsLB) (ha : Half a) (hb : Half b) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ M N, z = perV τ M N)
    (hfr : ∀ M N i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N))
    {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) : ∃ d : ℂ, Reads u p nu (fun z => -z) fun _ => d := by
  obtain ⟨r, hd, h0, hr⟩ := exists_entire_twist u p hL (a := k) (b := k) nu hnu (w := fun z => -z) (by fun_prop) exAt_neg
  have hc := const_of_periodic (u := u) hd h0 fun l hl z => by
    obtain ⟨M, N, rfl⟩ := (hΛ l).1 hl
    rw [Reads.period hL (w := fun z => -z) hr hl (l' := perV τ (-M) (-N)) ((hΛ _).2 ⟨_, _, rfl⟩)
      (by rw [perV_neg, neg_add]) (hfr M N · z) (hfr (-M) (-N) · (-z))]
    obtain ⟨n, hn⟩ := half_dot ha M
    obtain ⟨n', hn'⟩ := half_dot hb N
    have h : ∀ K : Fin g → ℤ, cv (-K) = -cv K := fun K => funext fun i => by simp [cv]
    rw [exp_eq_of_int (t := 0) (k * (n - n')), Complex.exp_zero, _root_.one_mul]
    simp only [h, dotProduct_neg, neg_dotProduct, Matrix.mulVec_neg, neg_neg]
    push_cast
    rw [← hn, ← hn']
    ring
  exact ⟨r 0, fun j z h1 h2 => (hr j z h1 h2).trans (by rw [hc])⟩

theorem exists_reads_transl (hL : L.IsLB) (hs : τ.IsSymm) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ M N, z = perV τ M N)
    (hfr : ∀ M N i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N))
    (hx : p ≫ Θ.pt = u.ex x) {M N : Fin g → ℤ} (hk : (k : ℂ) • x = perV τ M N) :
    ∃ c : ℂ, Reads u p Θ.φ (fun z => z + x) fun z => c * Complex.exp (2 * Real.pi * Complex.I * (cv N ⬝ᵥ z)) := by
  obtain ⟨r, hd, h0, hr⟩ := exists_entire_twist u p hL Θ.φ Θ.isGen (w := fun z => z + x) (by fun_prop) (exAt_translPt u hx)
  have hd' : Differentiable ℂ fun z : Fin g → ℂ => Complex.exp (-(2 * Real.pi * Complex.I * (cv N ⬝ᵥ z))) := by
    unfold dotProduct
    fun_prop
  have hc := const_of_periodic (u := u) (r := fun z => r z * Complex.exp (-(2 * Real.pi * Complex.I * (cv N ⬝ᵥ z))))
    (hd.mul hd') (fun z => mul_ne_zero (h0 z) (Complex.exp_ne_zero _)) fun l hl z => by
    obtain ⟨M', N', rfl⟩ := (hΛ l).1 hl
    rw [Reads.period hL (w := fun z => z + x) hr hl hl (add_right_comm _ _ _) (hfr M' N' · z) (hfr M' N' · (z + x)),
      _root_.mul_comm _ (r z), _root_.mul_assoc, ← Complex.exp_add]
    refine congrArg _ (exp_eq_of_int (N' ⬝ᵥ M - N ⬝ᵥ M') ?_)
    have e : (k : ℂ) * (cv N' ⬝ᵥ x) = cv N' ⬝ᵥ cv M + cv N ⬝ᵥ τ *ᵥ cv N' := by
      rw [← smul_eq_mul, ← dotProduct_smul, hk, perV, dotProduct_add, dot_symm hs]
    rw [Int.cast_sub, ← cv_dot, ← cv_dot]
    simp only [perV, dotProduct_add]
    linear_combination (2 * Real.pi * Complex.I) * e
  refine ⟨r 0, fun j z h1 h2 => (hr j z h1 h2).trans (congrArg (· * _) ?_)⟩
  have e := hc z
  simp only [dotProduct_zero, mul_zero, neg_zero, Complex.exp_zero, _root_.mul_one] at e
  beta_reduce
  rw [← e, _root_.mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, _root_.mul_one]

theorem prod_exp (c s : ℂ) (n : ℕ) :
    ∏ i ∈ Finset.range n, c * Complex.exp (2 * (i * s)) = c ^ n * Complex.exp (n * (n - 1) * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, _root_.mul_mul_mul_comm, ← pow_succ, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem eq_exp_of_odd {c s t : ℂ} {j : ℕ} (h1 : c ^ 2 * Complex.exp (2 * s) = 1)
    (h2 : c ^ (2 * j + 1) * Complex.exp t = 1) : c = Complex.exp (2 * j * s - t) := by
  have h3 : (c ^ 2 * Complex.exp (2 * s)) ^ j = 1 := by rw [h1, one_pow]
  rw [mul_pow, ← Complex.exp_nat_mul, ← pow_mul, show (j : ℂ) * (2 * s) = 2 * j * s by ring] at h3
  rw [Complex.exp_sub, eq_div_iff (Complex.exp_ne_zero _)]
  linear_combination Complex.exp (2 * j * s) * h2 - c * Complex.exp t * h3

end GlobalTheory.MBLow.Cl.SymLiftCl

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.ThetaFn GlobalTheory.CubeValues SymLiftCl in

theorem exists_symLift_act_classical : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ m : ℕ, Odd m → ∀ (M N : Fin g → ℤ) (pt : (baseOver (Sp ℂ)) ⟶ x.P.A), pt.left = (u.ex (((m : ℂ) ^ 2)⁻¹ • perV τ M N)).left → ∃ U : ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)), SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) pt U ∧ ∀ s f, FnT u (m ^ 2) s f → ∃ t, IsActOf x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) U s t ∧ FnT u (m ^ 2) t fun z => trFac τ a b m M N z * f (z + ((m : ℂ) ^ 2)⁻¹ • perV τ M N) := by
  intro g x hg u τ a b c W hNF m hm M N pt hpt
  have hfr := frame_eq_autV_mul g x hg u τ a b c W hNF
  obtain ⟨hs, -, ha, hb, -, hΛ, -⟩ := hNF
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  set y : Fin g → ℂ := ((m : ℂ) ^ 2)⁻¹ • perV τ M N with hy
  have hk : ((m ^ 2 : ℕ) : ℂ) • y = perV τ M N := by
    rw [hy, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero 2 hm0), one_smul]
  have hl : ((m ^ 2 : ℕ) : ℂ) • y ∈ u.Λ := (hΛ _).2 ⟨M, N, hk⟩
  have hp : basePt ≫ pt = u.ex y := Over.OverMorphism.ext ((Category.id_comp _).trans hpt)
  have htor : pt ^ (m ^ 2) = 1 := by
    rw [← cancel_epi basePt, MonObj.comp_pow, MonObj.comp_one, hp, ← ex_natCast_smul]
    exact (u.ker _).2 hl
  obtain ⟨U, hU⟩ := GlobalTheory.WeightProbe.exists_symLift_top x.P (N := m ^ 2) hm.pow pt htor
  have hx : basePt ≫ U.pt = u.ex y := hU.pt_eq ▸ hp
  obtain ⟨ξ, hξ⟩ := exists_reads_transl x.P.isLB hs hΛ hfr hx (M := M) (N := N) (by rw [Int.cast_natCast]; exact hk)
  obtain ⟨nu, hnu, hsym⟩ := hU.sym
  obtain ⟨d, hd⟩ := exists_reads_neg (p := basePt) x.P.isLB ha hb hΛ hfr hnu
  have h1 := mul_eq_one_of_sym x.P.isLB hx hξ hd hsym
  have h2 := prod_mul_eq_one x.P.isLB hx hξ hl (e := autV τ a b M N 0) (fun i hi => by rw [hk]; exact hfr M N i 0 hi) hU.pow_eq
  have hσ : ((m : ℂ) ^ 2) * (cv N ⬝ᵥ y) = cv N ⬝ᵥ cv M + cv N ⬝ᵥ τ *ᵥ cv N := by
    rw [← smul_eq_mul, ← dotProduct_smul, ← Nat.cast_pow, hk, perV, dotProduct_add]
  obtain ⟨j, hj⟩ : Odd (m ^ 2) := hm.pow
  have hj' : (m : ℂ) ^ 2 = 2 * j + 1 := by exact_mod_cast hj
  have h1' : ξ ^ 2 * Complex.exp (2 * (-(Real.pi * Complex.I * (cv N ⬝ᵥ y)))) = 1 := by
    rw [← h1]
    simp only [dotProduct_zero, mul_zero, Complex.exp_zero, dotProduct_neg]
    rw [show 2 * (-(Real.pi * Complex.I * (cv N ⬝ᵥ y))) = 2 * Real.pi * Complex.I * -(cv N ⬝ᵥ y) by ring]
    ring
  simp only [dotProduct_smul, smul_eq_mul, show ∀ i s : ℂ, 2 * Real.pi * Complex.I * (i * s) =
    2 * (i * (Real.pi * Complex.I * s)) from fun i s => by ring] at h2
  rw [prod_exp, zpow_natCast, autV, ← Complex.exp_nat_mul, _root_.mul_assoc, ← Complex.exp_add, hj] at h2
  have h3 := eq_exp_of_odd h1' h2
  refine ⟨U, hU, fun s f hf => ?_⟩
  obtain ⟨t, ht⟩ := GlobalTheory.ThetaPtExist.exists_isTwistPull x.P.isLB (translT x.P.A U.pt) (translPt x.P.A U.pt) (lift_snd _ _)
    _ _ U.φ U.isGen s
  refine ⟨t, ht, (fnT_iff u _ t _).2 ?_⟩
  convert hξ.act x.P.isLB hx ht ((fnT_iff u _ s f).1 hf) using 3 with z
  obtain ⟨n, hn⟩ := half_dot ha M
  obtain ⟨n', hn'⟩ := half_dot hb N
  rw [h3, ← Complex.exp_add, trFac]
  refine exp_eq_of_int ((j + 1) * ((N ⬝ᵥ M) + n - n')) ?_
  have hy' : cv N ⬝ᵥ cv M / (m : ℂ) ^ 2 + cv N ⬝ᵥ τ *ᵥ cv N / (m : ℂ) ^ 2 = cv N ⬝ᵥ y := by
    rw [← add_div, ← hσ, mul_div_cancel_left₀ _ (pow_ne_zero 2 hm0)]
  rw [hj'] at hσ
  rw [dotProduct_zero, mul_div_assoc, mul_div_assoc]
  push_cast
  rw [← cv_dot, ← hn, ← hn']
  linear_combination (Real.pi * Complex.I) * hy' + (Real.pi * Complex.I * (2 * j + 1)) * hσ

end GlobalTheory.MBLow.Cl

end
