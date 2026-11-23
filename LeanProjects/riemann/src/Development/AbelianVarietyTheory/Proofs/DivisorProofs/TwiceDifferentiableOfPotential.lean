import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O.InterpFam

section Gen

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

def TwiceDifferentiableInChart (A : FinHolAtlas e X) (P : LocPot X) (j : Fin A.n) (y : Fin e → ℂ) : Prop :=
  ContDiffAt ℝ 2 (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y

theorem twice_differentiable_of_potential {P : LocPot X} (hP : IsPotential A P) {j : Fin A.n} {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : TwiceDifferentiableInChart A P j y :=
  (contDiffAt_of_isPotential A P hP _ j ⟨hy, P.mem_U _⟩).of_le (by norm_cast)

theorem twice_differentiable_off_set {Z : Set X} (hZ : IsClosed Z) {u : X → ℝ} (hu : A.SmoothOn Zᶜ u) {j : Fin A.n} {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyZ : (A.chart j).symm y ∉ Z) : TwiceDifferentiableInChart A (LocPot.ofFun u) j y :=
  ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds ⟨hy, hyZ⟩)).of_le
    (by norm_cast)

theorem TwiceDifferentiableInChart.add {P Q : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (hP : TwiceDifferentiableInChart A P j y) (hQ : TwiceDifferentiableInChart A Q j y) :
    TwiceDifferentiableInChart A (P + Q) j y := ContDiffAt.add hP hQ

theorem TwiceDifferentiableInChart.rsmul {P : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (hP : TwiceDifferentiableInChart A P j y) (c : ℝ) :
    TwiceDifferentiableInChart A (P.rsmul c) j y := ContDiffAt.mul contDiffAt_const hP

theorem lv_add {P Q : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (hP : TwiceDifferentiableInChart A P j y) (hQ : TwiceDifferentiableInChart A Q j y)
    (w : Fin e → ℂ) : leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w := by
  have h := levi_add_smul 1 hP hQ w
  simp only [one_mul] at h
  exact h

theorem lv_rsmul {P : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (hP : TwiceDifferentiableInChart A P j y) (c : ℝ) (w : Fin e → ℂ) :
    leviAt A (P.rsmul c) j y w = c * leviAt A P j y w :=
  ReciprocityTheory.AnForm.P.TailChernBound.levi_smul' c hP w

theorem lv_zero (j : Fin A.n) (y w : Fin e → ℂ) : leviAt A (LocPot.ofFun fun _ => 0) j y w = 0 := by
  unfold leviAt
  have he : (LocPot.ofFun (X := X) fun _ => 0).φ ((A.chart j).symm y) ∘ (A.chart j).symm = fun _ => 0 := rfl
  rw [he]
  simp [levi]

theorem lv_fun {u p : X → ℝ} {j : Fin A.n} {y : Fin e → ℂ} (hu : TwiceDifferentiableInChart A (LocPot.ofFun u) j y)
    (hp : TwiceDifferentiableInChart A (LocPot.ofFun p) j y) (c : ℝ) (w : Fin e → ℂ) :
    leviAt A (LocPot.ofFun fun x => u x + c * p x) j y w =
      leviAt A (LocPot.ofFun u) j y w + c * leviAt A (LocPot.ofFun p) j y w :=
  levi_add_smul c hu hp w

theorem isPsh_of_lv {P : LocPot X} (hP : IsPotential A P)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, 0 ≤ leviAt A P j y w) : IsPsh A P := by
  intro x j y hy w
  have h1 := ReciprocityTheory.AnForm.P.TailChernBound.base_change A P hP x ((A.chart j).symm y) ((A.chart j).symm y) j
    ((A.chart j).map_target hy.1) hy.2 (P.mem_U _) w
  rw [(A.chart j).right_inv hy.1] at h1
  rw [h1]
  exact h j y hy.1 w

theorem lv_nonneg {P : LocPot X} (h : IsPsh A P) {j : Fin A.n} {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (w : Fin e → ℂ) : 0 ≤ leviAt A P j y w := h _ j y ⟨hy, P.mem_U _⟩ w

theorem lv_pos_nonneg {P : LocPot X} (h : IsPosPot A P) {j : Fin A.n} {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : 0 ≤ leviAt A P j y w := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact (levi_zero _ _).ge
  · exact (h _ j y ⟨hy, P.mem_U _⟩ w hw).le

def LvBd (A : FinHolAtlas e X) (Om : LocPot X) (K : ℝ) (P : LocPot X) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, |leviAt A P j y w| ≤ K * leviAt A Om j y w

theorem LvBd.mono {Om P : LocPot X} {K K' : ℝ} (h : LvBd A Om K P) (hpos : IsPosPot A Om) (hK : K ≤ K') :
    LvBd A Om K' P := fun j y hy w =>
  (h j y hy w).trans (mul_le_mul_of_nonneg_right hK (lv_pos_nonneg hpos hy w))

theorem exists_lvBd [CompactSpace X] {Om P : LocPot X} (hOm : IsPotential A Om) (hpos : IsPosPot A Om)
    (hP : IsPotential A P) : ∃ K : ℝ, 0 ≤ K ∧ LvBd A Om K P := by
  obtain ⟨C, hC, h⟩ := ReciprocityTheory.AnForm.P.TailChernBound.exists_levi_nonneg_chern_bound A Om P hOm hpos hP
  refine ⟨C, hC, fun j y hy w => ?_⟩
  have key : ∀ ε : ℝ, (∀ a : ℝ, -|a| ≤ ε * a) → 0 ≤ C * leviAt A Om j y w + ε * leviAt A P j y w := by
    intro ε hε
    have h1 := h ε hε ((A.chart j).symm y) j y ⟨hy, Om.mem_U _, P.mem_U _⟩ w
    have h2 := ReciprocityTheory.AnForm.P.TailChernBound.levi_lin C ε (twice_differentiable_of_potential hOm hy) (twice_differentiable_of_potential hP hy) w
    exact h1.trans_eq h2
  have h1 := key 1 fun a => by linarith [neg_abs_le a]
  have h2 := key (-1) fun a => by linarith [le_abs_self a]
  rw [abs_le]
  constructor <;> linarith

theorem LvBd.psh {Om P : LocPot X} {K : ℝ} (h : LvBd A Om K P) (hOm : IsPotential A Om) (hP : IsPotential A P) :
    IsPsh A (Om.rsmul K + P) ∧ IsPsh A (Om.rsmul K + P.rsmul (-1)) := by
  have hK := isPotentialRsmul A K _ hOm
  have hN := isPotentialRsmul A (-1) _ hP
  refine ⟨isPsh_of_lv (isPotentialAdd A _ _ hK hP) fun j y hy w => ?_,
    isPsh_of_lv (isPotentialAdd A _ _ hK hN) fun j y hy w => ?_⟩
  · rw [lv_add (twice_differentiable_of_potential hK hy) (twice_differentiable_of_potential hP hy), lv_rsmul (twice_differentiable_of_potential hOm hy)]
    linarith [(abs_le.1 (h j y hy w)).1]
  · rw [lv_add (twice_differentiable_of_potential hK hy) (twice_differentiable_of_potential hN hy), lv_rsmul (twice_differentiable_of_potential hOm hy), lv_rsmul (twice_differentiable_of_potential hP hy)]
    linarith [(abs_le.1 (h j y hy w)).2]

theorem abs_linear_le {ι : Type} [Fintype ι] {N : ℕ} (f : (ι → Fin N → ℝ) →ₗ[ℝ] ℝ) (u : ι → Fin N → ℝ) :
    |f u| ≤ ‖u‖ * ∑ τ, ∑ i, |f (Pi.single τ (Pi.single i 1))| := by
  have hu : u = ∑ τ, ∑ i, u τ i • (Pi.single τ (Pi.single i 1) : ι → Fin N → ℝ) := by
    funext τ i
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  conv_lhs => rw [hu]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)) (abs_nonneg _)

theorem exists_lvBd_lin [CompactSpace X] {ι : Type} [Fintype ι] {N : ℕ} {Om : LocPot X} (hOm : IsPotential A Om)
    (hpos : IsPosPot A Om) (th : (ι → Fin N → ℝ) → LocPot X) (hth : ∀ u, IsPotential A (th u))
    (hlin : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, IsLinearMap ℝ fun u => leviAt A (th u) j y w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, LvBd A Om (‖u‖ * K) (th u) := by
  choose K hK hb using fun (τ : ι) (i : Fin N) => exists_lvBd hOm hpos (hth (Pi.single τ (Pi.single i 1)))
  refine ⟨∑ τ, ∑ i, K τ i, Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => hK τ i, fun u j y hy w => ?_⟩
  refine (abs_linear_le (IsLinearMap.mk' _ (hlin j y hy w)) u).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [Finset.sum_mul]
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i j y hy w

theorem toBot_of_le {Z : Set X} {r u : X → ℝ} (hr : ∀ x, x ∉ Z → Real.exp 1 ≤ r x) (hb : ToBot Z fun x => -r x)
    {c : ℝ} (hc : 0 < c) (hu : ∀ x, x ∉ Z → u x ≤ -(c * Real.log (r x))) : ToBot Z u := by
  intro a
  refine (closure_mono ?_).trans (hb (Real.exp (a / c)))
  rintro x ⟨hx, hxa⟩
  refine ⟨hx, neg_le_neg ?_⟩
  have h0 : 0 < r x := (Real.exp_pos 1).trans_le (hr x hx)
  rw [← Real.log_le_iff_le_exp h0, le_div_iff₀ hc]
  linarith [hu x hx]

theorem one_le_log {Z : Set X} {r : X → ℝ} (hr : ∀ x, x ∉ Z → Real.exp 1 ≤ r x) {x : X} (hx : x ∉ Z) :
    1 ≤ Real.log (r x) :=
  (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (hr x hx))).2 (hr x hx)

theorem comb_one [CompactSpace X] {Z : Set X} {r : X → ℝ} {Om : LocPot X} (hbd : IsBd A Z r Om)
    {a b : LocPot X} {p : X → ℝ} (ha : IsPotential A a) (hap : IsPsh A a) (hb : IsPoin A Z r b p)
    (K₀ C₁ C₂ : ℝ) (hK₀ : 0 ≤ K₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ K₁ : ℝ, ∀ K, K₁ ≤ K → ∀ (θ : LocPot X) (g : X → ℝ) (t : ℝ), IsPotential A θ → LvBd A Om K₀ θ → A.Smooth g →
      (∀ x, x ∉ Z → |g x| ≤ C₁ * Real.log (r x)) → t ≤ C₂ →
      PshOff A Z (θ + LocPot.ofFun g + (b + LocPot.ofFun p).rsmul t) → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Comb A Z r Om K (θ + a.rsmul s + LocPot.ofFun g) := by
  obtain ⟨hZ, -, hOm, hpos, -, hr, hbot, -⟩ := hbd
  obtain ⟨hbp, hps, ⟨c, Cp, hc, hpb⟩, hbe⟩ := hb
  obtain ⟨Ka, hKa, hba⟩ := exists_lvBd hOm hpos ha
  obtain ⟨Kb, hKb, hbb⟩ := exists_lvBd hOm hpos hbp
  obtain ⟨C', hC'⟩ : ∃ C', C' = C₂ + (C₁ + 1) / c := ⟨_, rfl⟩
  have hq : 0 ≤ (C₁ + 1) / c := by positivity
  have hC'0 : 0 ≤ C' := by linarith
  have hC'c : C₁ + 1 ≤ C' * c := by
    rw [hC', add_mul, div_mul_cancel₀ _ hc.ne']
    nlinarith
  have hA := abs_nonneg Cp
  have hA' := le_abs_self Cp
  have h1 := mul_nonneg hC'0 hKb
  have h2 := mul_nonneg hC'0 hA
  refine ⟨1 + C' + Ka + Kb + K₀ + C' * Kb + C₁ + C' * |Cp| + |Cp|, fun K hK θ g t hθ hθb hg hgb ht hpsh s hs => ?_⟩
  have hgZ : A.SmoothOn Zᶜ g := fun j => (hg j).mono fun y hy => ⟨hy.1, trivial⟩
  have hθ' := isPotentialAdd A _ _ hθ (isPotentialRsmul A C' _ hbp)
  have hb1 : LvBd A Om K (θ + b.rsmul C') := by
    refine LvBd.mono (K := K₀ + C' * Kb) (fun j y hy w => ?_) hpos (by linarith)
    rw [lv_add (twice_differentiable_of_potential hθ hy) ((twice_differentiable_of_potential hbp hy).rsmul _), lv_rsmul (twice_differentiable_of_potential hbp hy)]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hC'0, add_mul, mul_assoc]
    exact add_le_add (hθb j y hy w) (mul_le_mul_of_nonneg_left (hbb j y hy w) hC'0)
  have hb2 : LvBd A Om K b := hbb.mono hpos (by linarith)
  have hb3 : LvBd A Om K a := hba.mono hpos (by linarith)
  have hsm : A.SmoothOn Zᶜ fun x => g x + C' * p x := fun j => (hgZ j).add (contDiffOn_const.mul (hps j))
  have hup : ∀ x, x ∉ Z → g x + C' * p x ≤ -(1 * Real.log (r x)) := fun x hx => by
    have := one_le_log hr hx
    have h3 := mul_le_mul_of_nonneg_left (hpb x hx).2 hC'0
    have h4 := mul_le_mul_of_nonneg_right hC'c (zero_le_one.trans this)
    have h5 := (abs_le.1 (hgb x hx)).2
    nlinarith
  have hl1 : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w,
      leviAt A (θ + b.rsmul C' + LocPot.ofFun fun x => g x + C' * p x) j y w =
        leviAt A θ j y w + leviAt A (LocPot.ofFun g) j y w + C' * leviAt A (b + LocPot.ofFun p) j y w := by
    intro j y hy hyZ w
    rw [lv_add (twice_differentiable_of_potential hθ' hy) (twice_differentiable_off_set hZ hsm hy hyZ), lv_add (twice_differentiable_of_potential hθ hy) ((twice_differentiable_of_potential hbp hy).rsmul _),
      lv_rsmul (twice_differentiable_of_potential hbp hy), lv_fun (twice_differentiable_off_set hZ hgZ hy hyZ) (twice_differentiable_off_set hZ hps hy hyZ),
      lv_add (twice_differentiable_of_potential hbp hy) (twice_differentiable_off_set hZ hps hy hyZ)]
    ring
  have h0 : A.Smooth fun _ => (0 : ℝ) := fun _ => contDiffOn_const
  have hl3 : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w,
      leviAt A (a + LocPot.ofFun fun _ => 0) j y w = leviAt A a j y w := by
    intro j y hy w
    rw [lv_add (twice_differentiable_of_potential ha hy) (twice_differentiable_of_potential (isPotential_ofFun A _ h0) hy), lv_zero, add_zero]
  have L1 : ListForm A Z r Om K (θ + b.rsmul C' + LocPot.ofFun fun x => g x + C' * p x) := by
    refine ⟨_, _, rfl, hθ', (hb1.psh hOm hθ').1, (hb1.psh hOm hθ').2, hsm, fun x hx => ⟨?_, ?_⟩,
      Or.inr (toBot_of_le hr hbot one_pos hup), fun j y hy hyZ w => ?_⟩
    · have := zero_le_one.trans (one_le_log hr hx)
      have h3 := mul_le_mul_of_nonneg_left (hpb x hx).1 hC'0
      have h4 := mul_le_mul_of_nonneg_right (show C₁ + C' * Cp ≤ K by nlinarith) this
      have h5 := (abs_le.1 (hgb x hx)).1
      nlinarith
    · linarith [hup x hx, one_le_log hr hx]
    · have h3 := hpsh j y hy hyZ w
      have cb := (twice_differentiable_of_potential hbp hy).add (twice_differentiable_off_set hZ hps hy hyZ)
      rw [lv_add ((twice_differentiable_of_potential hθ hy).add (twice_differentiable_off_set hZ hgZ hy hyZ)) (cb.rsmul _), lv_rsmul cb,
        lv_add (twice_differentiable_of_potential hθ hy) (twice_differentiable_off_set hZ hgZ hy hyZ)] at h3
      rw [hl1 j y hy hyZ]
      have h4 := mul_le_mul_of_nonneg_right (show t ≤ C' by linarith) (hbe j y hy hyZ w)
      linarith
  have L2 : ListForm A Z r Om K (b + LocPot.ofFun p) := by
    refine ⟨_, _, rfl, hbp, (hb2.psh hOm hbp).1, (hb2.psh hOm hbp).2, hps, fun x hx => ⟨?_, ?_⟩,
      Or.inr (toBot_of_le hr hbot hc fun x hx => (hpb x hx).2), hbe⟩
    · have := zero_le_one.trans (one_le_log hr hx)
      have h4 := mul_le_mul_of_nonneg_right (show Cp ≤ K by linarith) this
      linarith [(hpb x hx).1]
    · have := mul_nonneg hc.le (zero_le_one.trans (one_le_log hr hx))
      linarith [(hpb x hx).2]
  have L3 : ListForm A Z r Om K (a + LocPot.ofFun fun _ => 0) := by
    refine ⟨_, _, rfl, ha, (hb3.psh hOm ha).1, (hb3.psh hOm ha).2, fun _ => contDiffOn_const, fun x hx => ⟨?_, le_rfl⟩,
      Or.inl h0, fun j y hy _ w => ?_⟩
    · have := mul_nonneg (show 0 ≤ K by linarith) (zero_le_one.trans (one_le_log hr hx))
      linarith
    · rw [hl3 j y hy]
      exact lv_nonneg hap hy w
  have hs' := isPotentialRsmul A s _ ha
  refine ⟨isPotentialAdd A _ _ (isPotentialAdd A _ _ hθ hs') (isPotential_ofFun A _ hg),
    ![θ + b.rsmul C' + LocPot.ofFun fun x => g x + C' * p x, b + LocPot.ofFun p, a + LocPot.ofFun fun _ => 0],
    ![1, -C', s], fun l => ?_, fun j y hy hyZ w => ?_⟩
  · fin_cases l
    · exact ⟨L1, by simp; linarith⟩
    · exact ⟨L2, by simp [abs_of_nonneg hC'0]; linarith⟩
    · exact ⟨L3, by simp [abs_of_nonneg hs.1]; linarith [hs.2]⟩
  · rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [hl1 j y hy hyZ, hl3 j y hy, lv_add ((twice_differentiable_of_potential hθ hy).add (twice_differentiable_of_potential hs' hy)) (twice_differentiable_off_set hZ hgZ hy hyZ),
      lv_add (twice_differentiable_of_potential hθ hy) (twice_differentiable_of_potential hs' hy), lv_rsmul (twice_differentiable_of_potential ha hy)]
    ring

end Gen

theorem th_linear {D : D7} {Y : ShimX D.what₂.Tau} (T : Real0 Y) (c : Y.Comp) (σ : Fin ((T.M c).n + 1))
    (j : Fin ((T.M c).A σ).n) (y : Fin (dimY Y) → ℂ) (hy : y ∈ (((T.M c).A σ).chart j).target)
    (w : Fin (dimY Y) → ℂ) : IsLinearMap ℝ fun u => leviAt ((T.M c).A σ) ((T.F c).th u σ) j y w := by
  have hc := fun v => twice_differentiable_of_potential ((T.K 2 c).firstChern_isPotential v σ) hy
  refine ⟨fun u v => ?_, fun t v => ?_⟩
  · rw [← T.c1_L 2 c _ σ j y hy, map_add, (T.K 2 c).isOneCochain_add _ _ σ j y hy, lv_add (hc _) (hc _),
      T.c1_L 2 c _ σ j y hy, T.c1_L 2 c _ σ j y hy]
  · rw [← T.c1_L 2 c _ σ j y hy, map_smul, (T.K 2 c).firstChern_smul_leviEq _ _ σ j y hy, lv_rsmul (hc _),
      T.c1_L 2 c _ σ j y hy, smul_eq_mul]

theorem famR_of_inR (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (c : Y.Comp)
    (ha : ∀ σ, IsPsh ((T.M c).A σ) ((T.F c).a σ)) (hS : (T.F c).Size) (hR : (T.F c).InR Y.j) :
    (T.F c).FamR Y.j := by
  intro Λ
  obtain ⟨-, -, -, C₁, hC₁⟩ := hS
  have hmul : ∀ (C : ℝ) (u : Wt Y), ‖u‖ ≤ Λ → C * ‖u‖ ≤ |C| * |Λ| := fun C u hu =>
    mul_le_mul (le_abs_self C) (hu.trans (le_abs_self Λ)) (norm_nonneg _) (abs_nonneg _)
  have h2 : ∀ R : ℝ, Real.exp 2 ≤ R → 2 ≤ R := fun R h => by linarith [Real.add_one_le_exp 2]
  have key : ∀ σ, ∃ K₁ : ℝ, ∀ K, K₁ ≤ K → ∀ u : Wt Y, DomL Y.j u → ‖u‖ ≤ Λ → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ R : ℝ,
      Real.exp 2 ≤ R → ((T.M c).A σ).Smooth ((T.F c).phR R u σ) ∧
      Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) K ((T.F c).form u s ((T.F c).phR R u) σ) ∧
      ∀ x, x ∉ (T.M c).Z σ → |(T.F c).phR R u σ x| ≤ K * Real.log ((T.M c).r σ x) ∧
        ((T.M c).r σ x ≤ Real.sqrt R → |(T.F c).phR R u σ x - (T.F c).ph u σ x| ≤ K / R) := by
    intro σ
    obtain ⟨b, p, hb, C₂, hC₂⟩ := hR σ
    have hbd := (T.M c).bd σ
    obtain ⟨K₀, hK₀, hth⟩ := exists_lvBd_lin hbd.2.2.1 hbd.2.2.2.1 (fun u => (T.F c).th u σ)
      (fun u => T.th_pot c u σ) (th_linear T c σ)
    obtain ⟨K₁, hK₁⟩ := comb_one hbd (T.a_pot c σ) (ha σ) hb (|Λ| * K₀) (|C₁| * |Λ|) (|C₂| * |Λ|)
      (by positivity) (by positivity) (by positivity)
    refine ⟨max K₁ (max (|C₁| * |Λ|) (|C₂| * |Λ|)), fun K hK u hu hΛ s hs R hR' => ?_⟩
    obtain ⟨hKa, hK'⟩ := max_le_iff.1 hK
    obtain ⟨hKb, hKc⟩ := max_le_iff.1 hK'
    obtain ⟨hsm, hps, hx⟩ := hC₂ u R (h2 R hR')
    have hlog := fun x (hx : x ∉ (T.M c).Z σ) => zero_le_one.trans (one_le_log hbd.2.2.2.2.2.1 hx)
    have hg : ∀ x, x ∉ (T.M c).Z σ → |(T.F c).phR R u σ x| ≤ |C₁| * |Λ| * Real.log ((T.M c).r σ x) := fun x hx =>
      ((hC₁ u σ x hx).2 R (h2 R hR')).trans (mul_le_mul_of_nonneg_right (hmul C₁ u hΛ) (hlog x hx))
    refine ⟨hsm, hK₁ K hKa _ _ _ (T.th_pot c u σ) ((hth u).mono hbd.2.2.2.1
      (mul_le_mul_of_nonneg_right (hΛ.trans (le_abs_self Λ)) hK₀)) hsm hg (hmul C₂ u hΛ) (hps hu) s hs,
      fun x hxZ => ⟨(hg x hxZ).trans (mul_le_mul_of_nonneg_right hKb (hlog x hxZ)), fun h => ?_⟩⟩
    exact ((hx x hxZ).2 h).trans
      (div_le_div_of_nonneg_right ((hmul C₂ u hΛ).trans hKc) (by linarith [h2 R hR']))
  choose K₁ hK₁ using key
  refine ⟨∑ σ, |K₁ σ|, fun u hu hΛ s hs R hR' σ => hK₁ σ _ ?_ u hu hΛ s hs R hR'⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (K₁ i)) (Finset.mem_univ σ))

end GlobalTheory.Mean4O.InterpFam
