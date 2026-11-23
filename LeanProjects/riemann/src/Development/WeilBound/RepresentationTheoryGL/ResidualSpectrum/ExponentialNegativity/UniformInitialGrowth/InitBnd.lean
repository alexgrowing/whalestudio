import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace PositivityTheory.Rg.Rs.JInitBnd

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def ext0 (x : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then x ⟨j, h⟩ else 0

theorem sr_eq (x : Fin n → ℝ) {r : ℕ} (h0 : 0 < r) (h1 : r < n) : An.sr x r = ext0 x (r - 1) - ext0 x r := by
  rw [An.sr, dif_pos ⟨h0, h1⟩, ext0, ext0, dif_pos (by omega : r - 1 < n), dif_pos h1]

theorem abs_sr_le (x : Fin n → ℝ) (t₀ : ℝ) (hx : ∀ r, -t₀ ≤ An.sr x r) (r : ℕ) :
    |An.sr x r| ≤ An.sr x r + 2 * t₀ := by
  have h0 : -t₀ ≤ 0 := by simpa [An.sr] using hx 0
  have := hx r
  rw [abs_le]; constructor <;> linarith

theorem sum_bound (x : Fin n → ℝ) (t₀ : ℝ) (hx : ∀ r, -t₀ ≤ An.sr x r) :
    ∑ r ∈ Finset.range n, |An.sr x r| ≤ ∑ r ∈ Finset.range n, An.sr x r + 2 * (n : ℝ) * t₀ := by
  calc ∑ r ∈ Finset.range n, |An.sr x r| ≤ ∑ r ∈ Finset.range n, (An.sr x r + 2 * t₀) :=
        Finset.sum_le_sum fun r _ => abs_sr_le x t₀ hx r
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem bound_nonneg (x : Fin n → ℝ) (t₀ : ℝ) (hx : ∀ r, -t₀ ≤ An.sr x r) :
    0 ≤ ∑ r ∈ Finset.range n, An.sr x r + 2 * (n : ℝ) * t₀ :=
  (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (sum_bound x t₀ hx)

theorem abs_le_bound (x : Fin n → ℝ) (t₀ : ℝ) (hx : ∀ r, -t₀ ≤ An.sr x r)
    (hlast : ∀ i : Fin n, (i : ℕ) + 1 = n → x i = 0) (i : Fin n) :
    |x i| ≤ ∑ r ∈ Finset.range n, An.sr x r + 2 * (n : ℝ) * t₀ := by
  have hXi : ext0 x i = x i := by rw [ext0, dif_pos i.2]
  have hXl : ext0 x (n - 1) = 0 := by
    rw [ext0]; split_ifs with h
    · exact hlast _ (by show n - 1 + 1 = n; omega)
    · rfl
  have tele : ext0 x i = ∑ k ∈ Finset.range (n - ((i : ℕ) + 1)), An.sr x ((i : ℕ) + 1 + k) := by
    have := Finset.sum_range_sub' (fun k => ext0 x ((i : ℕ) + k)) (n - ((i : ℕ) + 1))
    simp only [add_zero] at this
    rw [show (i : ℕ) + (n - ((i : ℕ) + 1)) = n - 1 by omega, hXl, sub_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [sr_eq x (r := (i : ℕ) + 1 + k) (by omega) (by omega), show (i : ℕ) + 1 + k - 1 = i + k by omega,
      show (i : ℕ) + 1 + k = i + (k + 1) by omega]
  calc |x i| = |∑ k ∈ Finset.range (n - ((i : ℕ) + 1)), An.sr x ((i : ℕ) + 1 + k)| := by rw [← hXi, tele]
    _ ≤ ∑ k ∈ Finset.range (n - ((i : ℕ) + 1)), |An.sr x ((i : ℕ) + 1 + k)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ Finset.Ico ((i : ℕ) + 1) n, |An.sr x r| := (Finset.sum_Ico_eq_sum_range (fun r => |An.sr x r|) ((i : ℕ) + 1) n).symm
    _ ≤ ∑ r ∈ Finset.range n, |An.sr x r| :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => by
          rw [Finset.mem_Ico] at hr; rw [Finset.mem_range]; exact hr.2) (fun _ _ _ => abs_nonneg _)
    _ ≤ _ := sum_bound x t₀ hx

theorem tor_add (x y : Fin n → ℝ) : An.tor E (x + y) = An.tor E x * An.tor E y := by
  unfold An.tor
  rw [← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply]
  rw [← GlobalTheory.CuspBoundSiegel.posIdele_mul]
  exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (by rw [Pi.add_apply, Real.exp_add])

theorem tor_const_comm (c : ℝ) (g : AdelicGLn.AdelicGL E n) :
    An.tor E (fun _ : Fin n => c) * g = g * An.tor E (fun _ => c) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [An.tor, Units.val_mul, coe_diagUnits, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

theorem pFin_diag (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Matrix.GeneralLinearGroup.map (pFin E) (diagUnits n fun i => posIdele (K := E) (r i) (hr i)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, coe_diagUnits, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
  split_ifs
  · change ((posIdele (K := E) (r i) (hr i) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = 1
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl
  · exact map_zero _

theorem pFin_tor (x : Fin n → ℝ) : Matrix.GeneralLinearGroup.map (pFin E) (An.tor E x) = 1 :=
  pFin_diag (fun i => Real.exp (x i)) (fun i => Real.exp_pos _)

variable [IsTotallyComplex E]

def dg (x : Fin n → ℝ) : GL (Fin n) (Cinf E) := diagUnits n fun i => expU fun _ : InfinitePlace E => ((x i : ℝ) : ℂ)

theorem pInf_infId (v : (Cinf E)ˣ) : pInf E (infId E v) = v := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) = _
  simp only [map_add, map_sub, map_one, h, sub_self, zero_add]

theorem pInf_tor (x : Fin n → ℝ) : Matrix.GeneralLinearGroup.map (pInf E) (An.tor E x) = dg x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, An.tor, dg, coe_diagUnits, coe_diagUnits, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  split_ifs
  · rw [GlobalTheory.CuspBoundSiegel.posIdele_exp, pInf_infId]
  · exact map_zero _

omit [IsTotallyComplex E] in
theorem height_inv' (y : GL (Fin n) (Cinf E)) : GlobalTheory.CuspRep.height y⁻¹ = GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height; rw [inv_inv]; ring

omit [IsTotallyComplex E] in
theorem height_dg (x : Fin n → ℝ) (R : ℝ) (hR : ∀ i, |x i| ≤ R) (hR0 : 0 ≤ R) :
    GlobalTheory.CuspRep.height (dg (E := E) x) ≤ 3 * Real.exp R := by
  have he : 0 ≤ Real.exp R := (Real.exp_pos R).le
  have h1 : ‖toL (dg (E := E) x).val‖ ≤ Real.exp R := by
    refine (pi_norm_le_iff_of_nonneg he).2 fun i => (pi_norm_le_iff_of_nonneg he).2 fun j =>
      (pi_norm_le_iff_of_nonneg he).2 fun w => ?_
    change ‖(Matrix.diagonal (fun k => ((expU fun _ : InfinitePlace E => ((x k : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E)) i j) w‖ ≤ _
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · change ‖Complex.exp ((x i : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (hR i))
    · simp only [Pi.zero_apply, norm_zero]; exact he
  have h2 : ‖toL ((dg (E := E) x)⁻¹).val‖ ≤ Real.exp R := by
    refine (pi_norm_le_iff_of_nonneg he).2 fun i => (pi_norm_le_iff_of_nonneg he).2 fun j =>
      (pi_norm_le_iff_of_nonneg he).2 fun w => ?_
    change ‖(Matrix.diagonal (fun k => (((expU fun _ : InfinitePlace E => ((x k : ℝ) : ℂ) : (Cinf E)ˣ)⁻¹ : (Cinf E)ˣ) :
      Cinf E)) i j) w‖ ≤ _
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · change ‖Complex.exp (-((x i : ℝ) : ℂ))‖ ≤ _
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.2 ((neg_le_abs _).trans (hR i))
    · simp only [Pi.zero_apply, norm_zero]; exact he
  have h3 : 1 ≤ Real.exp R := Real.one_le_exp hR0
  unfold GlobalTheory.CuspRep.height
  linarith

abbrev mI (g : GA E n) : GL (Fin n) (Cinf E) := Matrix.GeneralLinearGroup.map (pInf E) g

theorem key (b s k : GA E n) (hs : Matrix.GeneralLinearGroup.map (pFin E) s = 1) (y : GL (Fin n) (Cinf E)) :
    b * s * k * infGL E n y = b * k * infGL E n ((mI k)⁻¹ * mI s * mI k * y) := by
  apply ga_ext
  · simp only [mI, map_mul, pInf_infGL, mul_assoc, mul_inv_cancel_left]
  · simp only [map_mul, pFin_infGL, hs, mul_one]

theorem key0 (b s k : GA E n) (hs : Matrix.GeneralLinearGroup.map (pFin E) s = 1) :
    b * s * k = b * k * infGL E n ((mI k)⁻¹ * mI s * mI k) := by
  apply ga_ext
  · simp only [mI, map_mul, pInf_infGL, mul_assoc, mul_inv_cancel_left]
  · simp only [map_mul, pFin_infGL, hs, mul_one]

theorem uniform_growth0 (φ : Sm E n) (hopen : IsOpen {k | finRep E n k φ = φ}) (N0 : ℕ)
    (hgr : ∀ g, ∃ C : ℝ, ∀ y, ‖φ.1 (g * infGL E n y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N0)
    {Ω : Set (GA E n)} (hΩ : IsCompact Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Ω, ∀ y, ‖φ.1 (h * infGL E n y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N0 := by
  have hS : ∀ s : GL (Fin n) (Af E), finRep E n s φ = φ → ∀ x, φ.1 (x * finGL E n s) = φ.1 x := fun s hs x => by
    have := congrFun (congrArg Subtype.val hs) x
    exact this
  have hU : ∀ t : GL (Fin n) (Af E), IsOpen ((fun k => t⁻¹ * k) ⁻¹' {k | finRep E n k φ = φ}) := fun t =>
    hopen.preimage (continuous_const.mul continuous_id)
  have hKf : IsCompact (Matrix.GeneralLinearGroup.map (n := Fin n) (pFin E) '' Ω) :=
    hΩ.image GlobalTheory.ConstTermGrowth.continuous_mapFin
  obtain ⟨T, hT⟩ := hKf.elim_finite_subcover (fun t => (fun k => t⁻¹ * k) ⁻¹' {k | finRep E n k φ = φ}) hU
    (fun k _ => Set.mem_iUnion.2 ⟨k, by
      change finRep E n (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]; rfl⟩)
  choose C hC using hgr
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le
    (hΩ.image (GlobalTheory.ConstTermGrowth.continuous_mapInf (E := E) (a := n)))
  refine ⟨∑ t ∈ T, |C (finGL E n t)| * B ^ N0,
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _), fun h hh y => ?_⟩
  obtain ⟨t, htT, hkt⟩ := Set.mem_iUnion₂.1 (hT ⟨h, hh, rfl⟩)
  have e : h * infGL E n y = finGL E n t * infGL E n (Matrix.GeneralLinearGroup.map (pInf E) h * y) *
      finGL E n (t⁻¹ * Matrix.GeneralLinearGroup.map (pFin E) h) := by
    apply ga_ext
    · simp only [map_mul, pInf_infGL, pInf_finGL, one_mul, mul_one]
    · simp only [map_mul, pFin_infGL, pFin_finGL, mul_one, mul_inv_cancel_left]
  rw [e, hS _ hkt]
  have hcy := hB _ ⟨h, hh, rfl⟩ y
  have h0 := one_le_height (Matrix.GeneralLinearGroup.map (pInf E) h * y)
  have hy := one_le_height y
  calc ‖φ.1 (finGL E n t * infGL E n (Matrix.GeneralLinearGroup.map (pInf E) h * y))‖
      ≤ C (finGL E n t) * GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) h * y) ^ N0 := hC _ _
    _ ≤ |C (finGL E n t)| * (B * GlobalTheory.CuspRep.height y) ^ N0 :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) hcy _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C (finGL E n t)| * B ^ N0 * GlobalTheory.CuspRep.height y ^ N0 := by ring
    _ ≤ (∑ t ∈ T, |C (finGL E n t)| * B ^ N0) * GlobalTheory.CuspRep.height y ^ N0 :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun t => |C (finGL E n t)| * B ^ N0)
          (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _)) htT) (pow_nonneg (by linarith) _)

theorem uniform_exp (φ : Sm E n) (hA : IsAutForm φ) :
    ∃ N0 : ℕ, ∀ g : GA E n, ∃ C : ℝ, ∀ y, ‖φ.1 (g * infGL E n y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N0 := by
  obtain ⟨ω0, hω0, -, t, -, hsieg⟩ := exists_siegelSet (K := E) n
  obtain ⟨C, N0, hC⟩ := GlobalTheory.ConstTermGrowth.uniform_growth φ hA.level hA.growth
    (hω0.mul (isCompact_maxCompact (K := E) (n := n)))
  refine ⟨N0, fun g => ?_⟩
  obtain ⟨γ, hmem⟩ := hsieg g
  obtain ⟨b, hb, a, ⟨r, hr, -, rfl⟩, k, hk, e⟩ := hmem
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E)
    (isCompact_singleton (x := (mI k)⁻¹ * mI (diagUnits n fun i => posIdele (K := E) (r i) (hr i)) * mI k))
  refine ⟨|C| * B ^ N0, fun y => ?_⟩
  have e2 : φ.1 (g * infGL E n y) = φ.1 ((b * k) * infGL E n
      ((mI k)⁻¹ * mI (diagUnits n fun i => posIdele (K := E) (r i) (hr i)) * mI k * y)) := by
    rw [← hA.left γ (g * infGL E n y), ← mul_assoc (ratGL E n γ) g]
    change φ.1 (AdelicGLn.diagonal E n γ * g * infGL E n y) = _
    rw [e, key b _ k (pFin_diag r hr) y]
  rw [e2]
  have h1 := hC (b * k) (Set.mul_mem_mul hb hk)
    ((mI k)⁻¹ * mI (diagUnits n fun i => posIdele (K := E) (r i) (hr i)) * mI k * y)
  have h2 := hB _ rfl y
  have hy := one_le_height y
  have hcy := one_le_height ((mI k)⁻¹ * mI (diagUnits n fun i => posIdele (K := E) (r i) (hr i)) * mI k * y)
  calc _ ≤ _ := h1
    _ ≤ |C| * (B * GlobalTheory.CuspRep.height y) ^ N0 :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) h2 _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C| * B ^ N0 * GlobalTheory.CuspRep.height y ^ N0 := by ring

end PositivityTheory.Rg.Rs.JInitBnd

namespace PositivityTheory.Rg.Rs

open JInitBnd in
theorem initBnd_holds : InitBnd := by
  intro E _ _ _ N φ hA hZ
  obtain ⟨N0, hN0⟩ := uniform_exp φ hA
  refine ⟨(N0 : ℝ), ?_⟩
  intro ω hω _ t₀ Q hQ
  obtain ⟨C1, hC10, hC1⟩ := uniform_growth0 φ hA.level N0 hN0 (hω.mul hQ)
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le
    (hQ.image (GlobalTheory.ConstTermGrowth.continuous_mapInf (E := E) (a := N)).inv)
  refine ⟨C1 * (3 * B * B * Real.exp (2 * (N : ℝ) * t₀)) ^ N0, fun b hb x hx q hq => ?_⟩
  show ‖φ.1 (b * An.tor E x * q)‖ ≤ _ * Real.exp (∑ r ∈ Finset.range N, (N0 : ℝ) * An.sr x r)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ i : Fin N, (i : ℕ) + 1 = N → x i = c := by
    by_cases hN : 0 < N
    · exact ⟨x ⟨N - 1, by omega⟩, fun i hi => congrArg x (Fin.ext (by simp only; omega))⟩
    · exact ⟨0, fun i _ => by exfalso; have := i.2; omega⟩
  set x' : Fin N → ℝ := fun i => x i - c with hx'
  have hsr : ∀ r, An.sr x' r = An.sr x r := fun r => by
    unfold An.sr; split_ifs <;> simp [hx']
  have hx'' : ∀ r, -t₀ ≤ An.sr x' r := fun r => (hsr r).symm ▸ hx r
  have hlast : ∀ i : Fin N, (i : ℕ) + 1 = N → x' i = 0 := fun i hi => by simp only [hx', hc i hi, sub_self]
  have hS : ∑ r ∈ Finset.range N, An.sr x' r = ∑ r ∈ Finset.range N, An.sr x r :=
    Finset.sum_congr rfl fun r _ => hsr r
  have hR0 : 0 ≤ ∑ r ∈ Finset.range N, An.sr x r + 2 * (N : ℝ) * t₀ := by
    rw [← hS]; exact bound_nonneg x' t₀ hx''
  have hxR : ∀ i, |x' i| ≤ ∑ r ∈ Finset.range N, An.sr x r + 2 * (N : ℝ) * t₀ := fun i => by
    rw [← hS]; exact abs_le_bound x' t₀ hx'' hlast i
  have hD := height_dg (E := E) x' _ hxR hR0
  have e1 : φ.1 (b * An.tor E x * q) = φ.1 (b * An.tor E x' * q) := by
    have htor : An.tor E x = An.tor E (fun _ : Fin N => c) * An.tor E x' := by
      rw [← tor_add]; congr 1; funext i; simp [hx']
    rw [← hZ c (b * An.tor E x' * q)]
    refine congrArg _ ?_
    rw [htor, ← mul_assoc b, ← tor_const_comm c b]
    simp only [mul_assoc]
  have e2 : φ.1 (b * An.tor E x' * q) = φ.1 ((b * q) * infGL E N ((mI q)⁻¹ * dg x' * mI q)) := by
    rw [key0 b _ q (pFin_tor x'), mI, mI, pInf_tor]
  have hz : GlobalTheory.CuspRep.height ((mI q)⁻¹ * dg (E := E) x' * mI q) ≤ B * B * GlobalTheory.CuspRep.height (dg (E := E) x') := by
    have h1 := hB (mI q)⁻¹ ⟨q, hq, rfl⟩ (dg x' * mI q)
    have h2 := hB (mI q)⁻¹ ⟨q, hq, rfl⟩ (dg x')⁻¹
    rw [← _root_.mul_inv_rev, height_inv', height_inv'] at h2
    rw [mul_assoc]
    calc _ ≤ B * GlobalTheory.CuspRep.height (dg (E := E) x' * mI q) := h1
      _ ≤ B * (B * GlobalTheory.CuspRep.height (dg (E := E) x')) := mul_le_mul_of_nonneg_left h2 hB0
      _ = _ := by ring
  rw [e1, e2]
  have hy1 := one_le_height ((mI q)⁻¹ * dg (E := E) x' * mI q)
  calc _ ≤ C1 * GlobalTheory.CuspRep.height ((mI q)⁻¹ * dg (E := E) x' * mI q) ^ N0 := hC1 _ (Set.mul_mem_mul hb hq) _
    _ ≤ C1 * (B * B * (3 * Real.exp (∑ r ∈ Finset.range N, An.sr x r + 2 * (N : ℝ) * t₀))) ^ N0 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
          (hz.trans (mul_le_mul_of_nonneg_left hD (mul_nonneg hB0 hB0))) _) hC10
    _ = _ := by
        rw [← Finset.mul_sum, Real.exp_nat_mul, Real.exp_add, mul_assoc C1, ← mul_pow]
        ring

end PositivityTheory.Rg.Rs

end
