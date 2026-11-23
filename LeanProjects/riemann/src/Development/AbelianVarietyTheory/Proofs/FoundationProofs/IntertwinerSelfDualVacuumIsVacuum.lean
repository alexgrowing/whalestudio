import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniquenessStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.VacuumMove

lemma even_im_hermitian_sub (a b c d u v x y m e : ℤ) (hm : 2 ∣ m) (he : e = 1 ∨ e = -1) (h1 : a + d = 1)
    (h2 : a ^ 2 + b * c - a + m = 0) (h3 : ¬ (2 ∣ u * a + v * c ∧ 2 ∣ u * b + v * d))
    (h4 : ¬ (2 ∣ u - (u * a + v * c) ∧ 2 ∣ v - (u * b + v * d))) :
    2 ∣ e * ((x * a + y * c) * y - (x * b + y * d) * x) + (-e) * (x * v - y * u) ↔ (2 ∣ x ∧ 2 ∣ y) := by
  have k : ∀ n : ℤ, 2 ∣ n ↔ (n : ZMod 2) = 0 := fun n =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).symm
  have he' : (e : ZMod 2) = 1 := by rcases he with rfl | rfl <;> decide
  have h1' := congrArg (Int.cast : ℤ → ZMod 2) h1
  have h2' := congrArg (Int.cast : ℤ → ZMod 2) h2
  simp only [k] at hm h3 h4 ⊢
  push_cast at *
  rw [hm] at h2'
  rw [he']
  generalize (a : ZMod 2) = a at *
  generalize (b : ZMod 2) = b at *
  generalize (c : ZMod 2) = c at *
  generalize (d : ZMod 2) = d at *
  generalize (u : ZMod 2) = u at *
  generalize (v : ZMod 2) = v at *
  generalize (x : ZMod 2) = x at *
  generalize (y : ZMod 2) = y at *
  revert a b c d u v x y
  decide

lemma exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z = Complex.exp (Real.pi * (t * starRingEnd ℂ ω - ω * starRingEnd ℂ t) / (area Λ : ℂ)) *
      U1 Λ t (U1 Λ ω G) z := by
  simp only [U1]
  rw [add_right_comm z ω t, mul_left_comm]
  simp only [mul_assoc (G _), ← Complex.exp_add]
  congr 2
  ring

lemma int_indep (L : PeriodPair) {p q : ℤ} (h : (p : ℂ) * L.ω₁ + q * L.ω₂ = 0) : p = 0 ∧ q = 0 := by
  have := LinearIndependent.pair_iff.mp L.indep p q (by simpa using h)
  exact_mod_cast this

lemma half_mem (L : PeriodPair) (p q : ℤ) :
    ((p : ℂ) * L.ω₁ + q * L.ω₂) / 2 ∈ L.lattice ↔ (2 ∣ p ∧ 2 ∣ q) := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    have := int_indep L (p := p - 2 * m) (q := q - 2 * n) (by push_cast; linear_combination -2 * h)
    omega
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    exact ⟨m, n, by push_cast; ring⟩

lemma genus_one (D : D7) (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (hw : ∀ w ∈ Λ, w0 D * w ∈ Λ) (G : ℂ → ℂ)
    (hG : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z)
    (t : ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D Λ t) (ω : ℂ) (hω : ω ∈ Λ) :
    ∃ n : ℤ, (Real.sqrt D.host.d : ℂ) / 2 * (ω * starRingEnd ℂ ω / (area Λ : ℂ)) = n ∧
      ∀ z, (-1 : ℂ) ^ n * U1 Λ ω (U1 Λ t G) z = U1 Λ t G z := by
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by omega⟩
  have hm' : (D.host.d : ℂ) + 1 = 8 * m := by exact_mod_cast hm
  set s : ℂ := (Real.sqrt D.host.d : ℂ) with hs
  have hs2 : s ^ 2 = D.host.d := by
    rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have hsc : starRingEnd ℂ s = s := Complex.conj_ofReal _
  have hw0 : w0 D = (1 + Complex.I * s) / 2 := rfl
  have hw0c : starRingEnd ℂ (w0 D) = (1 - Complex.I * s) / 2 := by
    rw [hw0, map_div₀, map_add, map_mul, hsc, Complex.conj_I, map_one, map_ofNat]; ring
  have hq : w0 D ^ 2 - w0 D + 2 * m = 0 := by
    rw [hw0]
    linear_combination (s ^ 2 / 4) * Complex.I_sq - (1 / 4) * hs2 - (1 / 4) * hm'
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((h _).1 (hw _ ((h _).2 L.ω₁_mem_lattice)))
  obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.1 ((h _).1 (hw _ ((h _).2 L.ω₂_mem_lattice)))
  obtain ⟨x, y, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 hω)
  obtain ⟨u, v, huv⟩ := PeriodPair.mem_lattice.1 ((h _).1 ht.1)
  have hA := GlobalTheory.LatticeInvariants.area_eq h
  have r1 := int_indep L (p := a ^ 2 + b * c - a + 2 * m) (q := b * (a + d - 1)) (by
    push_cast
    linear_combination L.ω₁ * hq + (w0 D + a - 1) * hab + b * hcd)
  have r2 := int_indep L (p := c * (a + d - 1)) (q := d ^ 2 + b * c - d + 2 * m) (by
    push_cast
    linear_combination L.ω₂ * hq + (w0 D + d - 1) * hcd + c * hab)
  have had : a + d = 1 := by
    by_contra hne
    have hb : b = 0 := by
      rcases mul_eq_zero.1 r1.2 with h | h
      · exact h
      · omega
    have h1 : L.ω₁ ≠ 0 := by
      intro h0
      simpa using (int_indep L (p := 1) (q := 0) (by simp [h0])).1
    have h2 : w0 D = a := by
      apply mul_right_cancel₀ h1
      rw [← hab, hb]; simp
    have h3 : Complex.I * s = 0 := by
      have := hw0c
      rw [h2, map_intCast, ← h2, hw0] at this
      linear_combination this
    have h4 : (D.host.d : ℂ) = 0 := by
      linear_combination -hs2 + s ^ 2 * Complex.I_sq - (Complex.I * s) * h3
    have : D.host.d = 0 := by exact_mod_cast h4
    omega
  have hne : (L.ω₁ * starRingEnd ℂ L.ω₂).im ≠ 0 := by
    intro h0
    have hi := LinearIndependent.pair_iff.mp L.indep
    simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re] at h0
    have h1 := hi L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have h2 := hi L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have h3 : L.ω₂ = 0 := Complex.ext h1.1 h2.1
    simpa using (hi 0 1 (by simp [h3])).2
  have hA0 : (area Λ : ℂ) ≠ 0 := by
    rw [hA]; exact_mod_cast abs_ne_zero.2 hne
  obtain ⟨e, he, hS⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      L.ω₁ * starRingEnd ℂ L.ω₂ - starRingEnd ℂ L.ω₁ * L.ω₂ = 2 * Complex.I * e * area Λ := by
    have h0 := Complex.sub_conj (L.ω₁ * starRingEnd ℂ L.ω₂)
    rw [map_mul, Complex.conj_conj] at h0
    rw [h0, hA]
    rcases abs_choice (L.ω₁ * starRingEnd ℂ L.ω₂).im with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h1]; push_cast; ring⟩
  have hab' := congrArg (starRingEnd ℂ) hab
  have hcd' := congrArg (starRingEnd ℂ) hcd
  have huv' := congrArg (starRingEnd ℂ) huv
  simp only [map_add, map_mul, map_intCast, map_ofNat, hw0c] at hab' hcd' huv'
  have h3 : ¬ (2 ∣ u * a + v * c ∧ 2 ∣ u * b + v * d) := by
    rw [← half_mem L, ← h]
    convert ht.2.1 using 2
    push_cast
    rw [← hs, ← hw0]
    linear_combination (u / 2 : ℂ) * hab + (v / 2 : ℂ) * hcd + (w0 D / 2) * huv
  have h4 : ¬ (2 ∣ u - (u * a + v * c) ∧ 2 ∣ v - (u * b + v * d)) := by
    rw [← half_mem L, ← h]
    convert ht.2.2 using 2
    push_cast
    rw [← hs]
    rw [hw0] at hab hcd
    linear_combination -(u / 2 : ℂ) * hab - (v / 2 : ℂ) * hcd + ((1 - Complex.I * s) / 4) * huv
  have hp := even_im_hermitian_sub a b c d u v x y (2 * m) e (by simp) he had r1.1 h3 h4
  refine ⟨e * ((x * a + y * c) * y - (x * b + y * d) * x), ?_, fun z => ?_⟩
  · rw [hw0] at hab hcd
    simp only [map_add, map_mul, map_intCast]
    field_simp
    push_cast
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination ((x * a + y * c) * y - (x * b + y * d) * x : ℂ) * hS
      - (x * starRingEnd ℂ L.ω₁ + y * starRingEnd ℂ L.ω₂) * (x * hab + y * hcd)
      + (x * L.ω₁ + y * L.ω₂) * (x * hab' + y * hcd')
  · have hU : U1 Λ (x * L.ω₁ + y * L.ω₂) G =
        fun z => (if ((x : ℂ) * L.ω₁ + y * L.ω₂) / 2 ∈ Λ then 1 else -1) * G z := funext (hG _ hω)
    have hE : Complex.exp (Real.pi * (t * starRingEnd ℂ (x * L.ω₁ + y * L.ω₂) -
        (x * L.ω₁ + y * L.ω₂) * starRingEnd ℂ t) / (area Λ : ℂ)) = (-1) ^ ((-e) * (x * v - y * u)) := by
      rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      congr 1
      simp only [map_add, map_mul, map_intCast]
      field_simp
      push_cast
      linear_combination (-(x * v - y * u) / 2 : ℂ) * hS
        - (x * starRingEnd ℂ L.ω₁ + y * starRingEnd ℂ L.ω₂) / 2 * huv + (x * L.ω₁ + y * L.ω₂) / 2 * huv'
    rw [exists_orthonormal_basis_family, hE, hU, ← mul_assoc, ← zpow_add₀ (by norm_num), h, half_mem, ← hp]
    simp only [U1]
    split_ifs with h2
    · rw [Even.neg_one_zpow (even_iff_two_dvd.2 h2)]; ring
    · rw [Odd.neg_one_zpow (Int.not_even_iff_odd.1 fun h' => h2 (even_iff_two_dvd.1 h'))]; ring

section Product

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' r : ℕ}
  {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}

lemma coordB_embV (htr : TraceMapNormalisation D) (hb : Orthonormal D b) (i j : Fin r) :
    coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b i)) = if i = j then 1 else 0 := by
  have h1 := htr (∑ a, ∑ c, b i a c * D.host.conj (b j a c))
  have h2 := hb i j
  rw [hYY] at h2
  rw [h2] at h1
  have h3 : D.host.φ₀ (((if i = j then 1 else 0 : D.host.K) : D.host.K) : D.host.E) =
      if i = j then 1 else 0 := by
    split_ifs <;> simp
  rw [← h3, ← h1]
  simp only [coordB, embV, tor0, map_sum, map_mul, WeightFamilies.emb_conj]
  rfl

lemma coordB_add (T : Tor D) (j : Fin r) (z x : VC D N N') :
    coordB D T b j (z + x) = coordB D T b j z + coordB D T b j x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma coordB_smul (T : Tor D) (j : Fin r) (c : ℂ) (z : VC D N N') :
    coordB D T b j (c • z) = c * coordB D T b j z := by
  simp only [coordB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma coordB_sum (htr : TraceMapNormalisation D) (hb : Orthonormal D b) (c : Fin r → ℂ) (j : Fin r) :
    coordB D (tor0 D cc δ) b j (∑ i, c i • embV D (tor0 D cc δ) (b i)) = c j := by
  let f : VC D N N' →+ ℂ := AddMonoidHom.mk' (coordB D (tor0 D cc δ) b j) (coordB_add _ j)
  change f _ = _
  rw [map_sum]
  change ∑ i, coordB D (tor0 D cc δ) b j _ = _
  simp [coordB_smul, coordB_embV htr hb]

lemma Hf_sum (T : Tor D) (c : Fin r → ℂ) (z : VC D N N') :
    Hf D T z (∑ i, c i • embV D T (b i)) =
      ∑ i, coordB D T b i z * starRingEnd ℂ (c i) / (area T.abelian₂ : ℂ) := by
  rw [Hf, ← Finset.sum_div]
  congr 1
  simp only [coordB, embV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma exists_coords (T : Tor D) {x : VC D N N'} (hx : x ∈ LaB D T b) :
    ∃ c : Fin r → ℂ, (∀ i, c i ∈ T.abelian₂) ∧ x = ∑ i, c i • embV D T (b i) := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, j, rfl⟩ := hz
    refine ⟨Pi.single j w, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hw
      · simp [h]
    · rw [Finset.sum_eq_single j] <;> simp +contextual
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    exact ⟨c + c', fun i => add_mem (hc i) (hc' i), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨-c, fun i => neg_mem (hc i), by simp⟩

lemma neg_one_zpow_sum {ι : Type*} (s : Finset ι) (n : ι → ℤ) :
    (-1 : ℂ) ^ (∑ i ∈ s, n i) = ∏ i ∈ s, (-1 : ℂ) ^ n i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

lemma pullB_mem (htr : TraceMapNormalisation D) (hb : Orthonormal D b) (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hch : ∀ ω ∈ lamOf D cc δ, ∃ n : ℤ,
      (Real.sqrt D.host.d : ℂ) / 2 * (ω * starRingEnd ℂ ω / (area (lamOf D cc δ) : ℂ)) = n ∧
      ∀ z, (-1 : ℂ) ^ n * U1 (lamOf D cc δ) ω g z = g z) :
    pullB D (tor0 D cc δ) b g ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := by
  refine ⟨?_, fun x hx z => ?_⟩
  · unfold pullB
    have hd : ∀ j, Differentiable ℂ fun z : VC D N N' => g (coordB D (tor0 D cc δ) b j z) := fun j => by
      refine hg.comp ?_
      unfold coordB
      fun_prop
    exact fun z => (HasFDerivAt.finset_prod fun j _ => (hd j z).hasFDerivAt).differentiableAt
  · obtain ⟨c, hc, rfl⟩ := exists_coords _ hx
    choose n hn hU using fun i => hch (c i) (hc i)
    have hal : al D (tor0 D cc δ) (∑ i, c i • embV D (tor0 D cc δ) (b i)) = ∏ i, (-1 : ℂ) ^ n i := by
      rw [← neg_one_zpow_sum, al]
      congr 1
      have h1 : (Real.sqrt D.host.d : ℂ) / 2 * Hf D (tor0 D cc δ) (∑ i, c i • embV D (tor0 D cc δ) (b i))
          (∑ i, c i • embV D (tor0 D cc δ) (b i)) = ((∑ i, n i : ℤ) : ℂ) := by
        rw [Hf_sum, Finset.mul_sum]
        simp only [coordB_sum htr hb]
        push_cast
        exact Finset.sum_congr rfl fun i _ => hn i
      have h2 := congrArg Complex.re h1
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.re_ofReal_mul, Complex.intCast_re] at h2
      rw [h2, round_intCast]
    rw [hal, U, Hf_sum, Hf_sum]
    simp only [pullB, coordB_add, coordB_sum htr hb]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Complex.exp_sum,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hU i (coordB D (tor0 D cc δ) b i z), U1]
    congr 3
    change _ = -(Real.pi : ℂ) * _ * _ / (area (tor0 D cc δ).abelian₂ : ℂ) -
      _ * _ * _ / (2 * (area (tor0 D cc δ).abelian₂ : ℂ))
    ring

end Product

theorem pullbackOrthonormal_normalizedTheta_mem_thetaSpace (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (hc : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : Orthonormal D b) :
    pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := by
  obtain ⟨hl, -, -, -, hO⟩ := GlobalTheory.T.idealPeriodLattice_of_curveDatum D hD cc δ hc
  obtain ⟨⟨hdiff, -, -, hG⟩, -⟩ := GlobalTheory.T.oddThetaFunction_existence_uniqueness _ hl
  obtain ⟨w₁, w₂, hi, hl⟩ := hl
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  have h : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ (⟨w₁, w₂, hi⟩ : PeriodPair).lattice := fun z => by
    rw [hl, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp
  refine pullB_mem hD.2 hb _ ?_ fun ω hω => ?_
  · unfold GL3Theta.th0 U1
    fun_prop
  · obtain ⟨n, hn, hU⟩ := genus_one D _ _ h (fun w hw => ha ▸ hO a w hw) _ hG t0 ht ω hω
    refine ⟨n, hn, fun z => ?_⟩
    have := hU z
    rw [U1] at this
    rw [U1, GL3Theta.th0, GL3Theta.th0, ← this]
    ring

lemma Iop_mul (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N')) (κ : ℂ)
    (F : VC D N N' → ℂ) (z : VC D N N') :
    Iop D T A₁ A₂ (fun z => κ * F z) z = κ * Iop D T A₁ A₂ F z := by
  simp only [Iop, U]
  rw [mul_left_comm, ← smul_eq_mul κ, smul_finsum]
  congr 1
  refine finsum_congr fun q => ?_
  rw [smul_eq_mul]
  ring

lemma mod1All_mul {κ μ : ℂ} (hκ : Mod1All κ) (hμ : μ ^ 8 = 1) : Mod1All (κ * μ) := by
  obtain ⟨h1, h2⟩ := hκ
  have h3 : μ ∈ Qbar := by
    rw [mem_algebraicClosure_iff']
    exact IsIntegral.of_pow (n := 8) (by norm_num) (hμ ▸ isIntegral_one)
  refine ⟨mul_mem h1 h3, fun σ => ?_⟩
  have h4 : (⟨μ, h3⟩ : Qbar) ^ 8 = 1 := Subtype.ext hμ
  have h5 : ‖σ ⟨μ, h3⟩‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := 8) _ (by norm_num)
    rw [← map_pow, h4, map_one]
  change ‖σ (⟨κ, h1⟩ * ⟨μ, h3⟩)‖ = 1
  rw [map_mul, norm_mul, h2, h5, one_mul]

theorem isVacuum_thetaIntertwiner_selfDual : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  rintro D hD cc δ t0 hc ht a d L L' L₁ L₁' hL hL' hL₁ hL₁' G ⟨b, κ, hb, hκ, rfl⟩
  obtain ⟨μ, hμ, h⟩ := hD.mu cc δ hc a d _ _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩)
    (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _ (pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hD.g1 cc δ t0 hc ht b hb.1)
  refine ⟨b, κ * μ, hb, mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

end GlobalTheory.VacuumMove
