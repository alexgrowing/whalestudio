import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.CardUn
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.SplitPow
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DivAlg

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem isOpen_setOf_cycMod_eq_one (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (r : ℕ) :
    IsOpen {s : G ℚ Ω | cycMod ℚ Ω l r s = 1} := by
  have key : ∀ s : G ℚ Ω, cycMod ℚ Ω l r s = 1 ↔
      ((cycZ ℚ Ω l s : ℤ_[l])) ∈ Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(r : ℤ))) := by
    intro s
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, Units.ext_iff]
    simp [cycMod]
  have e : {s : G ℚ Ω | cycMod ℚ Ω l r s = 1} =
      (fun s => ((cycZ ℚ Ω l s : ℤ_[l]))) ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(r : ℤ))) :=
    Set.ext key
  rw [e]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : Nat.Prime l).pos
  exact (IsUltrametricDist.isOpen_closedBall _ (zpow_pos hl _).ne').preimage
    (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))

private theorem norm_natCast_prime_lt_one_qbar (l : ℕ) [Fact (Nat.Prime l)] : ‖(l : Qbar l)‖ < 1 := by
  show ‖(l : PadicAlgCl l)‖ < 1
  have h : ((l : ℚ_[l]) : PadicAlgCl l) = (l : PadicAlgCl l) := map_natCast _ l
  rw [← h, PadicAlgCl.norm_extends]
  first | exact padicNormE.norm_p_lt_one | exact Padic.norm_p_lt_one

private theorem red_un_succ (l : ℕ) [Fact (Nat.Prime l)] (r : ℕ) (g : ℕ) (hg : ¬ l ∣ g) :
    red l r (un g hg (r + 1)) = un g hg r := by
  ext
  simp [un, red, ZMod.unitOfCoprime, ZMod.cast_natCast (pow_dvd_pow l (Nat.le_succ r))]

private theorem red_cycMod_succ (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (r : ℕ)
    (s : G ℚ Ω) : red l r (cycMod ℚ Ω l (r + 1) s) = cycMod ℚ Ω l r s := by
  ext
  simp [cycMod, red, PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r)]

private theorem eta_one_of_one_le (l : ℕ) [Fact (Nat.Prime l)] (φ : DirichletCharacter (Qbar l) l) (k r : ℕ)
    (hr : 1 ≤ r) : eta φ k r 1 = 1 := by
  haveI : Fact (1 < l ^ r) := ⟨Nat.one_lt_pow (by omega) (Fact.out : Nat.Prime l).one_lt⟩
  simp [eta, ZMod.val_one]

private theorem cg_iff_norm_sub_le_norm_pow (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (a b : Qbar l) :
    Cg n a b ↔ ‖a - b‖ ≤ ‖(l : Qbar l) ^ n‖ := Iff.rfl

set_option maxHeartbeats 800000 in
theorem UpperTheory.Kd.C7.pDiv :
    UpperTheory.Kd.C7.SDiv := by
  intro l _ hl Ω _ _ _ A hA c Z hZ hC φ k hk hS
  obtain ⟨g, hg, hg2, hgen⟩ := UpperTheory.Kd.C7.pGenEx l hl
  obtain ⟨c₂, w, hw, hcob⟩ := UpperTheory.Kd.C7.pCob l hl Ω A hA c Z hZ φ k hk hS
  obtain ⟨hZint, hZcoc, hZnrm⟩ := hZ
  have hdiv := UpperTheory.Kd.C7.pDivAlg l c g hg hg2 hgen φ k hk
  obtain ⟨μ, hμ⟩ : ∃ μ : G ℚ Ω → (r : ℕ) → (ZMod (l ^ r))ˣ → Qbar l, ∀ s r x,
      μ s r x = (l : Qbar l) ^ c₂ * Z r s x -
        w * ((if x = cycMod ℚ Ω l r s then 1 else 0) - (if x = 1 then 1 else 0)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hOl : ((l : Qbar l) ^ c₂) ∈ c.O := Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ l) _
  have hμint : ∀ s ∈ Ine A, ∀ r x, μ s r x ∈ c.O := by
    intro s hs r x
    rw [hμ]
    refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hOl (hZint r s hs x)) (Subalgebra.mul_mem _ hw ?_)
    refine Subalgebra.sub_mem _ ?_ ?_ <;> split_ifs <;> simp
  have hsumind : ∀ r (y : (ZMod (l ^ r))ˣ) (a : (ZMod (l ^ (r + 1)))ˣ),
      ∑ x' with red l r x' = y, (if x' = a then (1 : Qbar l) else 0) = if y = red l r a then 1 else 0 := by
    intro r y a
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  have hμnrm : ∀ s ∈ Ine A, ∀ r x, μ s r x = ∑ x' with red l r x' = x, μ s (r + 1) x' := by
    intro s hs r x
    have e1 := hsumind r x (cycMod ℚ Ω l (r + 1) s)
    have e2 := hsumind r x 1
    rw [red_cycMod_succ] at e1
    rw [map_one] at e2
    simp only [hμ]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, e1, e2,
      ← hZnrm r s hs x]
  have heta : ∀ s ∈ Ine A, ∀ n, ∃ r₀, ∀ r, r₀ ≤ r → Cg n (∑ x, eta φ k r x * μ s r x) 0 := by
    intro s hs n
    obtain ⟨r₀, hr₀⟩ := hcob s hs n
    refine ⟨max r₀ 1, fun r hr => ?_⟩
    have h := hr₀ r (le_of_max_le_left hr)
    have hx : ∀ x, eta φ k r x * μ s r x = (l : Qbar l) ^ c₂ * (eta φ k r x * Z r s x) -
        w * (if x = cycMod ℚ Ω l r s then eta φ k r x else 0) +
        w * (if x = 1 then eta φ k r x else 0) := by
      intro x
      rw [hμ]
      split_ifs <;> ring
    have e : ∑ x, eta φ k r x * μ s r x =
        (l : Qbar l) ^ c₂ * sp (eta φ k r) (Z r) s - (eta φ k r (cycMod ℚ Ω l r s) - 1) * w := by
      rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), eta_one_of_one_le l φ k r (le_of_max_le_right hr)]
      simp only [sp]
      ring
    rw [cg_iff_norm_sub_le_norm_pow, sub_zero, e]
    rw [cg_iff_norm_sub_le_norm_pow] at h
    exact h
  have hex : ∀ s ∈ Ine A, ∀ r, ∃ q : (ZMod (l ^ r))ˣ → Qbar l, (∀ x, q x ∈ c.O) ∧
      ∀ x, μ s r x = q (x * un g hg r) - φ ↑g * ↑g ^ k * q x :=
    fun s hs => hdiv.2 (μ s) (hμint s hs) (hμnrm s hs) (heta s hs)
  obtain ⟨Z', hZ'⟩ : ∃ Z' : Sy Ω l, ∀ r, ∀ s ∈ Ine A, (∀ x, Z' r s x ∈ c.O) ∧
      ∀ x, μ s r x = Z' r s (x * un g hg r) - φ ↑g * ↑g ^ k * Z' r s x := by
    refine ⟨fun r s => @dite _ (s ∈ Ine A) (Classical.dec _) (fun h => Classical.choose (hex s h r)) (fun _ => fun _ => 0), ?_⟩
    intro r s hs
    simp only [dif_pos hs]
    exact Classical.choose_spec (hex s hs r)
  have inj : ∀ r (q : (ZMod (l ^ r))ˣ → Qbar l),
      (∀ x, q (x * un g hg r) - φ ↑g * ↑g ^ k * q x = 0) → ∀ x, q x = 0 := by
    intro r q hq x
    obtain ⟨c₃, hc₃⟩ := hdiv.1 r
    by_contra hne
    have hpos : 0 < ‖q x‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_natCast_prime_lt_one_qbar l)
    have h := hc₃ q n (fun y => by
      rw [cg_iff_norm_sub_le_norm_pow, hq y, sub_zero, norm_zero]
      exact norm_nonneg _) x
    rw [cg_iff_norm_sub_le_norm_pow, sub_zero, norm_pow] at h
    linarith
  have hIwI : IwI c A Z' := by
    refine ⟨fun r s hs x => (hZ' r s hs).1 x, ?_, ?_⟩
    · intro r s hs t ht x
      have hst : s * t ∈ Ine A := (Ine A).mul_mem hs ht
      have key := inj r (fun y => Z' r (s * t) y -
        (Z' r s y + Z' r t (y * (cycMod ℚ Ω l r s)⁻¹))) ?_ x
      · exact sub_eq_zero.mp key
      · intro y
        beta_reduce
        have e1 := (hZ' r (s * t) hst).2 y
        have e2 := (hZ' r s hs).2 y
        have e3 := (hZ' r t ht).2 (y * (cycMod ℚ Ω l r s)⁻¹)
        rw [mul_right_comm y (cycMod ℚ Ω l r s)⁻¹ (un g hg r)] at e3
        have e4 : μ (s * t) r y = μ s r y + μ t r (y * (cycMod ℚ Ω l r s)⁻¹) := by
          rw [hμ, hμ, hμ, hZcoc r s hs t ht y, map_mul]
          simp only [mul_inv_eq_iff_eq_mul, mul_inv_eq_one, one_mul,
            mul_comm (cycMod ℚ Ω l r t) (cycMod ℚ Ω l r s)]
          split_ifs <;> ring
        linear_combination -e1 + e2 + e3 + e4
    · intro r s hs x
      have key := inj r (fun y => Z' r s y - ∑ x' with red l r x' = y, Z' (r + 1) s x') ?_ x
      · exact sub_eq_zero.mp key
      · intro y
        beta_reduce
        have e1 := (hZ' r s hs).2 y
        have e2 := hμnrm s hs r y
        have e3 : ∑ x' with red l r x' = y * un g hg r, Z' (r + 1) s x' =
            ∑ x' with red l r x' = y, Z' (r + 1) s (x' * un g hg (r + 1)) := by
          symm
          refine Finset.sum_nbij' (· * un g hg (r + 1)) (· * (un g hg (r + 1))⁻¹) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            rw [map_mul, ha, red_un_succ]
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            rw [map_mul, map_inv, ha, red_un_succ, mul_inv_cancel_right]
          · intro a _
            simp
          · intro a _
            simp
          · intro a _
            rfl
        have e4 : ∑ x' with red l r x' = y, μ s (r + 1) x' =
            ∑ x' with red l r x' = y,
              (Z' (r + 1) s (x' * un g hg (r + 1)) - φ ↑g * ↑g ^ k * Z' (r + 1) s x') :=
          Finset.sum_congr rfl (fun x' _ => (hZ' (r + 1) s hs).2 x')
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at e4
        rw [e3]
        linear_combination -e1 + e2 + e4
  have hCont : UpperTheory.Kd.C7.Cont A Z' := by
    intro r n
    obtain ⟨c₃, hc₃⟩ := hdiv.1 r
    obtain ⟨U, hU, hUZ⟩ := hC r (n + c₃)
    refine ⟨U ⊓ (cycMod ℚ Ω l r).ker, ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      refine hU.inter ?_
      have hk' : ((cycMod ℚ Ω l r).ker : Set (G ℚ Ω)) = {s | cycMod ℚ Ω l r s = 1} := by
        ext s
        simp [MonoidHom.mem_ker]
      rw [hk']
      exact isOpen_setOf_cycMod_eq_one l Ω r
    · intro s hs hsI x
      rw [Subgroup.mem_inf] at hs
      obtain ⟨hsU, hsK⟩ := hs
      have hc1 : cycMod ℚ Ω l r s = 1 := hsK
      refine hc₃ (Z' r s) n (fun y => ?_) x
      rw [← (hZ' r s hsI).2 y, hμ, hc1, sub_self, mul_zero, sub_zero]
      have hz := hUZ s hsU hsI y
      rw [cg_iff_norm_sub_le_norm_pow, sub_zero] at hz ⊢
      rw [norm_mul]
      calc ‖(l : Qbar l) ^ c₂‖ * ‖Z r s y‖ ≤ 1 * ‖(l : Qbar l) ^ (n + c₃)‖ :=
            mul_le_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_natCast_prime_lt_one_qbar l).le) hz
              (norm_nonneg _) zero_le_one
        _ = ‖(l : Qbar l) ^ (n + c₃)‖ := one_mul _
  refine ⟨g, hg, c₂, Z', hIwI, hCont, ?_⟩
  intro m s hs x
  obtain ⟨hsI, hsK⟩ := hs
  have hc1 : cycMod ℚ Ω l m s = 1 := hsK
  have e := (hZ' m s hsI).2 x
  rw [hμ, hc1, sub_self, mul_zero, sub_zero] at e
  exact e
