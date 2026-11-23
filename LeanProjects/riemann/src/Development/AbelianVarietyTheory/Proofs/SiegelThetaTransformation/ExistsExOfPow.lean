import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBoundsStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.Vac

noncomputable section

variable {κ ι : Type} [Fintype κ] [Fintype ι]

def pr (x a : Matrix κ ι ℚ) : ℚ := ∑ k, x k ⬝ᵥ a k

theorem pr_comm (x a : Matrix κ ι ℚ) : pr x a = pr a x := by
  simp [pr, dotProduct_comm]

theorem pr_add_left (x y a : Matrix κ ι ℚ) : pr (x + y) a = pr x a + pr y a := by
  simp [pr, dotProduct, Finset.sum_add_distrib, add_mul]

theorem pr_smul_left (c : ℚ) (x a : Matrix κ ι ℚ) : pr (c • x) a = c * pr x a := by
  simp [pr, dotProduct, Finset.mul_sum, mul_assoc]

theorem pr_neg_left (x a : Matrix κ ι ℚ) : pr (-x) a = - pr x a := by
  simp [pr, dotProduct]

theorem pr_zero_left (a : Matrix κ ι ℚ) : pr 0 a = 0 := by
  simp [pr, dotProduct]

theorem pr_sub_left (x y a : Matrix κ ι ℚ) : pr (x - y) a = pr x a - pr y a := by
  rw [sub_eq_add_neg, pr_add_left, pr_neg_left, sub_eq_add_neg]

theorem pr_add_right (x y a : Matrix κ ι ℚ) : pr a (x + y) = pr a x + pr a y := by
  rw [pr_comm, pr_add_left, pr_comm x, pr_comm y]

theorem pr_smul_right (c : ℚ) (x a : Matrix κ ι ℚ) : pr a (c • x) = c * pr a x := by
  rw [pr_comm, pr_smul_left, pr_comm x]

theorem pr_zero_right (a : Matrix κ ι ℚ) : pr a 0 = 0 := by
  rw [pr_comm, pr_zero_left]

theorem pr_int {x a : Matrix κ ι ℚ} (hx : IntM x) (ha : IntM a) : ∃ m : ℤ, pr x a = m := by
  have : IsIntegral ℤ (pr x a) := by
    unfold pr dotProduct
    exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hx k i).mul (ha k i)
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 this
  exact ⟨m, by simpa using hm.symm⟩

theorem om_eq (y y' : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    (∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) = pr y.1 y'.2 - pr y'.1 y.2 := by
  simp [pr, Finset.sum_sub_distrib]

def ex (r : ℚ) : ℂ := cexp (π * I * (r : ℂ))

theorem ex_add (r s : ℚ) : ex (r + s) = ex r * ex s := by
  simp [ex, mul_add, Complex.exp_add]

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem ex_ne_zero (r : ℚ) : ex r ≠ 0 := Complex.exp_ne_zero _

theorem ex_two_eq_one {r : ℚ} (h : ex (2 * r) = 1) : ∃ m : ℤ, r = m := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have : (r : ℂ) = n := by
    apply mul_right_cancel₀ h2
    rw [← hn]; push_cast; ring
  exact_mod_cast this

theorem exists_ex_of_pow {z : ℂ} {m : ℕ} (hm : 0 < m) (h : z ^ m = 1) :
    ∃ r : ℚ, z * ex (2 * r) = 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp m hm.ne').eq_pow_of_pow_eq_one h
  refine ⟨-(i / m), ?_⟩
  rw [← hi, ex, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Complex.exp_zero]; congr 1
  push_cast; field_simp; ring

theorem heisS_apply [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ) (x : Matrix κ ι ℚ) :
    heisS a b φ x = φ (x - b) * ex (2 * pr x a - pr a b) := by
  simp only [heisS, ex, pr, Finset.sum_sub_distrib, Finset.mul_sum]

theorem exists_pr (f : Matrix κ ι ℚ →ₗ[ℤ] ℚ) : ∃ x, ∀ v, f v = pr x v := by
  classical
  let g : Matrix κ ι ℚ →ₗ[ℚ] ℚ := f.toAddMonoidHom.toRatLinearMap
  refine ⟨fun k i => g (Matrix.single k i 1), fun v => ?_⟩
  change g v = _
  conv_lhs => rw [Matrix.matrix_eq_sum_single v]
  simp only [map_sum, pr, dotProduct]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  have : Matrix.single k i (v k i) = v k i • Matrix.single k i (1 : ℚ) := by
    simp [Matrix.smul_single]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem exists_graph (Γ : AddSubgroup (Matrix κ ι ℚ × ℚ)) (M : AddSubgroup (Matrix κ ι ℚ))
    (hM : M.FG) (hΓ : ∀ p ∈ Γ, p.1 ∈ M) : ∃ x, ∀ p ∈ Γ, (p.1, pr x p.1) ∈ Γ := by
  let G : Submodule ℤ (Matrix κ ι ℚ × ℚ) := Γ.toIntSubmodule
  let q : G →ₗ[ℤ] Matrix κ ι ℚ := (LinearMap.fst ℤ _ _).comp G.subtype
  have hM' : (M.toIntSubmodule).FG := (Submodule.fg_iff_addSubgroup_fg _).2 (by simpa using hM)
  have hfg : (LinearMap.range q).FG := by
    refine hM'.of_le ?_
    rintro _ ⟨p, rfl⟩
    exact hΓ p.1 p.2
  haveI : Module.Finite ℤ (LinearMap.range q) := Module.Finite.iff_fg.2 hfg
  haveI : Module.IsTorsionFree ℤ (Matrix κ ι ℚ) :=
    inferInstanceAs (Module.IsTorsionFree ℤ (κ → ι → ℚ))
  haveI : Module.Free ℤ (LinearMap.range q) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q.rangeRestrict LinearMap.id
    q.surjective_rangeRestrict
  have hB : Module.Baer ℤ ℚ := Module.Baer.of_divisible ℚ
  obtain ⟨f, hf⟩ := hB.extension_property (LinearMap.range q).subtype
    (Submodule.injective_subtype _) (((LinearMap.snd ℤ _ _).comp G.subtype).comp s)
  obtain ⟨x, hx⟩ := exists_pr f
  refine ⟨x, fun p hp => ?_⟩
  let u : LinearMap.range q := ⟨p.1, ⟨p, hp⟩, rfl⟩
  have h1 : (s u).1.1 = p.1 := congrArg Subtype.val (LinearMap.congr_fun hs u)
  have h2 : (s u).1.2 = pr x p.1 := by
    rw [← hx]; exact (LinearMap.congr_fun hf u).symm
  have : (p.1, pr x p.1) = (s u).1 := Prod.ext h1.symm h2.symm
  rw [this]; exact (s u).2

omit [Fintype κ] [Fintype ι] in
theorem intM_smul {x : Matrix κ ι ℚ} (n : ℕ) (h : IntM x) : IntM ((n : ℚ) • x) := by
  intro k i
  have := (h k i).nsmul n
  simpa [nsmul_eq_mul] using this

theorem exists_den (x : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • x) := by
  classical
  refine ⟨∏ p : κ × ι, (x p.1 p.2).den, Finset.prod_pos fun p _ => (x p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : κ × ι => (x p.1 p.2).den)
    (Finset.mem_univ (k, i))
  rw [hc]
  have : (((x k i).den * c : ℕ) : ℚ) * x k i = ((c * (x k i).num : ℤ) : ℚ) := by
    push_cast; rw [← Rat.den_mul_eq_num]; ring
  simp only [Matrix.smul_apply, smul_eq_mul, this]
  exact isIntegral_algebraMap (R := ℤ)

theorem exists_den_fg (M : AddSubgroup (Matrix κ ι ℚ)) (hM : M.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, IntM ((N : ℚ) • x) := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose d hd hd' using fun x : Matrix κ ι ℚ => exists_den x
  refine ⟨∏ x ∈ S, d x, Finset.prod_pos fun x _ => hd x, fun x hx => ?_⟩
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_coe.1 hx)
    rw [hc, mul_comm, Nat.cast_mul, mul_smul]
    exact intM_smul c (hd' x)
  | zero => intro k i; simpa using isIntegral_zero
  | add x y _ _ hx hy => intro k i; rw [smul_add]; exact (hx k i).add (hy k i)
  | neg x _ hx => intro k i; rw [smul_neg]; exact (hx k i).neg

theorem ip_smul_self (c : ℂ) (hc : c ≠ 0) (φ : Matrix κ ι ℚ → ℂ) :
    ip (c • φ) (c • φ) = c * conj c * ip φ φ := by
  have hcc : c * conj c ≠ 0 := mul_ne_zero hc (by simpa using hc)
  have key : ∀ (d : ℂ), d ≠ 0 → ∀ ψ : Matrix κ ι ℚ → ℂ, haar (fun x => d * ψ x) = d * haar ψ := by
    intro d hd ψ
    have hp : (fun R : ℕ => 0 < R ∧ HasLevel R (fun x => d * ψ x)) =
        fun R : ℕ => 0 < R ∧ HasLevel R ψ := by
      funext R; simp [HasLevel, hd]
    have hch : ∀ (p q : ℕ → Prop) (h : ∃ R, p R) (h' : ∃ R, q R), p = q → h.choose = h'.choose := by
      intro p q h h' e; subst e; rfl
    have hiff : IsSB (fun x => d * ψ x) ↔ IsSB ψ := by
      unfold IsSB; rw [hp]
    unfold haar
    by_cases h : IsSB ψ
    · rw [dif_pos h, dif_pos (hiff.2 h), hch _ _ (hiff.2 h) h hp]
      unfold haarAt
      rw [← mul_finsum]; ring
    · rw [dif_neg h, dif_neg (mt hiff.1 h), mul_zero]
  unfold ip
  rw [← key _ hcc]
  congr 1; funext x; simp; ring

theorem fg_map {G G' : Type} [AddCommGroup G] [AddCommGroup G'] {A : AddSubgroup G} (hA : A.FG)
    (f : G →+ G') : (A.map f).FG := by
  classical
  obtain ⟨S, rfl⟩ := hA
  exact ⟨S.image f, by rw [AddMonoidHom.map_closure, Finset.coe_image]⟩

def fac (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) (y : Matrix κ ι ℚ × Matrix κ ι ℚ)
    (x : Matrix κ ι ℚ) : ℂ := ε y * ex (2 * pr x y.1 - pr y.1 y.2)

theorem fixed_iff [DecidableEq ι] (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ)
    (y : Matrix κ ι ℚ × Matrix κ ι ℚ) (w : Matrix κ ι ℚ → ℂ) :
    ε y • heisS y.1 y.2 w = w ↔ ∀ x, fac ε y x * w (x - y.2) = w x := by
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [Pi.smul_apply, heisS_apply, fac, smul_eq_mul]
  constructor <;> intro h <;> rw [← h] <;> ring

theorem fac_add {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ} {y y' : Matrix κ ι ℚ × Matrix κ ι ℚ}
    (h : ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2)) (x : Matrix κ ι ℚ) :
    fac ε (y + y') x = fac ε y x * fac ε y' (x - y.2) := by
  unfold fac
  rw [h, mul_assoc, ← ex_add, mul_mul_mul_comm, ← ex_add]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, pr_add_left, pr_add_right, pr_sub_left, pr_comm y.2 y'.1]
  ring

theorem exists_base (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ))
    (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) (hA : A.FG)
    (hε : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2))
    {m : ℕ} (hm : 0 < m) (hm' : ∀ y ∈ A, ε (m • y) = 1) :
    ∃ x₀, ∀ a, (a, 0) ∈ A → ε (a, 0) * ex (2 * pr x₀ a) = 1 := by
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  have hadd : ∀ a a', (a, 0) ∈ A → (a', 0) ∈ A → ε (a + a', 0) = ε (a, 0) * ε (a', 0) := by
    intro a a' h h'
    simpa [pr_zero_right, ex_zero] using hε _ h _ h'
  let Γ : AddSubgroup (Matrix κ ι ℚ × ℚ) :=
    { carrier := {p | (p.1, 0) ∈ A ∧ ε (p.1, 0) * ex (2 * p.2) = 1}
      zero_mem' := ⟨A.zero_mem, by
        have : ε (0, 0) = 1 := h0
        simp [this, ex_zero]⟩
      add_mem' := by
        rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
        refine ⟨by simpa using A.add_mem hp hq, ?_⟩
        rw [Prod.fst_add, Prod.snd_add, hadd _ _ hp hq, mul_add, ex_add, mul_mul_mul_comm, hp', hq',
          one_mul]
      neg_mem' := by
        rintro p ⟨hp, hp'⟩
        have hn : (-p.1, 0) ∈ A := by simpa using A.neg_mem hp
        refine ⟨hn, ?_⟩
        have h1 := hadd _ _ hp hn
        have h2 := ex_add (2 * p.2) (2 * -p.2)
        rw [add_neg_cancel] at h1
        have h3 : ε (0, 0) = 1 := h0
        rw [h3] at h1
        rw [show 2 * p.2 + 2 * -p.2 = 0 by ring, ex_zero] at h2
        change ε (-p.1, 0) * ex (2 * -p.2) = 1
        calc _ = (ε (p.1, 0) * ex (2 * p.2)) * (ε (-p.1, 0) * ex (2 * -p.2)) := by
              rw [hp', one_mul]
          _ = 1 := by rw [mul_mul_mul_comm, ← h1, ← h2, one_mul] }
  obtain ⟨x, hx⟩ := exists_graph Γ (A.map (AddMonoidHom.fst _ _)) (fg_map hA _)
    (fun p hp => ⟨_, hp.1, rfl⟩)
  refine ⟨x, fun a ha => ?_⟩
  have hpow : ∀ n : ℕ, ε (n • a, 0) = ε (a, 0) ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact h0
    | succ n ih =>
      rw [succ_nsmul, hadd _ _ (by simpa using A.nsmul_mem ha n) ha, ih, pow_succ]
  have : ε (a, 0) ^ m = 1 := by
    rw [← hpow]; simpa using hm' _ ha
  obtain ⟨r, hr⟩ := exists_ex_of_pow hm this
  exact (hx (a, r) ⟨ha, hr⟩).2

theorem exists_lift (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)) (hA : A.FG)
    (hd : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, pr y.1 y'.2 - pr y'.1 y.2 = m) (b : Matrix κ ι ℚ)
    (hb : ∀ a, (a, 0) ∈ A → ∃ m : ℤ, pr b a = m) : ∃ a, (a, b) ∈ A := by
  let Γ : AddSubgroup (Matrix κ ι ℚ × ℚ) :=
    { carrier := {p | ∃ y ∈ A, y.2 = p.1 ∧ ∃ m : ℤ, p.2 - pr y.1 b = m}
      zero_mem' := ⟨0, A.zero_mem, rfl, 0, by simp [pr_zero_left]⟩
      add_mem' := by
        rintro p q ⟨y, hy, e, m, hm⟩ ⟨y', hy', e', m', hm'⟩
        refine ⟨y + y', A.add_mem hy hy', by simp [e, e'], m + m', ?_⟩
        rw [Prod.fst_add, Prod.snd_add, pr_add_left]; push_cast; linarith
      neg_mem' := by
        rintro p ⟨y, hy, e, m, hm⟩
        refine ⟨-y, A.neg_mem hy, by simp [e], -m, ?_⟩
        rw [Prod.fst_neg, Prod.snd_neg, pr_neg_left]; push_cast; linarith }
  obtain ⟨x, hx⟩ := exists_graph Γ (A.map (AddMonoidHom.snd _ _)) (fg_map hA _)
    (by rintro p ⟨y, hy, e, -⟩; exact ⟨y, hy, e⟩)
  refine ⟨x, (hd _).2 fun y hy => ?_⟩
  obtain ⟨y', hy', e, m, hm⟩ := hx (y.2, pr y.1 b) ⟨y, hy, rfl, 0, by simp⟩
  have hmem : (y'.1 - y.1, 0) ∈ A := by
    have : y' - y = (y'.1 - y.1, 0) := Prod.ext rfl (by simp [e])
    rw [← this]; exact A.sub_mem hy' hy
  obtain ⟨n, hn⟩ := hb _ hmem
  rw [pr_comm, pr_sub_left] at hn
  refine ⟨m + n, ?_⟩
  simp only at hm ⊢
  push_cast; linarith

theorem vacuum (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)) (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) : A.FG → (∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, (∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) = m) → (∀ y ∈ A, ‖ε y‖ = 1) → (∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * cexp (π * I * ((∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) : ℂ))) → (∃ m : ℕ, 0 < m ∧ ∀ y ∈ A, ε (m • y) = 1) → ∃ v : Matrix κ ι ℚ → ℂ, IsSB v ∧ ip v v = 1 ∧ (∀ y ∈ A, ε y • heisS y.1 y.2 v = v) ∧ ∀ w, IsSB w → (∀ y ∈ A, ε y • heisS y.1 y.2 w = w) → ∃ c : ℂ, w = c • v := by
  classical
  intro hA hd hnorm hε ⟨m, hm, hm'⟩
  simp only [om_eq] at hd hε
  replace hε : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2) := hε
  have hn : ∀ y ∈ A, ε y ≠ 0 := fun y hy h => by simpa [h] using hnorm y hy
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  obtain ⟨x₀, hx₀⟩ := exists_base A ε hA hε hm hm'
  simp only [fixed_iff]
  let v : Matrix κ ι ℚ → ℂ := fun x =>
    if h : ∃ y ∈ A, x = x₀ + y.2 then fac ε h.choose x else 0
  have hv : ∀ y ∈ A, v (x₀ + y.2) = fac ε y (x₀ + y.2) := by
    intro y hy
    have h : ∃ y' ∈ A, x₀ + y.2 = x₀ + y'.2 := ⟨y, hy, rfl⟩
    have e : v (x₀ + y.2) = fac ε h.choose (x₀ + y.2) := dif_pos h
    obtain ⟨hy', e'⟩ := h.choose_spec
    rw [e]
    generalize h.choose = y' at hy' e'
    have e2 : y' = y + (y'.1 - y.1, 0) := Prod.ext (by simp) (by simpa using e'.symm)
    have hmem : (y'.1 - y.1, 0) ∈ A := by
      have : (y'.1 - y.1, 0) = y' - y := by rw [eq_sub_iff_add_eq, add_comm]; exact e2.symm
      rw [this]; exact A.sub_mem hy' hy
    rw [e2, fac_add (hε _ hy _ hmem), add_sub_cancel_right]
    have : fac ε (y'.1 - y.1, 0) x₀ = 1 := by
      rw [← hx₀ _ hmem, fac, pr_zero_right, sub_zero]
    rw [this, mul_one]
  have hv0 : ∀ x, (¬ ∃ y ∈ A, x = x₀ + y.2) → v x = 0 := fun x h => dif_neg h
  have hvx : v x₀ = 1 := by
    have := hv 0 A.zero_mem
    simpa [fac, h0, pr_zero_right, ex_zero] using this
  have hfix : ∀ y ∈ A, ∀ x, fac ε y x * v (x - y.2) = v x := by
    intro y hy x
    by_cases h : ∃ y' ∈ A, x = x₀ + y'.2
    · obtain ⟨y', hy', rfl⟩ := h
      have e : x₀ + y'.2 - y.2 = x₀ + (y' - y).2 := by simp [add_sub_assoc]
      rw [hv _ hy', e, hv _ (A.sub_mem hy' hy), ← e, ← fac_add (hε _ hy _ (A.sub_mem hy' hy)),
        add_sub_cancel]
    · rw [hv0 _ h, hv0, mul_zero]
      rintro ⟨y', hy', e⟩
      exact h ⟨y' + y, A.add_mem hy' hy, by rw [Prod.snd_add, ← add_assoc, ← e, sub_add_cancel]⟩
  have huniq : ∀ w : Matrix κ ι ℚ → ℂ, (∀ y ∈ A, ∀ x, fac ε y x * w (x - y.2) = w x) →
      w = w x₀ • v := by
    intro w hw
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases h : ∃ y' ∈ A, x = x₀ + y'.2
    · obtain ⟨y, hy, rfl⟩ := h
      rw [hv _ hy, ← hw y hy, add_sub_cancel_right, mul_comm]
    · rw [hv0 _ h, mul_zero]
      by_contra hne
      apply h
      obtain ⟨a, ha⟩ := exists_lift A hA hd (x - x₀) fun a ha => by
        have h1 := hw _ ha x
        simp only [sub_zero, fac, pr_zero_right] at h1
        have h2 : ε (a, 0) * ex (2 * pr x a) = 1 := by
          apply mul_right_cancel₀ hne; rw [h1, one_mul]
        apply ex_two_eq_one
        apply mul_left_cancel₀ (mul_ne_zero (hn _ ha) (ex_ne_zero (2 * pr x₀ a)))
        rw [mul_assoc, ← ex_add, pr_sub_left, hx₀ _ ha, mul_one, ← h2]
        congr 2; ring
      exact ⟨_, ha, by simp⟩
  obtain ⟨N₁, hN₁, hN₁'⟩ := exists_den_fg (A.map (AddMonoidHom.fst _ _)) (fg_map hA _)
  obtain ⟨N₂, hN₂, hN₂'⟩ := exists_den_fg (A.map (AddMonoidHom.snd _ _)) (fg_map hA _)
  obtain ⟨D, hD, hD'⟩ := exists_den x₀
  have hR : 0 < m * N₁ * N₂ * D := by positivity
  have hlev : HasLevel (m * N₁ * N₂ * D) v := by
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ A, x = x₀ + y.2 := by
        by_contra h; exact hx (hv0 _ h)
      have h1 := intM_smul (m * N₁ * N₂) hD'
      have h2 := intM_smul (m * N₁ * D) (hN₂' y.2 ⟨y, hy, rfl⟩)
      rw [smul_smul] at h1 h2
      have e1 : ((m * N₁ * N₂ : ℕ) : ℚ) * D = ((m * N₁ * N₂ * D : ℕ) : ℚ) := by push_cast; ring
      have e2 : ((m * N₁ * D : ℕ) : ℚ) * N₂ = ((m * N₁ * N₂ * D : ℕ) : ℚ) := by push_cast; ring
      rw [e1] at h1; rw [e2] at h2
      intro k i
      rw [smul_add]
      exact (h1 k i).add (h2 k i)
    · intro x z hz
      have hz' := intM_smul (N₂ * D) hz
      have hmem : ((0 : Matrix κ ι ℚ), (N₁ : ℚ) • ((N₂ * D : ℕ) : ℚ) • z) ∈ A := by
        refine (hd _).2 fun y hy => ?_
        obtain ⟨n, hn⟩ := pr_int (hN₁' y.1 ⟨y, hy, rfl⟩) hz'
        refine ⟨-n, ?_⟩
        rw [pr_smul_left] at hn
        simp only [pr_zero_left]
        rw [pr_smul_right, hn]; simp
      have e : m • ((0 : Matrix κ ι ℚ), (N₁ : ℚ) • ((N₂ * D : ℕ) : ℚ) • z) =
          (0, ((m * N₁ * N₂ * D : ℕ) : ℚ) • z) := by
        refine Prod.ext (by simp) ?_
        rw [Prod.smul_snd, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
        congr 1; push_cast; ring
      have h1 := hm' _ hmem
      have h2 := hfix _ (A.nsmul_mem hmem m) (x + ((m * N₁ * N₂ * D : ℕ) : ℚ) • z)
      rw [e] at h1 h2
      rw [← h2, fac, h1]
      simp [pr_zero_left, pr_zero_right, ex_zero]
  obtain ⟨him, hre, hsup, -⟩ := GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds ℚ κ ι _ v hR hlev
  have hpos : 0 < (ip v v).re := by
    refine lt_of_le_of_ne hre fun h => ?_
    have := hsup x₀
    rw [← h, hvx] at this
    norm_num at this
  set t : ℝ := (ip v v).re with ht
  have hip : ip v v = (t : ℂ) := Complex.ext rfl (by simpa using him)
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 hpos
  have hc : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hs).ne'
  refine ⟨(((Real.sqrt t)⁻¹ : ℝ) : ℂ) • v, ⟨_, hR, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact hlev.1 x fun h => hx (by simp [h])
  · intro x z hz
    simp only [Pi.smul_apply, hlev.2 x z hz]
  · rw [ip_smul_self _ hc, hip, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
  · intro y hy x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hfix y hy x]
  · intro w _ hw
    refine ⟨w x₀ * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)⁻¹, ?_⟩
    rw [smul_smul, inv_mul_cancel_right₀ hc]
    exact huniq w hw

end

end GlobalTheory.SW.Vac
