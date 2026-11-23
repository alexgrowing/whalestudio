import Mathlib

noncomputable section

namespace GlobalTheory.K5

open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev Lau : Type := LaurentSeries ℤ_[p]

abbrev pI : Ideal (Lau p) := Ideal.span {(p : Lau p)}

abbrev O0 : Type := AdicCompletion (pI p) (Lau p)

def qO : O0 p := algebraMap (Lau p) (O0 p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]))

def towerIdeal (n : ℕ) : Ideal (Polynomial (Polynomial (O0 p))) :=
  Ideal.span {C (cyclotomic (p ^ n) (O0 p)), X ^ (p ^ n) - C (C (qO p))}

abbrev On (n : ℕ) : Type := Polynomial (Polynomial (O0 p)) ⧸ towerIdeal p n

def xn (n : ℕ) : On p n := Ideal.Quotient.mk _ (C X)

def yn (n : ℕ) : On p n := Ideal.Quotient.mk _ X

def IsDlog (n : ℕ) (w α β : On p n) : Prop :=
  (xn p n * yn p n) • KaehlerDifferential.D (O0 p) (On p n) w =
    (w * xn p n * α) • KaehlerDifferential.D (O0 p) (On p n) (yn p n) +
    (w * yn p n * β) • KaehlerDifferential.D (O0 p) (On p n) (xn p n)

def fPi (n : ℕ) (k l : ℤ) (α β α' β' : On p n) : On p n :=
  α * ((l : On p n) * xn p n + (xn p n - 1) * β') - ((k : On p n) * xn p n + (xn p n - 1) * β) * α'

structure IsClo (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Prop where
  inj : Function.Injective (algebraMap (O0 p) Ω)
  alg : Algebra.IsAlgebraic (O0 p) Ω
  clo : IsAlgClosed Ω

structure Tower (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] where
  ζ : ℕ → Ω
  qq : ℕ → Ω
  prim : ∀ n, IsPrimitiveRoot (ζ n) (p ^ n)
  ζpow : ∀ n, ζ (n + 1) ^ p = ζ n
  q0 : qq 0 = algebraMap (O0 p) Ω (qO p)
  qpow : ∀ n, qq (n + 1) ^ p = qq n

abbrev Gal (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ := Ω ≃ₐ[O0 p] Ω

variable {p}
variable {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def Gn (T : Tower p Ω) (n : ℕ) : Subgroup (Gal p Ω) :=
  MulAction.stabilizer (Gal p Ω) (T.ζ n) ⊓ MulAction.stabilizer (Gal p Ω) (T.qq n)

def IsEmb (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) : Prop :=
  ι (xn p n) = T.ζ n ∧ ι (yn p n) = T.qq n

variable (p) in

def IsInt (x : Ω) : Prop := IsIntegral (O0 p) x

variable (p) in

def Cong (k : ℕ) (x y : Ω) : Prop := ∃ z : Ω, IsInt p z ∧ x - y = (p : Ω) ^ k * z

def IsKum (T : Tower p Ω) (n : ℕ) (H : Subgroup (Gal p Ω)) (r : Ω) (a : Gal p Ω → ZMod (p ^ n)) : Prop :=
  ∀ g ∈ H, g r = T.ζ n ^ (a g).val * r

def Gms (T : Tower p Ω) (m s : ℕ) : Subgroup (Gal p Ω) :=
  MulAction.stabilizer (Gal p Ω) (T.ζ m) ⊓ MulAction.stabilizer (Gal p Ω) (T.qq s)

variable (p) in

def IsAlgZp (x : Ω) : Prop :=
  ∃ P : Polynomial ℤ_[p], P ≠ 0 ∧ Polynomial.aeval x (P.map (algebraMap ℤ_[p] (O0 p))) = 0

variable (p) in

def Ggeo (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Subgroup (Gal p Ω) where
  carrier := {g | ∀ x : Ω, IsAlgZp p x → g x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    show a (b x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    show a.symm x = x
    conv_lhs => rw [← ha x hx]
    exact a.symm_apply_apply x

def LocallyConstantOneCochain (k : ℕ) (w : Gal p Ω → Ω) : Prop :=
  (∀ g, IsInt p (w g)) ∧ ∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → Cong p k (w h) (w g)

def Cob2 (k : ℕ) (H : Subgroup (Gal p Ω)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, LocallyConstantOneCochain k w ∧ ∀ g ∈ H, ∀ h ∈ H, Cong p k (ξ g h) (g (w h) - w (g * h) + w g)

def Cob1 (k : ℕ) (H : Subgroup (Gal p Ω)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt p x ∧ ∀ g ∈ H, Cong p k (c g) (g x - x)

end GlobalTheory.K5

namespace GlobalTheory.K5.Basic

open Polynomial

section Ring

variable (p : ℕ) [hp : Fact p.Prime]

theorem natCast_pow_dvd_iff (k : ℕ) (f : Lau p) :
    (p : Lau p) ^ k ∣ f ↔ ∀ n, (p : ℤ_[p]) ^ k ∣ f.coeff n := by
  have hc : (p : Lau p) ^ k = HahnSeries.C ((p : ℤ_[p]) ^ k) := by rw [map_pow, map_natCast]
  have hne : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [hc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
    exact Dvd.intro _ rfl
  · intro h
    choose c hcn using h
    refine ⟨⟨c, f.isPWO_support'.mono ?_⟩, ?_⟩
    · intro n hn
      simp only [Function.mem_support] at hn ⊢
      rw [hcn n]
      exact mul_ne_zero hne hn
    · ext n
      rw [hc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hcn n]
      rfl

theorem dvd_iff_map (f : Lau p) :
    (p : Lau p) ∣ f ↔ f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
  have := natCast_pow_dvd_iff p 1 f
  simp only [pow_one] at this
  rw [this]
  have key : ∀ c : ℤ_[p], (p : ℤ_[p]) ∣ c ↔ PadicInt.toZMod c = 0 := by
    intro c
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  constructor
  · intro h; ext n; exact (key _).1 (h n)
  · intro h n
    have := congrArg (fun s => HahnSeries.coeff s n) h
    exact (key _).2 this

theorem prime_lau : Prime (p : Lau p) := by
  refine ⟨?_, ?_, ?_⟩
  · have hc : (p : Lau p) = HahnSeries.C (p : ℤ_[p]) := by simp
    rw [hc]
    exact HahnSeries.C_ne_zero (by exact_mod_cast hp.out.ne_zero)
  · intro hu
    have h1 := (dvd_iff_map p 1).1 hu.dvd
    have := congrArg (fun s => HahnSeries.coeff s 0) h1
    have h2 : PadicInt.toZMod (p := p) (HahnSeries.coeff (1 : Lau p) 0) = 0 := this
    simp at h2
  · intro a b h
    rw [dvd_iff_map, HahnSeries.map_mul] at h
    rw [dvd_iff_map, dvd_iff_map]
    exact mul_eq_zero.1 h

theorem mem_pI_pow (k : ℕ) (f : Lau p) : f ∈ pI p ^ k ↔ (p : Lau p) ^ k ∣ f := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem seq_sub_dvd (x : AdicCompletion.AdicCauchySequence (pI p) (Lau p)) {m n : ℕ} (h : m ≤ n) :
    (p : Lau p) ^ m ∣ x.1 n - x.1 m := by
  have h1 := AdicCompletion.AdicCauchySequence.mk_eq_mk h x
  rw [Submodule.Quotient.eq] at h1
  rw [← mem_pI_pow]
  simpa using h1

theorem exists_not_dvd (x : AdicCompletion.AdicCauchySequence (pI p) (Lau p))
    (hx : AdicCompletion.mk (pI p) (Lau p) x ≠ 0) :
    ∃ a, ∀ n, a ≤ n → ¬ (p : Lau p) ^ a ∣ x.1 n := by
  by_contra hcon
  push_neg at hcon
  apply hx
  apply AdicCompletion.ext_evalₐ
  intro a
  obtain ⟨n, hn, hd⟩ := hcon a
  rw [AdicCompletion.evalₐ_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow]
  have := dvd_sub hd (seq_sub_dvd p x hn)
  simpa using this

instance charZero_completed_ring : CharZero (O0 p) := by
  refine charZero_of_inj_zero ?_
  intro n hn
  have h1 := congrArg (AdicCompletion.evalₐ (pI p) n) hn
  rw [map_natCast, map_zero, ← map_natCast (Ideal.Quotient.mk (pI p ^ n)),
    Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow, natCast_pow_dvd_iff] at h1
  have h2 := h1 0
  have hc : (n : Lau p) = HahnSeries.C (n : ℤ_[p]) := by rw [map_natCast]
  rw [hc, HahnSeries.C_apply, HahnSeries.coeff_single_same] at h2
  have h3 : ((p : ℤ) ^ n) ∣ (n : ℤ) :=
    (PadicInt.pow_p_dvd_int_iff n (n : ℤ)).1 (by exact_mod_cast h2)
  have h4 : p ^ n ∣ n := by exact_mod_cast h3
  exact Nat.eq_zero_of_dvd_of_lt h4 (Nat.lt_pow_self hp.out.one_lt)

instance isDomain_completed_ring : IsDomain (O0 p) := by
  haveI : NoZeroDivisors (O0 p) := ⟨by
    intro x y hxy
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
    obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) y
    obtain ⟨a, ha⟩ := exists_not_dvd p x hx
    obtain ⟨b, hb⟩ := exists_not_dvd p y hy
    have h1 := congrArg (AdicCompletion.evalₐ (pI p) (a + b)) hxy
    rw [map_mul, map_zero, AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow, pow_dvd_iff_le_emultiplicity,
      emultiplicity_mul (prime_lau p)] at h1
    have h2 := ha (a + b) (Nat.le_add_right _ _)
    have h3 := hb (a + b) (Nat.le_add_left _ _)
    rw [pow_dvd_iff_le_emultiplicity, not_le] at h2 h3
    have h4 := ENat.add_lt_add h2 h3
    rw [← Nat.cast_add] at h4
    exact absurd h1 (not_le.2 h4)⟩
  exact NoZeroDivisors.to_isDomain _

theorem not_isUnit_p : ¬ IsUnit (p : O0 p) := by
  intro h
  have h2 := h.map (AdicCompletion.evalₐ (pI p) 1)
  haveI : (pI p ^ 1).IsPrime := by
    rw [pow_one]; exact (Ideal.span_singleton_prime (prime_lau p).ne_zero).2 (prime_lau p)
  refine h2.ne_zero ?_
  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (pI p ^ 1)), Ideal.Quotient.eq_zero_iff_mem,
    pow_one]
  exact Ideal.mem_span_singleton_self _

theorem isUnit_qO : IsUnit (qO p) := by
  refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
  rw [HahnSeries.single_mul_single]; simp [HahnSeries.single_zero_one]

theorem isClo_algebraicClosure : IsClo p (AlgebraicClosure (FractionRing (O0 p))) where
  inj := by
    rw [IsScalarTower.algebraMap_eq (O0 p) (FractionRing (O0 p))]
    exact (algebraMap (FractionRing (O0 p)) _).injective.comp (IsFractionRing.injective _ _)
  alg := (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).2
    inferInstance
  clo := inferInstance

theorem isDlog_yn (n : ℕ) : IsDlog p n (yn p n) 1 0 := by
  simp [IsDlog, mul_comm]

theorem isDlog_xn (n : ℕ) : IsDlog p n (xn p n) 0 1 := by
  simp [IsDlog]

theorem fPi_yn_xn (n : ℕ) : fPi p n 0 0 1 0 0 1 = xn p n - 1 := by simp [fPi]

theorem fPi_swap (n : ℕ) (k l : ℤ) (α β α' β' : On p n) :
    fPi p n l k α' β' α β = - fPi p n k l α β α' β' := by simp only [fPi]; ring

end Ring

section Field

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem charZero_of_isClo (h : IsClo p Ω) : CharZero Ω :=
  charZero_of_injective_algebraMap h.inj

theorem tw_prim_step {Ω : Type*} [Field Ω] {ζ z : Ω} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) (hz : z ^ p = ζ) :
    IsPrimitiveRoot z (p ^ (n + 2)) := by
  have h1 : z ^ (p ^ (n + 2)) = 1 := by
    rw [pow_succ' p (n + 1), pow_mul, hz, hζ.pow_eq_one]
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h1)
  rcases Nat.lt_or_ge k (n + 2) with hlt | hge
  · exfalso
    have h2 : z ^ (p ^ (n + 1)) = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.1
      rw [hko]
      exact pow_dvd_pow p (by omega)
    have h3 : ζ ^ (p ^ n) = 1 := by
      rw [← hz, ← pow_mul, ← pow_succ']
      exact h2
    have h4 := hζ.dvd_of_pow_eq_one _ h3
    rw [Nat.pow_dvd_pow_iff_le_right hp.out.one_lt] at h4
    omega
  · have hk2 : k = n + 2 := le_antisymm hk hge
    rw [← hk2, ← hko]
    exact IsPrimitiveRoot.orderOf z

theorem tw_exists_prim_p (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ z : Ω, IsPrimitiveRoot z p := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic p Ω)
    (ne_of_gt (degree_cyclotomic_pos p Ω hp.out.pos))
  exact ⟨z, (isRoot_cyclotomic_iff).1 hz⟩

theorem tw_exists_root_chain {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (a : Ω) :
    ∃ f : ℕ → Ω, f 0 = a ∧ ∀ n, f (n + 1) ^ p = f n := by
  choose r hr using fun x : Ω => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => r^[n] a, rfl, fun n => ?_⟩
  show r^[n + 1] a ^ p = r^[n] a
  rw [Function.iterate_succ_apply', hr]

theorem nonempty_tower (h : IsClo p Ω) : Nonempty (Tower p Ω) := by
  haveI := h.clo
  haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj
  obtain ⟨z, hz⟩ := tw_exists_prim_p (p := p) Ω
  obtain ⟨f, hf0, hf⟩ := tw_exists_root_chain (p := p) z
  obtain ⟨g, hg0, hg⟩ := tw_exists_root_chain (p := p) (algebraMap (O0 p) Ω (qO p))
  have hprim : ∀ n, IsPrimitiveRoot (f n) (p ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa [hf0] using hz
    | succ m ih => exact tw_prim_step ih (hf m)
  refine ⟨{ ζ := fun n => Nat.casesOn n 1 f
            qq := g
            prim := ?_
            ζpow := ?_
            q0 := hg0
            qpow := hg }⟩
  · intro n
    cases n with
    | zero => simpa using IsPrimitiveRoot.one
    | succ m => exact hprim m
  · intro n
    cases n with
    | zero =>
      show f 0 ^ p = 1
      rw [hf0, hz.pow_eq_one]
    | succ m => exact hf m

theorem qq_pow (T : Tower p Ω) (n : ℕ) : T.qq n ^ p ^ n = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simp [T.q0]
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]

theorem qq_ne_zero (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h0 := qq_pow T n
  rw [h, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at h0
  exact ((isUnit_qO p).map (algebraMap (O0 p) Ω)).ne_zero h0.symm

theorem exists_isEmb (T : Tower p Ω) (n : ℕ) : ∃ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine ⟨Ideal.Quotient.liftₐ (towerIdeal p n) (aevalTower (aeval (T.ζ n)) (T.qq n)) ?_, ?_, ?_⟩
  · intro a ha
    have : towerIdeal p n ≤
        RingHom.ker (aevalTower (aeval (T.ζ n) : (O0 p)[X] →ₐ[O0 p] Ω) (T.qq n)) := by
      rw [towerIdeal, Ideal.span_le]
      rintro b (rfl | rfl)
      · have := (T.prim n).isRoot_cyclotomic hpos
        simp only [SetLike.mem_coe, RingHom.mem_ker, aevalTower_C]
        rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
        exact this
      · simp [RingHom.mem_ker, qq_pow T]
    exact this ha
  · show aevalTower (aeval (T.ζ n) : (O0 p)[X] →ₐ[O0 p] Ω) (T.qq n) (C X) = _
    simp
  · show aevalTower (aeval (T.ζ n) : (O0 p)[X] →ₐ[O0 p] Ω) (T.qq n) X = _
    simp

theorem gms_self (T : Tower p Ω) (n : ℕ) : Gms T n n = Gn T n := rfl

theorem mem_gms (T : Tower p Ω) (m s : ℕ) (g : Gal p Ω) :
    g ∈ Gms T m s ↔ g (T.ζ m) = T.ζ m ∧ g (T.qq s) = T.qq s := Iff.rfl

theorem mem_gn (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem isInt_gal (g : Gal p Ω) {x : Ω} (hx : IsInt p x) : IsInt p (g x) :=
  IsIntegral.map g.toAlgHom hx

theorem isInt_intCast (m : ℤ) : IsInt p (m : Ω) := by
  rw [IsInt, ← map_intCast (algebraMap (O0 p) Ω)]
  exact isIntegral_algebraMap

theorem cong_refl (k : ℕ) (x : Ω) : Cong p k x x :=
  ⟨0, isIntegral_zero, by simp⟩

theorem cong_symm {k : ℕ} {x y : Ω} (h : Cong p k x y) : Cong p k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, IsIntegral.neg hz, by linear_combination -e⟩

theorem cong_trans {k : ℕ} {x y z : Ω} (h : Cong p k x y) (h' : Cong p k y z) : Cong p k x z := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a + b, IsIntegral.add ha hb, by linear_combination e + e'⟩

theorem cong_add {k : ℕ} {x y x' y' : Ω} (h : Cong p k x y) (h' : Cong p k x' y') :
    Cong p k (x + x') (y + y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a + b, IsIntegral.add ha hb, by linear_combination e + e'⟩

theorem cong_sub {k : ℕ} {x y x' y' : Ω} (h : Cong p k x y) (h' : Cong p k x' y') :
    Cong p k (x - x') (y - y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a - b, IsIntegral.sub ha hb, by linear_combination e - e'⟩

theorem cong_mul_right {k : ℕ} {x y c : Ω} (h : Cong p k x y) (hc : IsInt p c) :
    Cong p k (x * c) (y * c) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a * c, IsIntegral.mul ha hc, by linear_combination c * e⟩

theorem cong_gal {k : ℕ} {x y : Ω} (g : Gal p Ω) (h : Cong p k x y) : Cong p k (g x) (g y) := by
  obtain ⟨a, ha, e⟩ := h
  refine ⟨g a, isInt_gal g ha, ?_⟩
  rw [← map_sub, e, map_mul, map_pow, map_natCast]

theorem cong_natCast {k a b : ℕ} (h : a ≡ b [MOD p ^ k]) : Cong p k (a : Ω) (b : Ω) := by
  obtain ⟨c, hc⟩ := h.symm.dvd
  refine ⟨(c : Ω), isInt_intCast c, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hc
  push_cast at this
  exact this

theorem not_cong_one_zero (h : IsClo p Ω) (k : ℕ) (hk : k ≠ 0) : ¬ Cong p k (1 : Ω) 0 := by
  rintro ⟨z, hz, h1⟩
  haveI : FaithfulSMul (O0 p) (integralClosure (O0 p) Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b hab => h.inj (congrArg Subtype.val hab)
  have hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (p ^ k)) :=
    IsUnit.of_mul_eq_one ⟨z, hz⟩ (Subtype.ext (by simpa using h1.symm))
  haveI : IsLocalHom (algebraMap (O0 p) (integralClosure (O0 p) Ω)) :=
    Algebra.IsIntegral.isLocalHom _ _
  exact not_isUnit_p p ((isUnit_pow_iff hk).1 (isUnit_of_map_unit _ _ hu))

theorem zeta_pow_eq_iff (T : Tower p Ω) (k a b : ℕ) :
    T.ζ k ^ a = T.ζ k ^ b ↔ a ≡ b [MOD p ^ k] := by
  rw [(T.prim k).eq_orderOf]
  exact (T.prim k).isOfFinOrder (pow_ne_zero _ hp.out.ne_zero) |>.pow_eq_pow_iff_modEq

theorem exists_isKum (T : Tower p Ω) (n : ℕ) (H : Subgroup (Gal p Ω)) {r : Ω} (hr : r ≠ 0)
    (hH : ∀ g ∈ H, g (r ^ p ^ n) = r ^ p ^ n) : ∃ a, IsKum T n H r a := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : ∀ g : Gal p Ω, ∃ a : ZMod (p ^ n), g ∈ H → g r = T.ζ n ^ a.val * r := by
    intro g
    by_cases hg : g ∈ H
    · have : (g r / r) ^ (p ^ n) = 1 := by
        rw [div_pow, ← map_pow, div_eq_one_iff_eq (pow_ne_zero _ hr), hH g hg]
      obtain ⟨i, hi, he⟩ := (T.prim n).eq_pow_of_pow_eq_one this
      exact ⟨i, fun _ => by rw [ZMod.val_cast_of_lt hi, he, div_mul_cancel₀ _ hr]⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose a ha using this
  exact ⟨a, ha⟩

theorem exists_isKum_qq (T : Tower p Ω) (n : ℕ) : ∃ a, IsKum T n ⊤ (T.qq n) a :=
  exists_isKum T n ⊤ (qq_ne_zero T n) fun g _ => by rw [qq_pow, AlgEquiv.commutes]

theorem isKum_unique {T : Tower p Ω} {n : ℕ} {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0)
    {a b : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H r a) (hb : IsKum T n H r b) {g : Gal p Ω}
    (hg : g ∈ H) : a g = b g := by
  have h := mul_right_cancel₀ hr ((ha g hg).symm.trans (hb g hg))
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at h
  simpa using h

theorem exists_isCyc (T : Tower p Ω) (k : ℕ) :
    ∃ χ : Gal p Ω → ZMod (p ^ k), ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : ∀ g : Gal p Ω, ∃ a : ZMod (p ^ k), g (T.ζ k) = T.ζ k ^ a.val := by
    intro g
    have : (g (T.ζ k)) ^ (p ^ k) = 1 := by rw [← map_pow, (T.prim k).pow_eq_one, map_one]
    obtain ⟨i, hi, he⟩ := (T.prim k).eq_pow_of_pow_eq_one this
    exact ⟨i, by rw [ZMod.val_cast_of_lt hi, he]⟩
  choose a ha using this
  exact ⟨a, ha⟩

theorem isCyc_unique {T : Tower p Ω} {k : ℕ} {χ χ' : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (h' : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ' g).val) : χ = χ' := by
  funext g
  have e := (h g).symm.trans (h' g)
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e
  simpa using e

theorem isCyc_mul {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (g g' : Gal p Ω) : χ (g * g') = χ g * χ g' := by
  have e := h (g * g')
  rw [AlgEquiv.mul_apply, h g', map_pow, h g, ← pow_mul] at e
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e
  simpa using e.symm

theorem isCyc_eq_one_iff {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (g : Gal p Ω) : χ g = 1 ↔ g (T.ζ k) = T.ζ k := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [h g]
  conv_rhs => rhs; rw [← pow_one (T.ζ k)]
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff]
  simp

theorem isCyc_pow_totient {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (g : Gal p Ω) : χ g ^ Nat.totient (p ^ k) = 1 := by
  have hu : χ g * χ g⁻¹ = 1 := by
    rw [← isCyc_mul h, mul_inv_cancel, isCyc_eq_one_iff h]; rfl
  have := ZMod.pow_totient (Units.mkOfMulEqOne _ _ hu)
  have e := congrArg Units.val this
  rwa [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, Units.val_one] at e

theorem isKum_mul {T : Tower p Ω} {n : ℕ} {χ : Gal p Ω → ZMod (p ^ n)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val)
    {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H r a) {g h : Gal p Ω} (hg : g ∈ H) (hh : h ∈ H) :
    a (g * h) = a g + χ g * a h := by
  have e := ha (g * h) (H.mul_mem hg hh)
  rw [AlgEquiv.mul_apply, ha h hh, map_mul, map_pow, hχ g, ha g hg, ← pow_mul, ← mul_assoc,
    ← pow_add] at e
  have e' := mul_right_cancel₀ hr e
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e'
  simpa [add_comm] using e'.symm

theorem isKum_cocycle {T : Tower p Ω} {n : ℕ} {χ : Gal p Ω → ZMod (p ^ n)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val)
    {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H r a) {g h : Gal p Ω} (hg : g ∈ H) (hh : h ∈ H) :
    Cong p n (((χ g).val : Ω) ^ 1 * g ((a h).val : Ω) - ((a (g * h)).val : Ω) + ((a g).val : Ω)) 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e : (χ g).val * (a h).val + (a g).val ≡ (a (g * h)).val [MOD p ^ n] := by
    rw [← ZMod.natCast_eq_natCast_iff, isKum_mul hχ hr ha hg hh]
    simp [add_comm]
  obtain ⟨z, hz, ez⟩ := cong_natCast (Ω := Ω) e
  refine ⟨z, hz, ?_⟩
  rw [map_natCast, ← ez]
  push_cast
  ring

theorem cong_twist {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val) (j : ℕ)
    {g : Gal p Ω} (hg : g (T.ζ k) = T.ζ k) {x : Ω} (hx : IsInt p x) :
    Cong p k (((χ g).val : Ω) ^ j * g x) (g x) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e : (χ g).val ^ j ≡ 1 [MOD p ^ k] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val,
      (isCyc_eq_one_iff hχ g).2 hg]
    simp
  have := cong_mul_right (cong_natCast (Ω := Ω) e) (isInt_gal g hx)
  rwa [Nat.cast_pow, Nat.cast_one, one_mul] at this

theorem not_coboundary_constant_one (h : IsClo p Ω) {k : ℕ} (hk : k ≠ 0) (H : Subgroup (Gal p Ω)) :
    ¬ Cob1 k H (fun _ => (1 : Ω)) := by
  rintro ⟨x, -, hx⟩
  exact not_cong_one_zero h k hk (by simpa using hx 1 H.one_mem)

end Field

theorem inhabited_setting (p : ℕ) [Fact p.Prime] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (O0 p) Ω), IsClo p Ω ∧ ∃ T : Tower p Ω,
      ∀ n, (∃ ι, IsEmb T n ι) ∧
        (∃ χ : Gal p Ω → ZMod (p ^ n), ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val) ∧
        ∃ a, IsKum T n ⊤ (T.qq n) a :=
  ⟨_, inferInstance, inferInstance, isClo_algebraicClosure p,
    (nonempty_tower (isClo_algebraicClosure p)).some,
    fun n => ⟨exists_isEmb _ n, exists_isCyc _ n, exists_isKum_qq _ n⟩⟩

end GlobalTheory.K5.Basic
