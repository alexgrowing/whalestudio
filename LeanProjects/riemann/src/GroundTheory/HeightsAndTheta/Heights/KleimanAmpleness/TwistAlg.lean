import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

namespace SubSystem

theorem twist_sub_eq_mul_of_line (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact Set.mul_mem_mul hq hy
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩

theorem twist_comm (F Q : SubSystem S x Ω) : F.twist Q = Q.twist F :=
  ext_sub fun I => by rw [twist_sub_eq_mul_of_line, twist_sub_eq_mul_of_line, mul_comm]

theorem twist_assoc (F P Q : SubSystem S x Ω) : (F.twist P).twist Q = F.twist (P.twist Q) :=
  ext_sub fun I => by simp only [twist_sub_eq_mul_of_line, mul_assoc]

theorem pow_sub (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I = _
    rw [twistMod_eq_span 0 I hi, zpow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub_eq_mul_of_line, ih, pow_succ']

end SubSystem

theorem twistSys_twist_eq_add (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change twistMod S x b I * twistMod S x a I = twistMod S x (a + b) I
  rw [twistMod_eq_span b I hi, twistMod_eq_span a I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi, add_comm b a]

theorem pow_twistSys (c : ℤ) (n : ℕ) : (twistSys S x c).pow n = twistSys S x (n * c) := by
  induction n with
  | zero =>
    show twistSys S x 0 = twistSys S x (((0 : ℕ) : ℤ) * c)
    rw [Nat.cast_zero, zero_mul]
  | succ n ih =>
    change ((twistSys S x c).pow n).twist (twistSys S x c) = _
    rw [ih, twistSys_twist_eq_add]
    congr 1
    push_cast
    ring

theorem twistMul_sub (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) :
    (twistMul M p m).sub I = (twistSys S x m).sub I * M.sub I ^ p := by
  rw [twistMul, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub]

theorem twistSys_sub_mul (a b : ℤ) (I : Chart x) :
    (twistSys S x a).sub I * (twistSys S x b).sub I = (twistSys S x (a + b)).sub I := by
  rw [← twistSys_twist_eq_add, SubSystem.twist_sub_eq_mul_of_line, mul_comm]

theorem twistSys_sub_pow (c : ℤ) (n : ℕ) (I : Chart x) :
    (twistSys S x c).sub I ^ n = (twistSys S x (n * c)).sub I := by
  rw [← SubSystem.pow_sub, pow_twistSys]

theorem twistMul_twistMul (M : SubSystem S x Ω) (q n : ℕ) (m a : ℤ) :
    twistMul (twistMul M q m) n a = twistMul M (n * q) (n * m + a) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [twistMul_sub, twistMul_sub, twistMul_sub, mul_pow, twistSys_sub_pow, ← pow_mul,
    ← mul_assoc, twistSys_sub_mul, mul_comm q n, add_comm a]

theorem pow_twistMul (M : SubSystem S x Ω) (q j : ℕ) (m : ℤ) :
    (twistMul M q m).pow j = twistMul M (j * q) (j * m) := by
  have h := twistMul_twistMul M q j m 0
  rw [add_zero] at h
  rw [← h]
  exact (SubSystem.twist_twistSys_zero _).symm

namespace LineBundle

def tensorProd (P Q : LineBundle S x) : LineBundle S x where
  toSubSystem := P.toSubSystem.twist Q.toSubSystem
  mem_iff I J h y := by
    constructor
    · intro hy
      have hy' : y ∈ Submodule.span (chartRing S x J)
          {z | ∃ q ∈ Q.sub J, ∃ p ∈ P.sub J, z = q • p} := hy
      refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
        IsUnit (chartIncl h a) ∧ (a : Ω) • z ∈ (P.toSubSystem.twist Q.toSubSystem).sub I)
        ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨q, hq, p, hp, rfl⟩
        obtain ⟨a, ha, haq⟩ := (Q.mem_iff I J h q).mp hq
        obtain ⟨b, hb, hbp⟩ := (P.mem_iff I J h p).mp hp
        refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
        have : ((a * b : chartRing S x I) : Ω) • (q • p) = ((a : Ω) • q) • ((b : Ω) • p) := by
          simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.subset_span ⟨_, haq, _, hbp, rfl⟩
      · exact ⟨1, by simp, by simp⟩
      · rintro y₁ y₂ - - ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      · rintro c z - ⟨a, ha, hz⟩
        obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
        refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
        have : ((a' * a : chartRing S x I) : Ω) • (c • z) =
            (⟨_, hc⟩ : chartRing S x I) • ((a : Ω) • z) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.smul_mem _ _ hz
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (P.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
  fg I := by
    rw [SubSystem.twist_sub_eq_mul_of_line]
    exact (Q.fg I).mul (P.fg I)
  invertible I := by
    obtain ⟨P', hP⟩ := P.invertible I
    obtain ⟨Q', hQ⟩ := Q.invertible I
    refine ⟨P' * Q', ?_⟩
    rw [SubSystem.twist_sub_eq_mul_of_line,
      show Q.sub I * P.sub I * (P' * Q') = (P.sub I * P') * (Q.sub I * Q') by ring, hP, hQ, one_mul]

def powBundle (Q : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => (Q.powBundle n).tensorProd Q

theorem powBundle_toSubSystem (Q : LineBundle S x) (n : ℕ) :
    (Q.powBundle n).toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Q.powBundle n).toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [ih]

end LineBundle

theorem exists_lineBundle_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    ∃ L : LineBundle S x, L.toSubSystem = twistMul M.toSubSystem p m :=
  ⟨(M.powBundle p).tensorProd (twistBundle S x m), by
    change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
    rw [LineBundle.powBundle_toSubSystem]
    rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
