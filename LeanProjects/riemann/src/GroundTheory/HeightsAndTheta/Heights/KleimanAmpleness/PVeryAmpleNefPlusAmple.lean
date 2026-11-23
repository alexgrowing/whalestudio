import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GeneratedTwistSysZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Algebra

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem KThm.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩

theorem KThm.sub_pow (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [KThm.sub_twist, ih, pow_succ, mul_comm]

theorem KThm.span_zpow_mul (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (a b : ℤ) :
    Submodule.span (chartRing S x I) {x i ^ a} * Submodule.span (chartRing S x I) {x i ^ b} =
      Submodule.span (chartRing S x I) {x i ^ (a + b)} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

theorem KThm.span_zpow_pow (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (a : ℤ) (n : ℕ) :
    Submodule.span (chartRing S x I) {x i ^ a} ^ n =
      Submodule.span (chartRing S x I) {x i ^ (a * n)} := by
  induction n with
  | zero => simp [Submodule.one_eq_span]
  | succ n ih =>
    rw [pow_succ, ih, KThm.span_zpow_mul I hi]
    congr 3
    push_cast; ring_nf

theorem KThm.sub_twistMul (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) :
    (twistMul M p m).sub I = M.sub I ^ p * Submodule.span (chartRing S x I) {x i ^ m} := by
  rw [twistMul, KThm.sub_twist, KThm.sub_pow, mul_comm]
  change _ * twistMod S x m I = _
  rw [twistMod_eq_span m I hi]

theorem KThm.mem_sub_of_mem_secs {F : SubSystem S x Ω} {z : Ω} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I := by
  rw [SubSystem.secs, Submodule.mem_iInf] at hz
  exact hz I

theorem KThm.generated_of_le (F : SubSystem S x Ω)
    (h : ∀ I, F.sub I ≤ Submodule.span (chartRing S x I) (F.secs : Set Ω)) : F.Generated := by
  intro I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) (h I)
  exact KThm.mem_sub_of_mem_secs hz I

theorem KThm.mul_mem_secs {F Q : SubSystem S x Ω} {a b : Ω} (ha : a ∈ F.secs) (hb : b ∈ Q.secs) :
    b * a ∈ (F.twist Q).secs := by
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro I
  exact Submodule.subset_span ⟨b, KThm.mem_sub_of_mem_secs hb I, a, KThm.mem_sub_of_mem_secs ha I,
    (smul_eq_mul b a).symm⟩

theorem KThm.generated_twist {F Q : SubSystem S x Ω} (hF : F.Generated) (hQ : Q.Generated) :
    (F.twist Q).Generated := by
  refine KThm.generated_of_le _ fun I => ?_
  rw [KThm.sub_twist, ← hF I, ← hQ I, Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, a, ha, rfl⟩
  exact KThm.mul_mem_secs ha hb

theorem KThm.generated_pow {Q : SubSystem S x Ω} (hQ : Q.Generated) (n : ℕ) : (Q.pow n).Generated := by
  induction n with
  | zero => exact generated_twistSys_zero'
  | succ n ih => exact KThm.generated_twist ih hQ

theorem KThm.generated_twistSys_one : (twistSys S x 1).Generated := by
  refine KThm.generated_of_le _ fun I => ?_
  change twistMod S x 1 I ≤ _
  rw [← span_range_eq_twistMod_one I]
  exact Submodule.span_mono (Set.range_subset_iff.mpr fun j => mem_secs_twistBundle_one j)

theorem KThm.generated_twistSys_nat (e : ℕ) : (twistSys S x e).Generated := by
  have h : twistSys S x e = (twistSys S x 1).pow e := by
    refine SubSystem.ext_sub fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    rw [KThm.sub_pow]
    change twistMod S x e I = twistMod S x 1 I ^ e
    rw [twistMod_eq_span _ I hi, twistMod_eq_span _ I hi, KThm.span_zpow_pow I hi, one_mul]
  rw [h]
  exact KThm.generated_pow KThm.generated_twistSys_one e

theorem KThm.twistMul_one (M : SubSystem S x Ω) (c : ℤ) :
    twistMul M 1 c = M.twist (twistSys S x c) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twistMul M 1 c I hi, KThm.sub_twist, pow_one, mul_comm]
  change _ = twistMod S x c I * _
  rw [twistMod_eq_span c I hi]

theorem KThm.twistMul_one_zero (M : SubSystem S x Ω) : twistMul M 1 0 = M := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twistMul M 1 0 I hi, pow_one, zpow_zero, ← Submodule.one_eq_span, mul_one]

def KThm.lbTwist (F Q : LineBundle S x) : LineBundle S x :=
  { F.toSubSystem.twist Q.toSubSystem with
    mem_iff := fun I J h y => by
      constructor
      · intro hy
        change y ∈ Submodule.span _ {z | ∃ q ∈ Q.sub J, ∃ y ∈ F.sub J, z = q • y} at hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨q, hq, f, hf, rfl⟩ := hz
          obtain ⟨a, ha, haf⟩ := (F.mem_iff I J h f).mp hf
          obtain ⟨b, hb, hbq⟩ := (Q.mem_iff I J h q).mp hq
          refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
          have e : ((a * b : chartRing S x I) : Ω) • (q • f) = ((b : Ω) • q) • ((a : Ω) • f) := by
            simp only [smul_eq_mul, Subalgebra.coe_mul]; ring_nf
          rw [e]
          exact Submodule.subset_span ⟨_, hbq, _, haf, rfl⟩
        | zero => exact ⟨1, by simp, by simp⟩
        | add y₁ y₂ _ _ h₁ h₂ =>
          obtain ⟨a, ha, h1⟩ := h₁
          obtain ⟨b, hb, h2⟩ := h₂
          refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
          have e : ((a * b : chartRing S x I) : Ω) • (y₁ + y₂) = b • ((a : Ω) • y₁) + a • ((b : Ω) • y₂) := by
            simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring_nf
          rw [e]
          exact Submodule.add_mem _ (Submodule.smul_mem _ b h1) (Submodule.smul_mem _ a h2)
        | smul c y _ hy =>
          obtain ⟨a, ha, hay⟩ := hy
          obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
          refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
          have e : ((a' * a : chartRing S x I) : Ω) • (c • y) =
              (⟨(a' : Ω) * c, hc⟩ : chartRing S x I) • ((a : Ω) • y) := by
            simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring_nf
          rw [e]
          exact Submodule.smul_mem _ _ hay
      · rintro ⟨a, ⟨u, hu⟩, hay⟩
        have hJ := (F.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
        have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
          have := congrArg Subtype.val (Units.inv_mul u)
          rw [hu] at this
          exact this
        have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
          rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
        rw [hy]
        exact Submodule.smul_mem _ _ hJ
    fg := fun I => by
      rw [KThm.sub_twist]
      exact (Q.fg I).mul (F.fg I)
    invertible := fun I => by
      obtain ⟨F', hF'⟩ := F.invertible I
      obtain ⟨Q', hQ'⟩ := Q.invertible I
      refine ⟨Q' * F', ?_⟩
      change (F.toSubSystem.twist Q.toSubSystem).sub I * _ = 1
      rw [KThm.sub_twist, mul_mul_mul_comm]
      change Q.sub I * Q' * (F.sub I * F') = 1
      rw [hF', hQ', one_mul] }

def KThm.lbPow (Q : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => KThm.lbTwist (KThm.lbPow Q n) Q

theorem KThm.lbPow_toSubSystem (Q : LineBundle S x) (n : ℕ) :
    (KThm.lbPow Q n).toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (KThm.lbPow Q n).toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [ih]

end Algebra

section Upward

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem KThm.upward (hJ : GraphClosed.Statement.{u, w}) (M : LineBundle k x) (P : ℕ) (m' : ℤ)
    (hP : 1 ≤ P) (hG : (twistMul M.toSubSystem P m').Generated) (t : ℚ) (ht : (m' : ℚ) < P * t) :
    ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * t ∧ IsVeryAmple (twistMul M.toSubSystem p m) := by
  have hq : 0 < t.den := t.den_pos
  have hnum : (t.num : ℚ) = t * t.den := (Rat.mul_den_eq_num t).symm
  have hlt : ((t.den : ℤ) * m' : ℤ) < (P : ℤ) * t.num := by
    have h1 : ((t.den : ℚ) * m') < P * t.num := by
      rw [hnum]
      have : (0 : ℚ) < t.den := by exact_mod_cast hq
      nlinarith
    exact_mod_cast h1
  set e : ℤ := P * t.num - t.den * m' - 1 with he_def
  have he : 0 ≤ e := by omega
  let G : LineBundle k x := KThm.lbTwist (KThm.lbPow (KThm.lbTwist (KThm.lbPow M P) (twistBundle k x m')) t.den)
    (twistBundle k x e)
  have hGsub : G.toSubSystem = ((twistMul M.toSubSystem P m').pow t.den).twist (twistSys k x e) := by
    change (KThm.lbPow _ t.den).toSubSystem.twist (twistSys k x e) = _
    rw [KThm.lbPow_toSubSystem]
    change ((((KThm.lbPow M P).toSubSystem).twist (twistSys k x m')).pow t.den).twist _ = _
    rw [KThm.lbPow_toSubSystem]
    rfl
  have hGgen : G.toSubSystem.Generated := by
    rw [hGsub]
    refine KThm.generated_twist (KThm.generated_pow hG _) ?_
    have := KThm.generated_twistSys_nat (S := k) (x := x) e.toNat
    rwa [Int.toNat_of_nonneg he] at this
  have hV := hJ k Ω N x G (twistBundle k x 1) hGgen isVeryAmple_twistSys_one
  refine ⟨P * t.den, P * t.num, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    by push_cast; rw [hnum]; ring, ?_⟩
  convert hV using 1
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twistMul _ _ _ I hi, KThm.sub_twist, hGsub, KThm.sub_twist, KThm.sub_pow,
    KThm.sub_twistMul _ _ _ I hi]
  change _ = twistMod k x 1 I * (twistMod k x e I * _)
  rw [twistMod_eq_span _ I hi, twistMod_eq_span _ I hi, mul_pow, ← pow_mul, KThm.span_zpow_pow I hi,
    mul_left_comm (Submodule.span _ {x i ^ e}), mul_left_comm (Submodule.span _ {x i ^ (1 : ℤ)}),
    KThm.span_zpow_mul I hi, KThm.span_zpow_mul I hi]
  congr 3
  rw [he_def]; ring_nf

end Upward

theorem VeryAmpleNefPlusAmple.proof (hGen : Generated.Statement.{u, w})
    (hSec : SectionExists.Statement.{u, w}) (hThree : StepThree.Statement.{u, w})
    (hJ : GraphClosed.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    VeryAmpleNefPlusAmple.Statement.{u, w} := by
  intro k _ d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  rcases d with _ | d
  · intro Ω _ _ N x M hdim _ t ht
    have hG : (twistMul M.toSubSystem 1 0).Generated := by
      rw [KThm.twistMul_one_zero]; exact hPt k Ω N x M hdim
    exact KThm.upward hJ M 1 0 le_rfl hG t (by push_cast; linarith)
  · intro Ω _ _ N x M hdim hnef

    let VA : ℚ → Prop := fun u =>
      ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * u ∧ IsVeryAmple (twistMul M.toSubSystem p m)
    set ρ : ℚ := 1 - 1 / (2 * ((d : ℚ) + 1)) with hρ
    have hd : (0 : ℚ) < (d : ℚ) + 1 := by positivity
    have hρ0 : 0 < ρ := by
      rw [hρ]
      have : 1 / (2 * ((d : ℚ) + 1)) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have : (0 : ℚ) ≤ d := by positivity
        linarith
      linarith
    have hρ1 : ρ < 1 := by
      rw [hρ]
      have : 0 < 1 / (2 * ((d : ℚ) + 1)) := by positivity
      linarith

    have step : ∀ u : ℚ, 0 < u → VA u → ∀ t'' : ℚ, u * ρ < t'' → VA t'' := by
      intro u hu hVA t'' ht''
      have hs'0 : 0 < u / (2 * ((d : ℚ) + 1)) := by positivity
      have hs'lt : u / (2 * ((d : ℚ) + 1)) < u / ((d : ℚ) + 1) := by
        apply div_lt_div_of_pos_left hu hd; linarith
      obtain ⟨p, m, c₁, hp, hm, hc₁, σ, hσ, hσ0⟩ :=
        hSec k Ω N x d M u (u / (2 * ((d : ℚ) + 1))) hdim hnef hs'0 (by exact_mod_cast hs'lt) hVA
      let T : StepData k x :=
        { d := d, dim := hdim, M := M, nef := hnef, t := u, s' := u / (2 * ((d : ℚ) + 1)),
          s'_pos := hs'0, s'_lt := by exact_mod_cast hs'lt, p := p, p_pos := hp, m := m, m_eq := hm,
          c₁ := c₁, c₁_pos := hc₁, si := σ, si_mem := hσ, si_ne := hσ0 }
      obtain ⟨c₂, hc₂⟩ := hThree k Ω N x T (fun e he => ih e (Nat.lt_succ_of_le he))
      have hδ : 0 < t'' - (u - u / (2 * ((d : ℚ) + 1))) := by
        have : u * ρ = u - u / (2 * ((d : ℚ) + 1)) := by rw [hρ]; ring
        linarith
      obtain ⟨n, hn⟩ := exists_nat_gt ((c₂ : ℚ) / (t'' - (u - u / (2 * ((d : ℚ) + 1)))))
      have hgen := hc₂ (n + 1) (by omega)
      have heq : (T.L.pow (n + 1)).twist (twistSys k x c₂) =
          twistMul M.toSubSystem (p * (n + 1)) (m * (n + 1) + c₂) := by
        refine SubSystem.ext_sub fun I => ?_
        obtain ⟨i, hi⟩ := I.2.1
        rw [KThm.sub_twist, KThm.sub_pow, show T.L = twistMul M.toSubSystem p m from rfl,
          KThm.sub_twistMul _ _ _ I hi, KThm.sub_twistMul _ _ _ I hi]
        change twistMod k x c₂ I * _ = _
        rw [twistMod_eq_span _ I hi, mul_pow, ← pow_mul, KThm.span_zpow_pow I hi, mul_left_comm,
          KThm.span_zpow_mul I hi]
        congr 3
        push_cast; ring_nf
      rw [heq] at hgen
      refine KThm.upward hJ M (p * (n + 1)) (m * (n + 1) + c₂) (by nlinarith) hgen t'' ?_
      have hc₂lt : (c₂ : ℚ) < n * (t'' - (u - u / (2 * ((d : ℚ) + 1)))) := by
        rwa [div_lt_iff₀ hδ] at hn
      have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
      have hn0 : (0 : ℚ) ≤ n := by positivity
      have h1 : (n : ℚ) * (t'' - (u - u / (2 * ((d : ℚ) + 1)))) ≤
          p * ((n : ℚ) + 1) * (t'' - (u - u / (2 * ((d : ℚ) + 1)))) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hδ.le
      push_cast
      rw [hm]
      linarith

    obtain ⟨c₀, hc₀⟩ := hGen k Ω N x M
    have base : ∀ t : ℚ, (c₀ : ℚ) < t → VA t := fun t ht =>
      KThm.upward hJ M 1 c₀ le_rfl (by rw [KThm.twistMul_one]; exact hc₀ c₀ le_rfl) t
        (by push_cast; linarith)
    have iter : ∀ n : ℕ, ∀ t : ℚ, |(c₀ : ℚ)| * ρ ^ n < t → VA t := by
      intro n
      induction n with
      | zero =>
        intro t ht
        exact base t (by have := le_abs_self (c₀ : ℚ); simp at ht; linarith)
      | succ n ihn =>
        intro t ht
        have ha : 0 ≤ |(c₀ : ℚ)| * ρ ^ n := by positivity
        have hat : |(c₀ : ℚ)| * ρ ^ n * ρ < t := by rw [pow_succ, ← mul_assoc] at ht; exact ht
        have htρ : |(c₀ : ℚ)| * ρ ^ n < t / ρ := by rw [lt_div_iff₀ hρ0]; exact hat
        set a := |(c₀ : ℚ)| * ρ ^ n
        have hu0 : 0 < (a + t / ρ) / 2 := by linarith
        refine step ((a + t / ρ) / 2) hu0 (ihn _ (by linarith)) t ?_
        have : (a + t / ρ) / 2 < t / ρ := by linarith
        rwa [lt_div_iff₀ hρ0] at this
    intro t ht
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos ht (by positivity : (0 : ℚ) < |(c₀ : ℚ)| + 1)) hρ1
    refine iter n t ?_
    have hpos : 0 ≤ ρ ^ n := by positivity
    rw [lt_div_iff₀ (by positivity)] at hn
    nlinarith [abs_nonneg (c₀ : ℚ)]

end

end GroundTheory.Heights₂.Heights.Kleiman
