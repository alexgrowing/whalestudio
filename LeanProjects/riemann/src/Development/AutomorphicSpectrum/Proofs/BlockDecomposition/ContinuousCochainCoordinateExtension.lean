import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothUniformExponent
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.GrpOnto

theorem sum_range_periodic {A : Type*} [AddCommMonoid A] (u : ℕ → A) (p : ℕ)
    (hu : ∀ t, u (t + p) = u t) (q : ℕ) :
    ∑ t ∈ Finset.range (p * q), u t = q • ∑ t ∈ Finset.range p, u t := by
  have hper : ∀ q t, u (p * q + t) = u t := by
    intro q t
    induction q with
    | zero => simp
    | succ q ih => rw [show p * (q + 1) + t = (p * q + t) + p by ring, hu, ih]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hper q t

theorem val_sub_one {P : ℕ} [NeZero P] (z : ZMod P) :
    (z.val ≠ 0 → (z - 1).val = z.val - 1) ∧ (z.val = 0 → (z - 1).val = P - 1) := by
  have hlt := ZMod.val_lt z
  have hz : ((z.val : ℕ) : ZMod P) = z := ZMod.natCast_zmod_val z
  have hP := NeZero.pos P
  constructor
  · intro h
    have e1 : z - 1 = ((z.val - 1 : ℕ) : ZMod P) := by
      rw [Nat.cast_sub (by omega), hz]; simp
    rw [e1, ZMod.val_natCast_of_lt (by omega)]
  · intro h
    have hz0 : z = 0 := by rw [← hz, h]; simp
    have e1 : z - 1 = ((P - 1 : ℕ) : ZMod P) := by
      rw [Nat.cast_sub hP, hz0]; simp
    rw [e1, ZMod.val_natCast_of_lt (by omega)]

theorem core {R : Type} [CommRing R] (l : ℕ) [Fact l.Prime] (k : ℕ) {M : Type w} [AddCommGroup M]
    [Module R M] (ρ : Multiplicative (Fin k → ℤ_[l]) →* (M →ₗ[R] M)) (n c : ℕ) (S : Set (Fin k))
    (i : Fin k) (hiS : i ∉ S) (hc : ∀ x : M, l ^ c • x = 0)
    (hsm : ∀ x : M, ∃ a : ℕ, ∀ g : Fin k → ℤ_[l], ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) x = x)
    (f : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M)
    (hf : ∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      f (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (f x)) :
    ∃ g : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M,
      (∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
        g (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (g x)) ∧
      ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
        ρ (Multiplicative.ofAdd (Pi.single i 1)) (g fun j => x j - Pi.single i 1) - g x = f x := by
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.SmoothUniform.smooth_uniform_exponent (R := R) l k ρ n hsm f
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨e, he⟩ : ∃ e : Fin k → ℤ_[l], e = Pi.single i 1 := ⟨_, rfl⟩
  rw [← he]
  have hcomm : ∀ (p q : Multiplicative (Fin k → ℤ_[l])) (y : M), ρ p (ρ q y) = ρ q (ρ p y) := by
    intro p q y
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hmul : ∀ (p q : Fin k → ℤ_[l]) (y : M),
      ρ (Multiplicative.ofAdd (p + q)) y = ρ (Multiplicative.ofAdd p) (ρ (Multiplicative.ofAdd q) y) := by
    intro p q y
    rw [ofAdd_add, map_mul, Module.End.mul_apply]
  let sh : ℕ → (Fin (n + 1) → Fin k → ℤ_[l]) → (Fin (n + 1) → Fin k → ℤ_[l]) :=
    fun t x j => x j - t • e
  let F : ℕ → (Fin (n + 1) → Fin k → ℤ_[l]) → M :=
    fun t x => ρ (Multiplicative.ofAdd (t • e)) (f (sh t x))
  have hF0 : ∀ x, F 0 x = f x := by
    intro x
    have h1 : sh 0 x = x := by funext j; simp [sh]
    simp [F, h1]
  have hFs : ∀ t x, ρ (Multiplicative.ofAdd e) (F t fun j => x j - e) = F (t + 1) x := by
    intro t x
    have h1 : sh t (fun j => x j - e) = sh (t + 1) x := by
      funext j
      simp only [sh, succ_nsmul]
      abel
    change ρ _ (ρ _ (f (sh t fun j => x j - e))) = ρ _ (f (sh (t + 1) x))
    rw [h1, succ_nsmul', hmul]
  have hE : (l ^ a) • e = (l : ℤ_[l]) ^ a • e := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    rfl
  have hper : ∀ t x, F (t + l ^ a) x = F t x := by
    intro t x
    have h1 := (ha e (sh (t + l ^ a) x)).1
    have h2 := (ha e (sh (t + l ^ a) x)).2
    have h3 : (fun s => (l : ℤ_[l]) ^ a • e + sh (t + l ^ a) x s) = sh t x := by
      funext s
      simp only [sh, add_nsmul, ← hE]
      abel
    rw [h3] at h1
    change ρ _ (f (sh (t + l ^ a) x)) = ρ _ (f (sh t x))
    rw [add_nsmul, hmul, hE, h2, h1]
  have hsum : ∀ x, ∑ t ∈ Finset.range (l ^ (a + c)), F (t + 1) x = 0 := by
    intro x
    rw [pow_add, sum_range_periodic (fun t => F (t + 1) x) (l ^ a)
      (fun t => by
        change F (t + l ^ a + 1) x = F (t + 1) x
        rw [add_right_comm]
        exact hper (t + 1) x) (l ^ c)]
    exact hc _
  haveI : NeZero (l ^ (a + c)) := ⟨pow_ne_zero _ hlpos.ne'⟩
  let z : (Fin (n + 1) → Fin k → ℤ_[l]) → ZMod (l ^ (a + c)) :=
    fun x => PadicInt.toZModPow (a + c) (x 0 i)
  have hz1 : ∀ x, z (fun j => x j - e) = z x - 1 := by
    intro x
    simp [z, he, map_sub]
  have hzj : ∀ j ∈ S, ∀ x, z (fun t => Pi.single j (1 : ℤ_[l]) + x t) = z x := by
    intro j hj x
    have hij : i ≠ j := fun h => hiS (h ▸ hj)
    simp [z, Pi.single_eq_of_ne hij]
  have hzl : IsLocallyConstant z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have hb : Metric.closedBall (x 0 i) ((l : ℝ) ^ (-((a + c : ℕ) : ℤ))) ∈ nhds (x 0 i) :=
      Metric.closedBall_mem_nhds _ (zpow_pos (by exact_mod_cast hlpos) _)
    have hcont : Continuous (fun y : Fin (n + 1) → Fin k → ℤ_[l] => y 0 i) :=
      (continuous_apply i).comp (continuous_apply 0)
    filter_upwards [hcont.continuousAt.preimage_mem_nhds hb] with y hy
    have h1 : ‖y 0 i - x 0 i‖ ≤ (l : ℝ) ^ (-((a + c : ℕ) : ℤ)) := by
      simpa [dist_eq_norm] using hy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h1
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hFl : ∀ t, IsLocallyConstant (F t) := by
    intro t
    have hsh : Continuous (sh t) := continuous_pi fun j => (continuous_apply j).sub continuous_const
    exact (f.isLocallyConstant.comp_continuous hsh).comp _
  let gf : (Fin (n + 1) → Fin k → ℤ_[l]) → M :=
    fun x => -∑ t ∈ Finset.range ((z x).val + 1), F t x
  have hg : IsLocallyConstant gf := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h1 := (IsLocallyConstant.iff_eventually_eq _).1 hzl x
    have h2 : ∀ᶠ y in nhds x, ∀ t ∈ Finset.range ((z x).val + 1), F t y = F t x :=
      (Filter.eventually_all_finset _).2 fun t _ => (IsLocallyConstant.iff_eventually_eq _).1 (hFl t) x
    filter_upwards [h1, h2] with y hy1 hy2
    change -∑ t ∈ Finset.range ((z y).val + 1), F t y = -∑ t ∈ Finset.range ((z x).val + 1), F t x
    rw [hy1]
    exact congrArg _ (Finset.sum_congr rfl hy2)
  have hgE : ∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      gf (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (gf x) := by
    intro j hj x
    have hFj : ∀ t, F t (fun s => Pi.single j (1 : ℤ_[l]) + x s) =
        ρ (Multiplicative.ofAdd (Pi.single j 1)) (F t x) := by
      intro t
      have h1 : sh t (fun s => Pi.single j (1 : ℤ_[l]) + x s) =
          fun s => Pi.single j (1 : ℤ_[l]) + sh t x s := by
        funext s
        simp only [sh, add_sub_assoc]
      change ρ _ (f (sh t _)) = ρ _ (ρ _ (f (sh t x)))
      rw [h1, hf j hj, hcomm]
    simp only [gf]
    rw [hzj j hj x, map_neg, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun t _ => hFj t)
  have hgT : ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      ρ (Multiplicative.ofAdd e) (gf fun j => x j - e) - gf x = f x := by
    intro x
    simp only [gf]
    rw [map_neg, map_sum, hz1 x]
    simp only [hFs]
    obtain ⟨hne, h0⟩ := val_sub_one (z x)
    by_cases hx : (z x).val = 0
    · have hP := NeZero.pos (l ^ (a + c))
      rw [h0 hx, hx, Nat.sub_add_cancel hP, hsum x]
      simp [hF0]
    · rw [hne hx, Nat.sub_add_cancel (Nat.pos_of_ne_zero hx),
        Finset.sum_range_succ' (fun t => F t x) (z x).val, hF0]
      abel
  exact ⟨⟨gf, hg⟩, hgE, hgT⟩

end GlobalTheory.CompanionTheory.GrpOnto
