import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx

noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.KapSplitNorm

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one (q : ℕ) [Fact q.Prime] (n : ℕ) (hn : ¬ q ∣ n) : ‖((n : ℕ) : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (n : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)

theorem norm_iota_le_one (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int (ι : ℂ →+* ℂ_[q]) hz using 1 <;> first | exact Subsingleton.elim _ _ | rfl)

theorem norm_iota_unit (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (hn : ¬ q ∣ n) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (n : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := norm_iota_le_one q ι x hx
  have e2 := norm_iota_le_one q ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, map_natCast, norm_natCast_eq_one q n hn]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem norm_rt_eq_one {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpq : p ≠ q) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpq' : ¬ q ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : q ∣ p := (Fact.out : q.Prime).dvd_of_dvd_pow h
    exact hpq (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem norm_kappa_split : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q →
    ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  intro D γ₀ k q _ hsq ι
  have hfin := yFinite D γ₀ k
  have hfinS : (Function.mulSupport
      (fun p : {p : ℕ // p.Prime ∧ SplitK D p} => k.rt p ^ (-(k.yP p)))).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro p hp
    refine ⟨p.2.1, p.2.2, ?_⟩
    intro h0
    apply hp
    simp [h0]
  let F : ℂ →* ℝ :=
    { toFun := fun z => ‖ι z‖
      map_one' := by simp
      map_mul' := fun x y => by simp [norm_mul] }
  have hF : ∀ z, F z = ‖ι z‖ := fun _ => rfl
  rw [KapChoice.kappa, ← hF, MonoidHom.map_finprod F hfinS,
    finprod_eq_single _ (⟨q, Fact.out, hsq⟩ : {p : ℕ // p.Prime ∧ SplitK D p})]
  · rw [hF, map_zpow₀, norm_zpow]
  · intro p hp
    have hpq : (p : ℕ) ≠ q := fun h => hp (Subtype.ext h)
    rw [hF, map_zpow₀, norm_zpow, norm_rt_eq_one k q ι p p.2.1 p.2.2 hpq, one_zpow]

end GlobalTheory.KapSplitNorm
