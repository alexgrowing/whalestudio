import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapVal
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapDet
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapSplit

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical IsDedekindDomain

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions
open Formalism.L2.Th1.H (stdLat pow4 imgLat relIdx IsIsom IsSelfDual)

variable {D : D7}

def f1 {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : D.host.K →+* ℂ_[p] := (ι : ℂ →+* ℂ_[p]).comp (fK D)

def f2 {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : D.host.K →+* ℂ_[p] :=
  ((ι : ℂ →+* ℂ_[p]).comp (starRingEnd ℂ)).comp (fK D)

theorem liftOneFormsToCompatible_apply {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (x : D.host.K) : f1 ι x = ι (D.host.φ₀ (x : D.host.E)) := rfl

theorem conjugate_embedding_apply {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (x : D.host.K) :
    f2 ι x = ι (D.host.φ₀ (D.host.conj (x : D.host.E))) := by
  rw [phi_conj]; rfl

section Kap

variable {γ₀ : IsoK D} (k : KapChoice γ₀)

theorem pi_unit {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p]) (q : ℕ) (hq : q.Prime) (hs : SplitK D q) (hqp : q ≠ p) :
    ‖f ((k.pi q : 𝓞 D.host.K) : D.host.K)‖ = 1 := by
  have h1 : ((q : ℕ) : 𝓞 D.host.K) ^ classNumber D.host.K ∈ Ideal.span {k.pi q} :=
    k.pi_gen q hq hs ▸ Ideal.pow_mem_pow (k.pp_over q hq hs) _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : ((c : D.host.K) * ((k.pi q : 𝓞 D.host.K) : D.host.K)) = ((q : ℕ) : D.host.K) ^ classNumber D.host.K := by
    exact_mod_cast congrArg (fun z : 𝓞 D.host.K => (z : D.host.K)) hc
  have h3 : ‖f (c : D.host.K)‖ * ‖f ((k.pi q : 𝓞 D.host.K) : D.host.K)‖ = 1 := by
    rw [← norm_mul, ← map_mul, h2, map_pow, map_natCast, norm_pow,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p ((Nat.coprime_primes hq Fact.out).2 hqp), one_pow]
  have h4 := normO_le f c
  have h5 := normO_le f (k.pi q)
  nlinarith [norm_nonneg (f (c : D.host.K)), norm_nonneg (f ((k.pi q : 𝓞 D.host.K) : D.host.K))]

theorem rt_norm_pow {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (q : ℕ) (hq : q.Prime) (hs : SplitK D q) :
    ‖ι (k.rt q)‖ ^ (2 * classNumber D.host.K) =
      ‖f1 ι ((k.pi q : 𝓞 D.host.K) : D.host.K)‖ / ‖f2 ι ((k.pi q : 𝓞 D.host.K) : D.host.K)‖ := by
  rw [← norm_pow, ← map_pow, k.rt_pow q hq hs, map_div₀, norm_div, liftOneFormsToCompatible_apply, conjugate_embedding_apply]

theorem rt_unit {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (q : ℕ) (hq : q.Prime) (hs : SplitK D q) (hqp : q ≠ p) :
    ‖ι (k.rt q)‖ = 1 := by
  have h := rt_norm_pow k ι q hq hs
  rw [pi_unit k _ q hq hs hqp, pi_unit k _ q hq hs hqp, div_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (mul_ne_zero two_ne_zero (classNumber_ne D))).1 h

def nm {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : ℂ →* ℝ where
  toFun z := ‖ι z‖
  map_one' := by simp
  map_mul' x y := by simp

theorem supp_finite : (Function.mulSupport fun q : {q : ℕ // q.Prime ∧ SplitK D q} => k.rt q ^ (-(k.yP q))).Finite := by
  have h := (yFinite D γ₀ k).preimage (f := fun q : {q : ℕ // q.Prime ∧ SplitK D q} => (q : ℕ)) Subtype.val_injective.injOn
  refine h.subset fun q hq => ?_
  refine ⟨q.2.1, q.2.2, fun h0 => hq ?_⟩
  show k.rt q ^ (-(k.yP q)) = 1
  rw [h0, neg_zero, zpow_zero]

theorem kappa_norm {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) :
    ‖ι k.kappa‖ = ∏ᶠ q : {q : ℕ // q.Prime ∧ SplitK D q}, ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  have h := (nm ι).map_finprod (supp_finite k)
  have e : ∀ q : {q : ℕ // q.Prime ∧ SplitK D q}, nm ι (k.rt q ^ (-(k.yP q))) = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
    intro q
    show ‖ι (k.rt q ^ (-(k.yP q)))‖ = _
    rw [map_zpow₀, norm_zpow]
  simp only [e] at h
  exact h

theorem kappa_norm_split {p : ℕ} [hp : Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hs : SplitK D p) :
    ‖ι k.kappa‖ = ‖ι (k.rt p)‖ ^ (-(k.yP p)) := by
  rw [kappa_norm]
  rw [finprod_eq_single _ (⟨p, hp.out, hs⟩ : {q : ℕ // q.Prime ∧ SplitK D q})]
  intro q hq
  rw [rt_unit k ι q q.2.1 q.2.2 (fun h => hq (Subtype.ext h)), one_zpow]

theorem kappa_norm_nonsplit {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hs : ¬ SplitK D p) : ‖ι k.kappa‖ = 1 := by
  rw [kappa_norm]
  refine finprod_eq_one_of_forall_eq_one fun q => ?_
  rw [rt_unit k ι q q.2.1 q.2.2 (fun h => hs (h ▸ q.2.2)), one_zpow]

theorem zpow_aux (a X : ℝ) (y : ℤ) (h : ℕ) : ((a ^ (-y)) ^ 2 * X) ^ h = (a ^ (2 * h)) ^ (-y) * X ^ h := by
  rw [mul_pow, ← zpow_natCast (a ^ (-y)) 2, ← zpow_mul, ← zpow_natCast (a ^ _) h, ← zpow_mul, ← zpow_natCast a (2 * h), ← zpow_mul]
  congr 2
  push_cast
  ring

theorem kappa_split {p : ℕ} [hp : Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hs : SplitK D p) :
    ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ (((k.gaP p).detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  set x : D.host.K := (k.gaP p).detRel γ₀ with hx
  have hU := detRel_unitary (k.gaP p) γ₀
  rw [← hx] at hU
  have hX0 : D.host.φ₀ (x : D.host.E) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hU; exact zero_ne_one hU
  have hx0 : x ≠ 0 := by
    rintro h0
    apply hX0
    rw [h0]; simp
  have hh : classNumber D.host.K ≠ 0 := classNumber_ne D
  obtain ⟨b, hb⟩ := exists_conj (k.pi p)
  have hbn := conj_pi_not_mem k p hp.out hs b hb
  have hgen := k.pi_gen p hp.out hs
  have hrt := rt_norm_pow k ι p hp.out hs
  have hy : k.yP p = -WithZero.log ((k.pp p).valuation D.host.K x) := rfl
  rw [kappa_norm_split k ι hs]
  refine (pow_eq_one_iff_of_nonneg (by positivity) hh).1 ?_
  rw [zpow_aux, hrt]
  rcases pi_dichotomy k p hp.out hs ι with hlt | hlt
  · have hlt1 : ‖f1 ι ((k.pi p : 𝓞 D.host.K) : D.host.K)‖ < 1 := hlt
    have e1 := norm_pow_eq (f1 ι) (k.pp p) (k.pi p) _ hgen hlt1 hx0
    have e2 := norm_eq_one_of_not_mem (f1 ι) (k.pp p) (k.pi p) _ hgen hlt1 hbn
    have e3 : f2 ι ((k.pi p : 𝓞 D.host.K) : D.host.K) = f1 ι (b : D.host.K) := by
      rw [conjugate_embedding_apply, liftOneFormsToCompatible_apply, hb]
    rw [e3, e2, div_one]
    rw [liftOneFormsToCompatible_apply] at e1
    rw [e1, ← hy, ← zpow_add₀ (by
      intro h0
      have := norm_eq_zero.1 h0
      have h1 := (map_eq_zero (f1 ι)).1 this
      exact k.pi_ne_zero p hp.out hs (by exact_mod_cast h1))]
    simp
  · have hlt2 : ‖f2 ι ((k.pi p : 𝓞 D.host.K) : D.host.K)‖ < 1 := by rw [conjugate_embedding_apply]; exact hlt
    have e1 := norm_pow_eq (f2 ι) (k.pp p) (k.pi p) _ hgen hlt2 hx0
    have e2 := norm_eq_one_of_not_mem (f2 ι) (k.pp p) (k.pi p) _ hgen hlt2 hbn
    have e3 : f1 ι ((k.pi p : 𝓞 D.host.K) : D.host.K) = f2 ι (b : D.host.K) := by
      rw [conjugate_embedding_apply, liftOneFormsToCompatible_apply, hb, conj_conj]
    have e4 : ‖f2 ι x‖ = ‖ι (D.host.φ₀ (x : D.host.E))‖⁻¹ := by
      have : ‖ι (D.host.φ₀ (x : D.host.E))‖ * ‖f2 ι x‖ = 1 := by
        show _ * ‖ι ((starRingEnd ℂ) (D.host.φ₀ (x : D.host.E)))‖ = 1
        rw [← norm_mul, ← map_mul, hU, map_one, norm_one]
      exact eq_inv_of_mul_eq_one_right this
    have hA0 : ‖f2 ι ((k.pi p : 𝓞 D.host.K) : D.host.K)‖ ≠ 0 := by
      intro h0
      have := norm_eq_zero.1 h0
      have h1 := (map_eq_zero (f2 ι)).1 this
      exact k.pi_ne_zero p hp.out hs (by exact_mod_cast h1)
    rw [e3, e2]
    rw [e4, inv_pow, ← hy] at e1
    have e5 : ‖ι (D.host.φ₀ (x : D.host.E))‖ ^ classNumber D.host.K
        = (‖f2 ι ((k.pi p : 𝓞 D.host.K) : D.host.K)‖ ^ (k.yP p))⁻¹ := by rw [← e1, inv_inv]
    rw [e5, one_div, inv_zpow, zpow_neg, inv_inv]
    exact mul_inv_cancel₀ (zpow_ne_zero _ hA0)

end Kap

section Main

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappaAt_split (hsd : IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) B.latA) (p : ℕ) [hp : Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) (hs : SplitK D p) : B.KappaAt p ι := by
  intro u hiso _ h2 _
  rw [det_compare B hsd p ι (B.kc.gaP p) (B.kc.gaP_at p hp.out hs) u hiso h2]
  exact kappa_split B.kc ι hs

end Main

end Formalism.L2.Ker.KS
