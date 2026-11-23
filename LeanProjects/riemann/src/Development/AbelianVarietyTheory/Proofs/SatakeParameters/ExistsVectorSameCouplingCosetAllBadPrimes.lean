import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameCongApprox

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_val_le {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : P.valuation E a ≤ 1) : IntAt P a := by
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

theorem exists_depth (P : HeightOneSpectrum (𝓞 E)) {w : 𝓞 E} (hw : w ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P (algebraMap (𝓞 E) E z / algebraMap (𝓞 E) E w) := by
  have h0 : P.intValuation w ≠ 0 := P.intValuation_ne_zero w hw
  refine ⟨(P.intValuation w).log.natAbs, fun z hz => intAt_of_val_le ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_one₀ (zero_lt_iff.2 h0)]
  refine ((P.intValuation_le_pow_iff_mem z _).2 hz).trans ?_
  conv_rhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) (t : T → E) (u : T → 𝓞 E) (hu : ∀ P, u P ≠ 0) :
    ∃ y : E, ∀ P : T, IntAt P.1 ((y - t P) / algebraMap (𝓞 E) E (u P)) := by
  have inj := IsFractionRing.injective (𝓞 E) E
  choose a b hb hab using fun P => IsFractionRing.div_surjective (𝓞 E) (t P)
  have hb0 : ∀ P, b P ≠ 0 := fun P => nonZeroDivisors.ne_zero (hb P)
  set D : 𝓞 E := ∏ Q, b Q with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q
  have hw : ∀ P, D * u P ≠ 0 := fun P => mul_ne_zero hD0 (hu P)
  choose k hk using fun P : T => exists_depth P.1 (hw P)
  obtain ⟨x, hx⟩ := exists_forall_sub_mem_ideal (s := T) (fun P => P.asIdeal)
    (fun P => if h : P ∈ T then k ⟨P, h⟩ else 0) (fun P _ => P.prime)
    (fun P _ Q _ h h' => h (HeightOneSpectrum.ext h')) (fun P => a P * ∏ Q ∈ Finset.univ.erase P, b Q)
  refine ⟨algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E D, fun P => ?_⟩
  have hxP := hx P.1 P.2
  simp only [dif_pos P.2] at hxP
  have h1 := hk P _ hxP
  convert h1 using 1
  have hsplit : D = b P * ∏ Q ∈ Finset.univ.erase P, b Q := (Finset.mul_prod_erase _ _ (Finset.mem_univ P)).symm
  have hbE : algebraMap (𝓞 E) E (b P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hb0 P)
  have hBE : algebraMap (𝓞 E) E (∏ Q ∈ Finset.univ.erase P, b Q) ≠ 0 :=
    (map_ne_zero_iff _ inj).2 (Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q)
  have huE : algebraMap (𝓞 E) E (u P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hu P)
  rw [← hab P, map_mul, map_sub, map_mul, hsplit, map_mul]
  field_simp

theorem exists_den {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ (P : HeightOneSpectrum (𝓞 E)) (z : Fin n → E), (∀ l, IntAt P (z l)) →
      ∀ l, IntAt P (algebraMap (𝓞 E) E d * g z l) := by
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => g (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun P z hz l => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ g z, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) fun j _ => ?_
  obtain ⟨r, hr⟩ := hdi (j, l) (Finset.mem_univ _)
  rw [Algebra.smul_def] at hr
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  exact (hz j).mul (by rw [← hr]; exact IntAt.coe P r)

end GlobalTheory.FrameCongApprox

namespace GlobalTheory.FrameCongApprox

theorem exists_sameCoset {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ}
    (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) := by
  have inj := IsFractionRing.injective (𝓞 X.E) X.E
  choose d hd0 hd using fun P : rowSG Pr sel mu => exists_den (fr P).symm.toLinearMap
  let e : rowSG Pr sel mu → ℕ := fun P => if P.1 ∈ Pr.vGs then 0 else cst.M
  let m : rowSG Pr sel mu → 𝓞 X.E := fun P => d P * ((qOf P.1 : ℕ) : 𝓞 X.E) ^ e P
  have hq : ∀ P : rowSG Pr sel mu, ((qOf P.1 : ℕ) : X.E) ≠ 0 := fun P => by
    rw [Nat.cast_ne_zero]
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hmE : ∀ P, algebraMap (𝓞 X.E) X.E (m P) = algebraMap (𝓞 X.E) X.E (d P) * ((qOf P.1 : ℕ) : X.E) ^ e P := fun P => by
    simp [m, map_mul, map_pow, map_natCast]
  have hm : ∀ P, m P ≠ 0 := fun P h => by
    have h2 := hmE P
    rw [h, map_zero] at h2
    exact mul_ne_zero ((map_ne_zero_iff _ inj).2 (hd0 P)) (pow_ne_zero _ (hq P)) h2.symm
  choose yl hyl using fun l : Fin n => exists_approx (rowSG Pr sel mu) (fun P => fr P (y0 P) l) m hm
  refine ⟨yl, fun P l => ?_⟩
  have hmP : algebraMap (𝓞 X.E) X.E (m P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hm P)
  set z : Sp X.E n := fun l => (yl l - fr P (y0 P) l) / algebraMap (𝓞 X.E) X.E (m P) with hz
  have hy : yl = fr P (y0 P) + algebraMap (𝓞 X.E) X.E (m P) • z := by
    funext l
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hdiff : (fr P).symm yl - y0 P = algebraMap (𝓞 X.E) X.E (m P) • (fr P).symm z := by
    rw [hy, map_add, map_smul, LinearEquiv.symm_apply_apply, add_sub_cancel_left]
  have key := hd P P.1 z (fun l => hyl l P) l
  show IntAt P.1 (((qOf P.1 : X.E) ^ e P)⁻¹ * ((fr P).symm yl - y0 P) l)
  rw [hdiff, Pi.smul_apply, smul_eq_mul, hmE]
  have : (((qOf P.1 : ℕ) : X.E) ^ e P)⁻¹ * (algebraMap (𝓞 X.E) X.E (d P) * ((qOf P.1 : ℕ) : X.E) ^ e P * (fr P).symm z l) =
      algebraMap (𝓞 X.E) X.E (d P) * (fr P).symm.toLinearMap z l := by
    have hqe := pow_ne_zero (e P) (hq P)
    simp only [LinearEquiv.coe_coe]
    field_simp
  rw [this]
  exact key

end GlobalTheory.FrameCongApprox
