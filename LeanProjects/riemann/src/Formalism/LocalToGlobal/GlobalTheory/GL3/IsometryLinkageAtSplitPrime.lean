import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PUnitBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsometryLinkageTrivialLevel

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.GP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.FrobeniusOrbits Classical

variable (D : D7)

def OO : Subring D.host.K := (algebraMap (𝓞 D.host.K) D.host.K).range

def LL : AddSubgroup D.host.E := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup

theorem memO_iff (t : D.host.K) : t ∈ OO D ↔ IsIntegral ℤ t :=
  ⟨by rintro ⟨y, rfl⟩; exact y.isIntegral_coe, fun h => ⟨⟨t, h⟩, rfl⟩⟩

theorem psi_cK (t : D.host.K) : AR.psi D (G0.cK D t) = starRingEnd ℂ (AR.psi D t) :=
  CU.emb_conj D D.host.φ₀ (t : D.host.E)

theorem int_mul_mem {z x : D.host.E} (hz : IsIntegral ℤ z) (hx : x ∈ LL D) : z * x ∈ LL D := by
  have h2 : ((⟨z, hz⟩ : 𝓞 D.host.E) • x) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
    Submodule.smul_mem _ _ hx
  have e : ((⟨z, hz⟩ : 𝓞 D.host.E) • x) = z * x := by rw [Algebra.smul_def]; rfl
  rw [e] at h2
  exact h2

theorem hK_rat (x : D.host.E) : ∃ p : ℚ, 0 ≤ p ∧ G0.hK D x x = ((p : ℚ) : D.host.K) := by
  have hφ : D.host.φ₀ ((G0.hK D x x : D.host.K) : D.host.E)
      = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ) := by
    show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _
    rw [← FL.sum_tau_trace]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, CU.emb_conj, Complex.mul_conj]
  have hpos : 0 ≤ ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) :=
    Finset.sum_nonneg fun τ _ => Complex.normSq_nonneg _
  obtain ⟨p, q, e⟩ := CS.K_repr D _ (G0.hK D x x).2
  have hs := IO.sqrt_d_pos D
  rw [e, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d] at hφ
  have him := congrArg Complex.im hφ
  have hre := congrArg Complex.re hφ
  simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre
  have hq : (q : ℝ) = 0 := by
    have : (q : ℝ) * Real.sqrt D.host.d = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hs.ne'
  have hq' : q = 0 := by exact_mod_cast hq
  have hp : (0 : ℝ) ≤ (p : ℝ) := by rw [hq] at hre; linarith
  refine ⟨p, by exact_mod_cast hp, ?_⟩
  apply Subtype.ext
  rw [e, hq']
  show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)
  rw [map_ratCast]; simp

theorem hK_nat (x : D.host.E) (hx : x ∈ LL D) : ∃ n : ℕ, G0.hK D x x = (n : D.host.K) := by
  obtain ⟨p, hp, e⟩ := hK_rat D x
  have hint : IsIntegral ℤ (G0.hK D x x) := TI.trace_conj_integral D x x hx hx
  rw [e] at hint
  have h2 : IsIntegral ℤ ((p : ℚ) : ℂ) := by
    have := hint.map (AR.psi D).toIntAlgHom
    simpa using this
  obtain ⟨n, hn⟩ := AR.int_of_rat p h2
  have hn0 : 0 ≤ n := by rw [hn] at hp; exact_mod_cast hp
  refine ⟨n.toNat, ?_⟩
  rw [e, hn]
  have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
  conv_lhs => rw [← this]
  push_cast; rfl

theorem crit (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ D.host.d) (t : D.host.K) (ht : t ∈ OO D)
    (h1 : ∃ k : ℤ, t + G0.cK D t = (p : D.host.K) * k)
    (h2 : ∃ k : ℤ, ((AR.om D : 𝓞 D.host.K) : D.host.K) * t + G0.cK D (((AR.om D : 𝓞 D.host.K) : D.host.K) * t)
      = (p : D.host.K) * k) : ∃ t' ∈ OO D, t = (p : D.host.K) * t' := by
  obtain ⟨o, rfl⟩ := ht
  obtain ⟨x, y, -, hxy⟩ := AR.okc_of D o
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  have hψ : AR.psi D (algebraMap (𝓞 D.host.K) D.host.K o) = ((x : ℂ) + (y : ℂ) * AR.be D) / 2 := hxy
  have hω : AR.psi D ((AR.om D : 𝓞 D.host.K) : D.host.K) = (1 + AR.be D) / 2 := AR.ph_om D
  have hb2 := AR.be_sq D
  have hbc := AR.conj_be D
  have e1 : (x : ℂ) = (p : ℂ) * k := by
    have := congrArg (AR.psi D) hk
    rw [map_add, psi_cK, hψ] at this
    simp only [map_mul, map_div₀, map_add, hbc, map_intCast, map_natCast, map_ofNat] at this
    linear_combination this
  have e2 : (x : ℂ) - (D.host.d : ℂ) * y = 2 * (p : ℂ) * k' := by
    have := congrArg (AR.psi D) hk'
    rw [map_add, psi_cK, map_mul, hψ, hω] at this
    simp only [map_mul, map_div₀, map_add, hbc, map_intCast, map_natCast, map_ofNat, map_one] at this
    linear_combination 2 * this - (y : ℂ) * hb2
  have e1' : x = (p : ℤ) * k := by exact_mod_cast e1
  have e2' : x - (D.host.d : ℤ) * y = 2 * (p : ℤ) * k' := by exact_mod_cast e2
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hdy : (p : ℤ) ∣ (D.host.d : ℤ) * y := ⟨k - 2 * k', by linarith⟩
  obtain ⟨y', hy'⟩ : (p : ℤ) ∣ y := by
    rcases hpp.dvd_or_dvd hdy with h | h
    · exact absurd (Int.natCast_dvd_natCast.1 h) hpd
    · exact h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e3 : k - (D.host.d : ℤ) * y' = 2 * k' := by
    apply mul_left_cancel₀ hp0
    rw [hy'] at e2'
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℤ, (D.host.d : ℤ) = 2 * e + 1 := ⟨(D.host.d : ℤ) / 2, by have := D.host.hyp.2.2.2.1; omega⟩
  refine ⟨((k' + e * y' : ℤ) : D.host.K) + ((y' : ℤ) : D.host.K) * ((AR.om D : 𝓞 D.host.K) : D.host.K),
    (OO D).add_mem (intCast_mem _ _) ((OO D).mul_mem (intCast_mem _ _) ⟨AR.om D, rfl⟩), ?_⟩
  apply (AR.psi D).injective
  rw [hψ, map_mul, map_add, map_mul, hω, map_natCast, map_intCast, map_intCast]
  have hkC : (k : ℂ) = (y' : ℂ) + 2 * ((k' + e * y' : ℤ) : ℂ) := by
    have : k = y' + 2 * (k' + e * y') := by rw [he] at e3; linarith
    exact_mod_cast this
  have hyC : (y : ℂ) = (p : ℂ) * y' := by exact_mod_cast hy'
  rw [e1, hyC, hkC]
  ring

theorem plat (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ D.host.d) : FS.PLat (G0.cK D) (G0.hK D) (OO D) (LL D) p where
  herm := G0.herm D
  prime := hp
  cO t ht := (memO_iff D _).2 (((memO_iff D t).1 ht).map (G0.cK D).toIntAlgHom)
  smul o ho x hx := by
    obtain ⟨o', rfl⟩ := ho
    rw [Algebra.smul_def]
    exact int_mul_mem D (FL.intK D o') hx
  int x hx y hy := (memO_iff D _).2 (TI.trace_conj_integral D x y hx hy)
  unim x h :=
    (D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 x).2 (fun y hy => h y hy)
  full x := by
    obtain ⟨m, hm, h⟩ := SO.exists_nat_mul D.host.E {x}
    refine ⟨m, hm, ?_⟩
    rw [Algebra.smul_def, map_natCast]
    exact SO.int_mem_inverse_half_different (h x (Finset.mem_singleton_self x))
  nat := hK_nat D
  crit := ⟨_, ⟨AR.om D, rfl⟩, fun t ht h1 h2 => crit D p hp hpd t ht h1 h2⟩

theorem not_dvd_of_split (p : ℕ) (hp : p.Prime) (hs : SplitK D p) : ¬ p ∣ D.host.d := by
  intro hd
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have e : p = D.host.d := (Nat.prime_dvd_prime_iff_eq hp hdp).1 hd
  have h16 := D.host.hyp.2.2.2.1
  rcases hs with h | h
  · omega
  · rw [e] at h
    have : NeZero D.host.d := ⟨hdp.ne_zero⟩
    have h0 : jacobiSym (-(D.host.d : ℤ)) D.host.d = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      have e2 : (-(D.host.d : ℤ)).gcd (D.host.d : ℤ) = D.host.d := by simp
      rw [e2]
      exact hdp.one_lt.ne'
    rw [h0] at h
    exact zero_ne_one h

theorem isoP (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ D.host.d) : ∃ γ : IsoK D, γ.AtP p := by
  obtain ⟨g, hg, s, hcop, h1, h2⟩ := (plat D p hp hpd).iso (ι := D.what₂.Tau) (G0.card_eq D)
  refine ⟨⟨g, fun x y => ?_⟩, fun x hx => ⟨s, hcop, fun w => h1 x hx w⟩, fun v hv => ⟨s, hcop, fun a => ?_⟩⟩
  · have h3 : (∑ a, Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a))) = ∑ w, g x w * G0.cK D (g y w) :=
      (hg x y).symm
    rw [h3, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul]
    rfl
  · have := h2 v hv a
    rw [Algebra.smul_def, map_natCast] at this
    exact this

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.GP

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def LinkIsoP : Prop := ∀ D : D7, IsoPExists D

def LinkBaseEx : Prop := ∀ D : D7, BaseExists D

def LinkSplitPrimeIsometry : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

theorem isometry_linkage_at_split_prime : LinkIsoP := fun D p hp hs => GP.isoP D p hp (GP.not_dvd_of_split D p hp hs)

theorem base_linkage_exists : LinkBaseEx := fun D => base_linkage_at_prime D (isometry_linkage_at_split_prime D)

theorem eigen_linkage_all_primes : LinkSplitPrimeIsometry :=
  fun D C hA hper hΔ h => eigen_linkage_at_prime D C hA hper hΔ (isometry_linkage_at_split_prime D) h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
