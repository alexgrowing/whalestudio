import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

section arith

open NumberField IsLocalization
open scoped nonZeroDivisors

namespace GlobalTheory.NormUnitInert.Arith

variable {K : Type*} [Field K] [NumberField K]

theorem cancel_coe {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) {A B : Submodule (𝓞 K) K}
    (h : coeSubmodule K P * A = coeSubmodule K P * B) : A = B := by
  have hP0 : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP
  have hinv : ((((P : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) *
      coeSubmodule K P = 1 := by
    rw [← FractionalIdeal.coe_coeIdeal, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hP0, FractionalIdeal.coe_one]
  calc A = 1 * A := (one_mul A).symm
    _ = _ * (coeSubmodule K P * A) := by rw [← hinv, mul_assoc]
    _ = _ * (coeSubmodule K P * B) := by rw [h]
    _ = B := by rw [← mul_assoc, hinv, one_mul]

theorem coprime_absNorm (p : ℕ) [hp : Fact p.Prime] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.out.one_lt.ne hx

section main

variable (c : K ≃+* K) (p : ℕ) [hp : Fact p.Prime] (𝔞 𝔟 : Submodule (𝓞 K) K)

def Cnd (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ coeSubmodule K I * 𝔞 = coeSubmodule K (I.map (RingOfIntegers.mapRingEquiv c))

def Goal : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ 𝔞, (s : K) * x ∈ (1 : Submodule (𝓞 K) K)) ∧ (s : K) ∈ 𝔞

variable {c p 𝔞 𝔟}

theorem coe_le_one (I : Ideal (𝓞 K)) : coeSubmodule K I ≤ 1 := by
  rw [← coeSubmodule_top]; exact coeSubmodule_mono _ le_top

theorem goal_of_top {I : Ideal (𝓞 K)} (hC : Cnd c 𝔞 I) (htop : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) :
    Goal p 𝔞 := by
  refine ⟨Ideal.absNorm I, coprime_absNorm p hC.1 htop, fun x hx => ?_, ?_⟩
  · have hs : ((Ideal.absNorm I : ℕ) : K) ∈ coeSubmodule K I :=
      (mem_coeSubmodule _ _).2 ⟨_, Ideal.absNorm_mem I, map_natCast _ _⟩
    have h := Submodule.mul_mem_mul hs hx
    rw [hC.2] at h
    exact coe_le_one _ h
  · have hs : ((Ideal.absNorm I : ℕ) : 𝓞 K) ∈ I.map (RingOfIntegers.mapRingEquiv c) := by
      have := Ideal.mem_map_of_mem (RingOfIntegers.mapRingEquiv c) (Ideal.absNorm_mem I)
      rwa [map_natCast] at this
    have hs' : ((Ideal.absNorm I : ℕ) : K) ∈ coeSubmodule K (I.map (RingOfIntegers.mapRingEquiv c)) :=
      (mem_coeSubmodule _ _).2 ⟨_, hs, map_natCast _ _⟩
    rw [← hC.2] at hs'
    have hle : coeSubmodule K I * 𝔞 ≤ 𝔞 := by
      rw [Submodule.mul_le]
      intro m hm n hn
      obtain ⟨y, -, rfl⟩ := (mem_coeSubmodule _ _).1 hm
      rw [← Algebra.smul_def]
      exact 𝔞.smul_mem y hn
    exact hle hs'

theorem descent (hst : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P →
      P.map (RingOfIntegers.mapRingEquiv c) = P)
    {I : Ideal (𝓞 K)} (hC : Cnd c 𝔞 I) {P : Ideal (𝓞 K)} (hPp : P.IsPrime) (hP0 : P ≠ ⊥)
    (hpP : ((p : ℕ) : 𝓞 K) ∈ P) (hIP : I ≤ P) :
    ∃ I', Cnd c 𝔞 I' ∧ Ideal.absNorm I' < Ideal.absNorm I := by
  obtain ⟨I', rfl⟩ := Ideal.dvd_iff_le.mpr hIP
  have hI' : I' ≠ ⊥ := by
    rintro rfl
    exact hC.1 (by rw [Ideal.mul_bot])
  refine ⟨I', ⟨hI', cancel_coe hP0 ?_⟩, ?_⟩
  · have h := hC.2
    rw [Ideal.map_mul, hst P hPp hP0 hpP, coeSubmodule_mul, coeSubmodule_mul, mul_assoc] at h
    exact h
  · rw [map_mul]
    have h1 : Ideal.absNorm P ≠ 1 := fun h => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)
    have h0' : Ideal.absNorm I' ≠ 0 := fun h => hI' (Ideal.absNorm_eq_zero_iff.mp h)
    have h2 : 2 ≤ Ideal.absNorm P := by omega
    have h3 : 1 ≤ Ideal.absNorm I' := by omega
    nlinarith

theorem goal_of_cnd (hst : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P →
      P.map (RingOfIntegers.mapRingEquiv c) = P) :
    ∀ n, ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → Cnd c 𝔞 I → Goal p 𝔞 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hn hC
    by_cases htop : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤
    · exact goal_of_top hC htop
    · obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal _ htop
      have hpP : ((p : ℕ) : 𝓞 K) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      have hP0 : P ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hpP
        exact hp.out.ne_zero (by exact_mod_cast hpP)
      obtain ⟨I', hC', hlt⟩ := descent hst hC hPm.isPrime hP0 hpP (le_sup_left.trans hle)
      exact ih _ (hn ▸ hlt) I' rfl hC'

theorem mem_comap_integers_fractionalIdeal_iff (y : 𝓞 K) : y ∈ Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟 ↔ (y : K) ∈ 𝔟 := Iff.rfl

theorem idealDescent_conjInvariant_of_inverse (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (hab : 𝔞 * 𝔟 = 1) :
    Cnd c 𝔞 (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) := by
  have hba : 𝔟 * 𝔞 = 1 := by rw [mul_comm]; exact hab

  have hint : ∀ a ∈ 𝔞, ∀ b ∈ 𝔟, a * b ∈ (1 : Submodule (𝓞 K) K) := fun a ha b hb' => by
    rw [← hab]; exact Submodule.mul_mem_mul ha hb'
  refine ⟨?_, le_antisymm ?_ ?_⟩
  ·
    have hb0 : 𝔟 ≠ ⊥ := by
      rintro rfl
      rw [Submodule.mul_bot] at hab
      have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.mp le_rfl
      rw [← hab, Submodule.mem_bot] at h1
      exact one_ne_zero h1
    obtain ⟨b, hbm, hb0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb0
    obtain ⟨⟨z, d⟩, hz⟩ := IsLocalization.surj (𝓞 K)⁰ b
    simp only at hz
    intro hbot
    have hzmem : z ∈ Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟 := by
      rw [mem_comap_integers_fractionalIdeal_iff]
      have : (z : K) = (d : 𝓞 K) • b := by
        rw [Algebra.smul_def, mul_comm]; exact hz.symm
      rw [this]; exact 𝔟.smul_mem _ hbm
    rw [hbot, Ideal.mem_bot] at hzmem
    subst hzmem
    have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    rw [map_zero] at hz
    exact hb0' ((mul_eq_zero.mp hz).resolve_right hd0)
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨y, hy, rfl⟩ := (mem_coeSubmodule _ _).1 hm
    have hyn : algebraMap (𝓞 K) K y * n ∈ (1 : Submodule (𝓞 K) K) := by
      rw [mul_comm]; exact hint n hn _ hy
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp hyn
    refine (mem_coeSubmodule _ _).2 ⟨z, ?_, hz⟩
    refine (Ideal.mem_map_of_equiv (RingOfIntegers.mapRingEquiv c) z).2
      ⟨(RingOfIntegers.mapRingEquiv c).symm z, ?_, (RingOfIntegers.mapRingEquiv c).apply_symm_apply z⟩
    rw [mem_comap_integers_fractionalIdeal_iff, hb, RingOfIntegers.mapRingEquiv_symm_apply, RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 K) K z ∈ 𝔞
    rw [hz, ← Algebra.smul_def]
    exact 𝔞.smul_mem y hn
  · intro m hm
    obtain ⟨z, hz, rfl⟩ := (mem_coeSubmodule _ _).1 hm
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_of_equiv (RingOfIntegers.mapRingEquiv c) z).1 hz
    have hwa : c (w : K) ∈ 𝔞 := (hb _).1 ((mem_comap_integers_fractionalIdeal_iff w).1 hw)
    have hzK : algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv c w) = c (w : K) := rfl
    rw [hzK]
    set z' : 𝓞 K := RingOfIntegers.mapRingEquiv c w with hz'
    have hz'K : (z' : K) = c (w : K) := rfl

    have hsp : Submodule.span (𝓞 K) {(z' : K)} * 𝔟 ≤ coeSubmodule K (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) := by
      rw [Submodule.mul_le]
      intro u hu n hn
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ r ?_
      obtain ⟨q, hq⟩ := Submodule.mem_one.mp (hint _ (hz'K ▸ hwa) n hn)
      refine (mem_coeSubmodule _ _).2 ⟨q, ?_, hq⟩
      rw [mem_comap_integers_fractionalIdeal_iff]
      change algebraMap (𝓞 K) K q ∈ 𝔟
      rw [hq, ← Algebra.smul_def]
      exact 𝔟.smul_mem z' hn
    have h1 : (1 : K) ∈ 𝔟 * 𝔞 := by rw [hba]; exact Submodule.one_le.mp le_rfl
    have hmem : (z' : K) * 1 ∈ Submodule.span (𝓞 K) {(z' : K)} * (𝔟 * 𝔞) :=
      Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) h1
    rw [mul_one, ← mul_assoc] at hmem
    rw [← hz'K]
    have hle : Submodule.span (𝓞 K) {(z' : K)} * 𝔟 * 𝔞 ≤
        coeSubmodule K (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) * 𝔞 := by
      rw [Submodule.mul_le]
      intro u hu a ha
      exact Submodule.mul_mem_mul (hsp hu) ha
    exact hle hmem

theorem fractionalIdealUnitAtPrime_of_conj_inverse (hst : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P →
      P.map (RingOfIntegers.mapRingEquiv c) = P)
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (hab : 𝔞 * 𝔟 = 1) : Goal p 𝔞 :=
  goal_of_cnd hst _ _ rfl (idealDescent_conjInvariant_of_inverse hb hab)

end main

end GlobalTheory.NormUnitInert.Arith

end arith

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace GlobalTheory.NormUnitInert

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormUnitK (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ z : D.host.E, z * D.host.conj z = 1 → ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z)‖ = 1

theorem lamC_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

def FrobOut (D : D7) (p : ℕ) : Prop :=
  ∃ g : D.R.GG, g ∉ D.R.Psi ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 D.host.E) ∈ P →

    P.map (RingOfIntegers.mapRingEquiv (D.host.sigmaOf g : D.host.E ≃+* D.host.E)) = P

section nu

variable {D : D7}

theorem sigmaOf_mul' (g h : D.R.GG) : D.host.sigmaOf (g * h) = D.host.sigmaOf g * D.host.sigmaOf h :=
  map_mul (D.host.gal).symm g h

theorem conj_eq' : D.host.conj = D.host.sigmaOf (D.R.cc) := rfl

theorem conj_sigmaOf (g : D.R.GG) (x : D.host.E) :
    D.host.conj (D.host.sigmaOf g x) = D.host.sigmaOf g (D.host.conj x) := by
  rw [conj_eq']
  change (D.host.sigmaOf (D.R.cc) * D.host.sigmaOf g) x = (D.host.sigmaOf g * D.host.sigmaOf (D.R.cc)) x
  rw [← sigmaOf_mul', ← sigmaOf_mul', mul_comm]

theorem conj_conj' (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [conj_eq']
  change (D.host.sigmaOf (D.R.cc) * D.host.sigmaOf (D.R.cc)) x = x
  rw [← sigmaOf_mul']
  have : D.R.cc * D.R.cc = 1 := by
    exact Prod.ext (by change c0 * c0 = 1; decide) (mul_one _)
  rw [this, show D.host.sigmaOf 1 = 1 from map_one (D.host.gal).symm]
  rfl

def nPsi (D : D7) (z : D.host.E) : D.host.E := ∏ τ : D.what₂.Tau, D.host.sigmaOf (D.eTau τ : D.R.GG) z

theorem nPsi_inv {ρ : D.R.GG} (hρ : ρ ∈ D.R.Psi) (z : D.host.E) :
    D.host.sigmaOf ρ (nPsi D z) = nPsi D z := by
  unfold nPsi
  rw [map_prod]
  let e : D.what₂.Tau ≃ D.what₂.Tau := (D.eTau.trans (Equiv.mulLeft (⟨ρ, hρ⟩ : D.R.Psi))).trans D.eTau.symm
  refine Fintype.prod_equiv e _ _ fun τ => ?_
  simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.coe_mulLeft, Subgroup.coe_mul]
  rw [sigmaOf_mul']
  rfl

theorem nPsi_conj {z : D.host.E} (hz : z * D.host.conj z = 1) : nPsi D z * D.host.conj (nPsi D z) = 1 := by
  unfold nPsi
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [conj_sigmaOf, ← map_mul, hz, map_one]

theorem prod_embT (z : D.host.E) : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z = D.host.φ₀ (nPsi D z) := by
  unfold nPsi
  rw [map_prod]
  rfl

theorem normUnitK_of_frobOut {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (hF : FrobOut D p) :
    NormUnitK D p lam := by
  intro z hz
  obtain ⟨g, hg, hst⟩ := hF
  set y := nPsi D z with hy
  have hyc : y * D.host.conj y = 1 := nPsi_conj hz
  have hy0 : y ≠ 0 := by rintro h; rw [h, zero_mul] at hyc; exact zero_ne_one hyc

  have hρ : (D.R.cc)⁻¹ * g ∈ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
    have h1 : ((D.R.cc)⁻¹ * g).1.2 = (D.R.cc).1.2⁻¹ * g.1.2 := rfl
    have h2 : (D.R.cc).1.2 = -1 := rfl
    rw [h1, h2]
    rcases Int.units_eq_one_or g.1.2 with h | h
    · exact absurd h hg
    · rw [h]; decide
  have hgy : D.host.sigmaOf g y = D.host.conj y := by
    have : g = D.R.cc * ((D.R.cc)⁻¹ * g) := by rw [mul_inv_cancel_left]
    rw [this, sigmaOf_mul', AlgEquiv.mul_apply, nPsi_inv hρ, ← conj_eq']
  have hgcy : D.host.sigmaOf g (D.host.conj y) = y := by
    rw [← conj_sigmaOf, hgy, conj_conj']

  set c : D.host.E ≃+* D.host.E := (D.host.sigmaOf g : D.host.E ≃+* D.host.E) with hc
  have hcx : ∀ x, c x = D.host.sigmaOf g x := fun x => rfl
  have hb : ∀ x, x ∈ Submodule.span (𝓞 D.host.E) {D.host.conj y} ↔ c x ∈ Submodule.span (𝓞 D.host.E) {y} := by
    intro x
    simp only [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨RingOfIntegers.mapRingEquiv c r, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcx (D.host.conj y), hgcy]
      rfl
    · rintro ⟨r, hr⟩
      refine ⟨(RingOfIntegers.mapRingEquiv c).symm r, c.injective ?_⟩
      rw [Algebra.smul_def, map_mul, hcx (D.host.conj y), hgcy, ← hr, Algebra.smul_def]
      congr 1
      change c (c.symm (r : D.host.E)) = (r : D.host.E)
      exact c.apply_symm_apply _
  have hab : Submodule.span (𝓞 D.host.E) {y} * Submodule.span (𝓞 D.host.E) {D.host.conj y} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hyc, ← Submodule.one_eq_span]
  obtain ⟨s, hs, h1, h2⟩ := Arith.fractionalIdealUnitAtPrime_of_conj_inverse (c := c) (p := p) hst hb hab
  have hA : (s : D.host.E) * y ∈ (1 : TaylorLogMetric.IdE D) := h1 y (Submodule.mem_span_singleton_self y)
  have hB : (s : D.host.E) * D.host.conj y ∈ (1 : TaylorLogMetric.IdE D) := by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h2
    rw [← hr, Algebra.smul_def, mul_assoc, hyc, mul_one]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  let τ₁ : D.what₂.Tau := D.eTau.symm 1
  have hemb : ∀ x, TaylorLogMetric.embT D τ₁ x = D.host.φ₀ (D.host.sigmaOf (D.eTau τ₁ : D.R.GG) x) := fun x => rfl
  have hτ₁ : (D.eTau τ₁ : D.R.GG) = 1 := by simp [τ₁]
  have hn : ‖(s : ℂ_[p])‖ = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p hs
  have hprod : lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y)) *
      lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y)) = (s : ℂ_[p]) ^ 2 := by
    rw [← map_mul, ← map_mul]
    have e : (s : D.host.E) * y * ((s : D.host.E) * D.host.conj y) = (s : D.host.E) ^ 2 := by
      rw [show (s : D.host.E) * y * ((s : D.host.E) * D.host.conj y) = (s : D.host.E) ^ 2 * (y * D.host.conj y) by ring,
        hyc, mul_one]
    rw [e, map_pow, map_pow, map_natCast, map_natCast]
  have a1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_lam_int lam τ₁ hA
  have b1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_lam_int lam τ₁ hB
  have hnorm : ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y))‖ *
      ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y))‖ = 1 := by
    rw [← norm_mul, hprod, norm_pow, hn, one_pow]
  have hA1 : ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y))‖ = 1 := by
    have n0 := norm_nonneg (lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y)))
    have n1 := norm_nonneg (lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y)))
    nlinarith
  simp only [map_mul, map_natCast, norm_mul, hn, one_mul] at hA1

  have hP : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z = TaylorLogMetric.embT D τ₁ y := by
    rw [prod_embT, hemb, nPsi_inv (D.eTau τ₁).2]
  rw [hP, lamC_of_mem lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.emb_mem τ₁ y)]
  exact hA1

end nu

section frob

open scoped Pointwise

variable {D : D7}

set_option maxHeartbeats 400000 in

theorem frobOut_of_inertK {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hI : Formalism.MainNotions.GL3Theta.InertK D p) : FrobOut D p := by
  classical
  let G := 𝓞 D.host.E ≃ₐ[ℤ] 𝓞 D.host.E
  have hGal : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hInv : Algebra.IsInvariant ℤ (𝓞 D.host.E) G := Algebra.isInvariant_of_isGalois' ℤ ℚ D.host.E (𝓞 D.host.E)
  have hFin : Finite G := Finite.of_equiv _ (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).toEquiv
  have hcomm : ∀ σ τ : G, σ * τ = τ * σ := by
    intro σ τ
    apply (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).symm.injective
    apply (D.host.gal).injective
    simp only [map_mul]
    exact mul_comm _ _

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  obtain ⟨Q₀, hQm, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(p : ℤ)})
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by rw [RingHom.mem_ker] at hx; rw [hx, map_zero])
      rw [this]; exact Submodule.zero_mem _)
  have hunder : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((p : ℕ) : 𝓞 D.host.E) ∈ P →
      P.under ℤ = Ideal.span {(p : ℤ)} := by
    intro P hP hpP
    refine (hPmax.eq_of_le ?_ ?_).symm
    · intro h
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [h]; trivial
      rw [Ideal.under_def, Ideal.mem_comap, map_one] at h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
      simpa using hpP
  have hpQ : ((p : ℕ) : 𝓞 D.host.E) ∈ Q₀ := by
    have : (p : ℤ) ∈ Q₀.comap (algebraMap ℤ (𝓞 D.host.E)) := by rw [hQc]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at this
    simpa using this
  have hQ0 : Q₀ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact hp.out.ne_zero (by exact_mod_cast hpQ)
  have hQfin : Finite (𝓞 D.host.E ⧸ Q₀) := Ideal.finiteQuotientOfFreeOfNeBot Q₀ hQ0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ G Q₀
  have hstab : σ • Q₀ = Q₀ := MulAction.mem_stabilizer_iff.mp hσ.mem_stabilizer

  have hfix : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((p : ℕ) : 𝓞 D.host.E) ∈ P → σ • P = P := by
    intro P hP hpP
    have hu : Q₀.under ℤ = P.under ℤ := by
      rw [hunder P hP hpP, hunder Q₀ hQm.isPrime hpQ]
    obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 D.host.E) G Q₀ P hu
    rw [hτ, smul_smul, hcomm, ← smul_smul, hstab]

  let τ' : D.host.E ≃ₐ[ℚ] D.host.E := (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).symm σ
  let g : D.R.GG := D.host.gal τ'
  have hsg : D.host.sigmaOf g = τ' := by
    change (D.host.gal).symm (D.host.gal τ') = τ'
    exact MulEquiv.symm_apply_apply _ _
  have hfun : ∀ x : 𝓞 D.host.E,
      RingOfIntegers.mapRingEquiv (D.host.sigmaOf g : D.host.E ≃+* D.host.E) x = σ • x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have h1 : σ = galRestrict ℤ ℚ D.host.E (𝓞 D.host.E) τ' := (MulEquiv.apply_symm_apply _ σ).symm
    have h2 := algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := D.host.E) (B := 𝓞 D.host.E) τ' x
    rw [← h1] at h2
    change (D.host.sigmaOf g) (x : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (σ x)
    rw [h2, hsg]
  refine ⟨g, ?_, ?_⟩
  ·
    intro hgPsi
    have hbK : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
    have hb := Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host g hgPsi _ hbK
    have hbsq : D.host.sqrtMinusD ^ 2 = -((D.host.d : ℕ) : D.host.E) := D.host.sqrtMinusD_sq
    have hint : IsIntegral ℤ D.host.sqrtMinusD := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hbsq]
      have : -((D.host.d : ℕ) : D.host.E) = algebraMap ℤ D.host.E (-(D.host.d : ℤ)) := by push_cast; rfl
      rw [this]
      exact isIntegral_algebraMap
    let β : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, hint⟩
    have hβsq : β ^ 2 = ((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      push_cast
      exact hbsq
    have hσβ : σ • β = β := by
      rw [← hfun]
      apply RingOfIntegers.ext
      rw [RingOfIntegers.mapRingEquiv_apply]
      exact hb

    have hcard : Nat.card (ℤ ⧸ Q₀.under ℤ) = p := by
      rw [hunder Q₀ hQm.isPrime hpQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
    have hfr := hσ β
    rw [hcard] at hfr
    change σ • β - β ^ p ∈ Q₀ at hfr
    rw [hσβ] at hfr

    have hl : legendreSym p (-(D.host.d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hI
    have he := legendreSym.eq_pow p (-(D.host.d : ℤ))
    rw [hl] at he
    obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) ((-(D.host.d : ℤ)) ^ (p / 2)) p).mp (by push_cast at he ⊢; exact he)
    have hodd : p = 2 * (p / 2) + 1 := by
      rcases hp.out.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · obtain ⟨k, hk⟩ := h; omega
    have hβp : β ^ p = β * (((-(D.host.d : ℤ)) ^ (p / 2) : ℤ) : 𝓞 D.host.E) := by
      conv_lhs => rw [hodd]
      rw [pow_succ, pow_mul, hβsq, mul_comm]
      push_cast
      ring
    have h2β : 2 * β ∈ Q₀ := by
      have e1 : ((-(D.host.d : ℤ)) ^ (p / 2) : ℤ) = -1 + p * t := by linarith
      rw [hβp, e1] at hfr
      have e2 : 2 * β = (β - β * (((-1 + p * t : ℤ)) : 𝓞 D.host.E)) + ((p : ℕ) : 𝓞 D.host.E) * ((t : 𝓞 D.host.E) * β) := by
        push_cast; ring
      rw [e2]
      exact Q₀.add_mem hfr (Q₀.mul_mem_right _ hpQ)
    have h4d : (((-4 * (D.host.d : ℤ)) : ℤ) : 𝓞 D.host.E) ∈ Q₀ := by
      have : (((-4 * (D.host.d : ℤ)) : ℤ) : 𝓞 D.host.E) = (2 * β) * (2 * β) := by
        rw [show (2 * β) * (2 * β) = 4 * β ^ 2 by ring, hβsq]; push_cast; ring
      rw [this]; exact Q₀.mul_mem_right _ h2β
    have hdvd : (p : ℤ) ∣ -4 * (D.host.d : ℤ) := by
      have : (-4 * (D.host.d : ℤ)) ∈ Q₀.comap (algebraMap ℤ (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap]; simpa using h4d
      rw [hQc, Ideal.mem_span_singleton] at this
      exact this
    rw [neg_mul, dvd_neg] at hdvd
    rcases hpZ.dvd_or_dvd hdvd with h4 | hd
    · have : (p : ℤ) ∣ 2 * 2 := by norm_num at h4 ⊢; exact h4
      rcases hpZ.dvd_or_dvd this with h2 | h2 <;>
      · have h2' : p ∣ 2 := by exact_mod_cast h2
        rcases (Nat.prime_two.eq_one_or_self_of_dvd p h2') with h | h
        · exact hp.out.one_lt.ne' h
        · exact hp2 h
    · have h0 : ((-(D.host.d : ℤ) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((dvd_neg).mpr hd)
      have := (legendreSym.eq_zero_iff p (-(D.host.d : ℤ))).mpr h0
      rw [hl] at this
      norm_num at this
  ·
    intro P hP hP0 hpP
    have hσP := hfix P hP hpP
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hfun]
      have := Ideal.smul_mem_pointwise_smul σ x P hx
      rwa [hσP] at this
    · intro hy
      refine ⟨σ⁻¹ • y, ?_, ?_⟩
      · rw [← hσP] at hy
        have : σ • (σ⁻¹ • y) ∈ σ • P := by rwa [smul_inv_smul]
        exact (Ideal.smul_mem_pointwise_smul_iff).mp this
      · rw [hfun, smul_inv_smul]

theorem normUnitK_of_inertK {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (hp2 : p ≠ 2)
    (hI : Formalism.MainNotions.GL3Theta.InertK D p) : NormUnitK D p lam :=
  normUnitK_of_frobOut lam (frobOut_of_inertK hp2 hI)

end frob

end GlobalTheory.NormUnitInert

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct in

theorem GlobalTheory.normUnit_of_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 → GL3Theta.InertK D p →
    ∀ z : D.host.E, z * D.host.conj z = 1 → ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z)‖ = 1 :=
  fun _ _ _ lam hp2 hI => GlobalTheory.NormUnitInert.normUnitK_of_inertK lam hp2 hI
