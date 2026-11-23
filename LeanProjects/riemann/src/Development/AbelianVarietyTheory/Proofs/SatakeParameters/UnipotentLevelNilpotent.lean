import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDataRec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.UnipVol

section Group

theorem index_eq_prime_pow {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] {p : ℕ} (hp : p.Prime)
    (hroot : ∀ (g : G) (m : ℕ), m.Coprime p → g ^ m ∈ H → g ∈ H) : ∃ k, H.index = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ∀ (g : G) (m : ℕ), m.Coprime p → g ^ m ∈ H.normalCore → g ∈ H.normalCore := by
    intro g m hm hg
    have hg' : ∀ b : G, b * g ^ m * b⁻¹ ∈ H := hg
    show ∀ b : G, b * g * b⁻¹ ∈ H
    intro b
    refine hroot _ m hm ?_
    rw [conj_pow]
    exact hg' b
  have hfin : Finite (G ⧸ H.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hP : IsPGroup p (G ⧸ H.normalCore) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have ho : orderOf (g : G ⧸ H.normalCore) ≠ 0 := (orderOf_pos _).ne'
    obtain ⟨s, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p hp.ne_one
    refine ⟨s, ?_⟩
    have h1 : (g ^ p ^ s) ^ m ∈ H.normalCore := by
      rw [← QuotientGroup.eq_one_iff, ← pow_mul, QuotientGroup.mk_pow, ← he]
      exact pow_orderOf_eq_one _
    have h2 := hN _ m ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm h1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have h3 : H.index ∣ p ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le H)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h3
  exact ⟨j, hj⟩

end Group

section Poly

open Polynomial

theorem exists_one_add_X_pow (m : ℕ) : ∃ w : ℤ[X], (1 + X) ^ m - 1 = X * ((m : ℤ[X]) + X * w) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(m : ℤ[X]) + w + X * w, ?_⟩
    have : (1 + X : ℤ[X]) ^ (m + 1) - 1 = (1 + X) * ((1 + X) ^ m - 1) + X := by ring
    rw [this, hw]
    push_cast
    ring

theorem exists_pow_expansion (m k : ℕ) :
    ∃ v : ℤ[X], ((1 + X : ℤ[X]) ^ m - 1) ^ k = (m : ℤ[X]) ^ k * X ^ k + X ^ (k + 1) * v := by
  obtain ⟨w, hw⟩ := exists_one_add_X_pow m
  obtain ⟨z, hz⟩ := sub_dvd_pow_sub_pow ((m : ℤ[X]) + X * w) (m : ℤ[X]) k
  refine ⟨w * z, ?_⟩
  rw [hw, mul_pow]
  have : ((m : ℤ[X]) + X * w) ^ k = (m : ℤ[X]) ^ k + ((m : ℤ[X]) + X * w - (m : ℤ[X])) * z := by rw [← hz]; ring
  rw [this]
  ring

theorem smul_mem_of_pow {A V : Type*} [Ring A] [AddCommGroup V] [Module A V] (M : AddSubgroup V) (ν : A) {d : ℕ}
    (hν : ν ^ d = 0) (m : ℕ) (hdiv : ∀ x, m • x ∈ M → x ∈ M)
    (hu : ∀ x ∈ M, ((1 + ν) ^ m - 1) • x ∈ M) : ∀ x ∈ M, ν • x ∈ M := by
  have hdivk : ∀ (k : ℕ) x, (m ^ k) • x ∈ M → x ∈ M := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      refine hdiv x (ih _ ?_)
      rwa [smul_smul, ← pow_succ]
  have huk : ∀ (k : ℕ), ∀ x ∈ M, (((1 + ν) ^ m - 1) ^ k) • x ∈ M := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ, mul_smul]
      exact ih _ (hu x hx)
  have key : ∀ j k, d ≤ k + j → ∀ (f : ℤ[X]), ∀ x ∈ M, (aeval ν (X ^ k * f)) • x ∈ M := by
    intro j
    induction j with
    | zero =>
      intro k hk f x _
      have : ν ^ k = 0 := pow_eq_zero_of_le (by omega) hν
      simp [this]
    | succ j ih =>
      intro k hk f x hx
      have h1 : (aeval ν (X ^ k : ℤ[X])) • x ∈ M := by
        obtain ⟨v, hv⟩ := exists_pow_expansion m k
        refine hdivk k _ ?_
        have h2 : aeval ν (((1 + X : ℤ[X]) ^ m - 1) ^ k) = ((1 + ν) ^ m - 1) ^ k := by simp
        have h3 := huk k x hx
        rw [← h2, hv, map_add, add_smul] at h3
        have h4 := ih (k + 1) (by omega) v x hx
        have h5 := M.sub_mem h3 h4
        rw [add_sub_cancel_right] at h5
        convert h5 using 1
        rw [map_mul, mul_smul, map_pow, map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      have e : X ^ k * f = C (f.coeff 0) * X ^ k + X ^ (k + 1) * f.divX := by
        conv_lhs => rw [← divX_mul_X_add f]
        ring
      rw [e, map_add, add_smul]
      refine M.add_mem ?_ (ih (k + 1) (by omega) _ x hx)
      rw [map_mul, mul_smul, aeval_C]
      have : ∀ (a : ℤ) (y : V), y ∈ M → (algebraMap ℤ A a) • y ∈ M := by
        intro a y hy
        rw [eq_intCast, Int.cast_smul_eq_zsmul]
        exact M.zsmul_mem hy a
      exact this _ _ h1
  intro x hx
  simpa using key d 1 (by omega) 1 x hx

end Poly

section Unip

variable {k : Type} [CommRing k] {n c : ℕ}

abbrev T (V : Type) [AddCommGroup V] [Module k V] : (V ≃ₗ[k] V) →* Module.End k V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem nil_Ufl {g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hg : g ∈ Loc.N1 k n c) (i : ℕ) :
    ∀ v ∈ Loc.Ufl k n c i, ((T (k := k) _ g - 1) ^ (i + 1)) v = 0 := by
  have hR := hg.1.1
  have hX := hg.2
  induction i with
  | zero =>
    intro v hv
    have e : v = Loc.inX k n c fun l => v (Fin.castAdd c l) := by
      funext l
      by_cases h : l.1 < n
      · simp only [Loc.inX, LinearMap.pi_apply, dif_pos h]
        rfl
      · simp only [Loc.inX, LinearMap.pi_apply, dif_neg h]
        exact hv l (by simpa using h)
    have h1 : g v = v := by
      rw [e]
      exact hX _
    simp [h1]
  | succ i ih =>
    intro v hv
    have hmem : ((T (k := k) _ g - 1)) v ∈ Loc.Ufl k n c i := by
      set e := Loc.eN k (n + c) (n + i) with he
      set t := Loc.atN v (n + i) with ht
      have hv' : v - t • e ∈ Loc.Ufl k n c i := by
        intro l hl
        have hl' : n + i ≤ l.1 := by simpa using hl
        by_cases h : l.1 = n + i
        · have h1 : t = v l := by rw [ht, ← h]; simp [Loc.atN]
          have h2 : e l = 1 := by rw [he]; simp [Loc.eN, h]
          rw [Pi.sub_apply, Pi.smul_apply, h1, h2]
          simp
        · have : l.1 ∉ {l | l < n + (i + 1)} := by
            simp only [Set.mem_setOf_eq]
            omega
          simp [he, Loc.eN, h, hv l this]
      have e1 : ((T (k := k) _ g - 1)) v =
          (g (v - t • e) - (v - t • e)) + t • (g e - e) := by
        simp only [map_sub, map_smul]
        show g v - v = _
        module
      rw [e1]
      exact add_mem (sub_mem (hR.1 i _ hv') hv') (Submodule.smul_mem _ _ (hR.2.2 i))
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ hmem

theorem unipotent_level_nilpotent {g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hg : g ∈ Loc.N1 k n c) :
    (T (k := k) _ g - 1) ^ (c + 1) = 0 := by
  exact LinearMap.ext fun v => nil_Ufl hg c v fun l hl => absurd l.2 hl

end Unip

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem stab_fwd {n c : ℕ} {Λ : Submodule (𝓞 E) (Sp E (n + c))} {m : ℕ}
    (hdiv : ∀ x, m • x ∈ Λ → x ∈ Λ) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ Loc.N1 E n c) (hm : g ^ m ∈ stabL E _ Λ) : ∀ x ∈ Λ, g x ∈ Λ := by
  intro x hx
  have h1 := smul_mem_of_pow (A := Module.End E (Sp E (n + c))) Λ.toAddSubgroup (T (k := E) _ g - 1) (unipotent_level_nilpotent hg) m hdiv
    (fun y hy => ?_) x hx
  · have h2 : (T (k := E) _ g - 1) x ∈ Λ := h1
    have h3 := Λ.add_mem h2 hx
    simpa using h3
  · have h2 : (g ^ m) y ∈ Λ := (hm y).2 hy
    have h3 : (1 + (T (k := E) _ g - 1)) ^ m = T (k := E) _ (g ^ m) := by
      rw [add_sub_cancel, map_pow]
    show ((1 + (T (k := E) _ g - 1)) ^ m - 1) y ∈ Λ
    rw [h3]
    exact Λ.sub_mem h2 hy

theorem stab_root {n c : ℕ} {Λ : Submodule (𝓞 E) (Sp E (n + c))} {m : ℕ}
    (hdiv : ∀ x, m • x ∈ Λ → x ∈ Λ) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ Loc.N1 E n c) (hm : g ^ m ∈ stabL E _ Λ) : g ∈ stabL E _ Λ := by
  intro x
  refine ⟨fun h => ?_, stab_fwd hdiv hg hm x⟩
  have h1 := stab_fwd hdiv (inv_mem hg) (by rw [inv_pow]; exact inv_mem hm) _ h
  have h2 : g⁻¹ (g x) = x := g.symm_apply_apply x
  rwa [h2] at h1

theorem relIndex_prime_pow {n c : ℕ} {Λ : Submodule (𝓞 E) (Sp E (n + c))} {p : ℕ} (hp : p.Prime)
    (hdiv : ∀ m : ℕ, m.Coprime p → ∀ x, m • x ∈ Λ → x ∈ Λ) {C : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c))}
    (hC : C ≤ Loc.N1 E n c) (h0 : (Loc.N1 E n c ⊓ stabL E _ Λ).relIndex C ≠ 0) :
    ∃ k, (Loc.N1 E n c ⊓ stabL E _ Λ).relIndex C = p ^ k := by
  haveI : ((Loc.N1 E n c ⊓ stabL E _ Λ).subgroupOf C).FiniteIndex := ⟨h0⟩
  refine index_eq_prime_pow _ hp fun g m hm hg => ?_
  rw [Subgroup.mem_subgroupOf] at hg ⊢
  refine ⟨hC g.2, stab_root (hdiv m hm) (hC g.2) ?_⟩
  simpa using hg.2

theorem div_sclLat (P : HeightOneSpectrum (𝓞 E)) (q N : ℕ) (e : ℕ → ℤ) {m : ℕ} (hm : (m : 𝓞 E) ∉ P.asIdeal) (x : Sp E N)
    (h : m • x ∈ LocE.sclLat P q N e) : x ∈ LocE.sclLat P q N e := by
  unfold LocE.sclLat stdAt at h ⊢
  rw [Submodule.mem_comap, mem_localization_standardLattice] at h ⊢
  intro l
  obtain ⟨r, s, hs, hr⟩ := h l
  refine ⟨r, s * m, fun h' => (P.isPrime.mem_or_mem h').elim hs hm, ?_⟩
  rw [← hr]
  simp
  ring

theorem natCast_notMem {P : HeightOneSpectrum (𝓞 E)} {p m : ℕ} (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hm : m.Coprime p) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro h
  have h1 : (((m.gcd p : ℕ) : ℤ) : 𝓞 E) ∈ P.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ h) (Ideal.mul_mem_right _ _ hpP)
  rw [hm.gcd_eq_one] at h1
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h1))

theorem intOff_volN_inv {K : Type} [Field K] (σ : K →+* ℂ) {S : Finset ℕ} {P : HeightOneSpectrum (𝓞 E)} (hq : SNum S (qOf P))
    {n c : ℕ} (e : ℕ → ℤ) (q : ℕ) (C : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c))) :
    IntOff S (σ (Loc.volN K C (Loc.N1 E n c ⊓ stabL E _ (LocE.sclLat P q (n + c) e)))⁻¹) := by
  have hq1 : qOf P ≠ 1 := by
    intro h
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hp : (qOf P).minFac.Prime := Nat.minFac_prime hq1
  have hdvd := Nat.minFac_dvd (qOf P)
  have hpP := GlobalTheory.KerTie.natCast_mem_of_prime_dvd_absNorm P hp hdvd
  unfold Loc.volN
  by_cases h0 : (Loc.N1 E n c ⊓ stabL E _ (LocE.sclLat P q (n + c) e)).relIndex (C ⊓ Loc.N1 E n c) = 0
  · rw [h0]
    simpa using IntOff.zero
  obtain ⟨k, hk⟩ := relIndex_prime_pow hp (fun m hm x hx => div_sclLat P q _ e (natCast_notMem hpP hm) x hx)
    (inf_le_right : C ⊓ Loc.N1 E n c ≤ _) h0
  rw [hk, inv_div, map_div₀, map_natCast, map_natCast, div_eq_mul_inv]
  refine IntOff.mul (Formalism.L2.KerInert.RepRec.intOff_natCast S _) (IntOff.inv_nat ⟨pow_pos hp.pos _, fun r hr hd => ?_⟩)
  rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hd)]
  exact hq.2 _ hp hdvd

end Stab

theorem intOff_volN_Cbe : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (i : ℕ) (P : rowSG t.Pr t.sel (t.tup μ)) (h : AutY t.X D.R (i + 1)), IntOff (t.O u μ).S (t.seam.σ₀ (Loc.volN t.X.K (Loc.Cbe (Jat (Pr := t.Pr) (t.cst μ).sharp (i + 1) P.1) h) (Loc.N1 t.X.E (D.R.N (i + 1)) (cOf D.R (i + 1)) ⊓ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1)))⁻¹) := by
  intro D L hT Gi Gl K Y cX ex t u μ i P h
  exact intOff_volN_inv _ (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _ _ _

end GlobalTheory.UnipVol
