import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanInj

open GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem core_inj {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F))
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (c : 𝓞 D.F) (hc0 : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w)
    (v : V) (hv : L c v = 0) : v = 0 := by
  have hpr : p.Prime := Fact.out
  by_cases hp : (p : k) = 0
  swap
  ·
    set N := Ideal.absNorm (Ideal.span {c}) with hNdef
    have hNmem : ((N : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hNmem
    have hN0 : N ≠ 0 := by
      rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc0
    obtain ⟨e, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hpr.one_lt.ne'
    have hN'u : IsUnit ((N' : ℕ) : R) := b.unit N' ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hN').symm
    have hN'k : ((N' : ℕ) : k) ≠ 0 := by
      have := hN'u.map β
      rw [map_natCast] at this
      exact this.ne_zero
    have hNk : ((N : ℕ) : k) ≠ 0 := by
      rw [hNe, Nat.cast_mul, Nat.cast_pow]
      exact mul_ne_zero (pow_ne_zero _ hp) hN'k
    have h : L ((N : ℕ) : 𝓞 D.F) v = 0 := by
      rw [← hd, map_mul, Module.End.mul_apply, hv, map_zero]
    rw [L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left hNk
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hpr).mpr hp
  set Tω := L D.ω with hTω
  set ρ1 := β b.ρ with hρ1
  set ρ2 := (D.tr : k) - ρ1 with hρ2
  have hquad : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    have hb : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
    have h := D.nm_eq
    rw [hb] at h
    linear_combination (-1 : 𝓞 D.F) * h
  have hq : ∀ u, Tω (Tω u) = (D.tr : k) • Tω u - (D.nm : k) • u := by
    intro u
    have h := congrArg (fun f => f u) (congrArg L hquad)
    simp only [map_add, map_sub, map_mul, map_zero, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, L_int] at h
    rw [← hTω] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hρ : ρ1 ^ 2 - (D.tr : k) * ρ1 + (D.nm : k) = 0 := by
    have h := congrArg β b.ρ_root
    simpa using h
  have hsum : ρ1 + ρ2 = D.tr := by rw [hρ2]; ring
  have hprod : ρ1 * ρ2 = D.nm := by rw [hρ2]; linear_combination (-1 : k) * hρ
  clear_value Tω ρ1 ρ2
  have hδ : ρ1 - ρ2 ≠ 0 := by
    intro h0
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      have : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = (ρ1 - ρ2) ^ 2 := by
        push_cast
        rw [← hsum, ← hprod]; ring
      rw [this, h0]; ring
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hcomm : ∀ c u, L c (Tω u) = Tω (L c u) := by
    intro c u
    rw [hTω, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  set v1 := (ρ1 - ρ2)⁻¹ • (Tω v - ρ2 • v) with hv1
  set v2 := (ρ1 - ρ2)⁻¹ • (ρ1 • v - Tω v) with hv2
  have hv12 : v = v1 + v2 := by
    rw [hv1, hv2, ← smul_add]
    have : Tω v - ρ2 • v + (ρ1 • v - Tω v) = (ρ1 - ρ2) • v := by rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have e1 : Tω v1 = ρ1 • v1 := by
    rw [hv1, map_smul, map_sub, map_smul, hq, smul_comm ρ1]
    congr 1
    rw [← hsum, ← hprod]
    module
  have e2 : Tω v2 = ρ2 • v2 := by
    rw [hv2, map_smul, map_sub, map_smul, hq, smul_comm ρ2]
    congr 1
    rw [← hsum, ← hprod]
    module
  have k1 : L c v1 = 0 := by
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : L c v2 = 0 := by
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv, map_zero, smul_zero, sub_zero, smul_zero]
  have hp0 : ((p : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have z1 : v1 = 0 := by
    have hne : ∀ i, β (b.t i c) ≠ 0 := by
      intro i h0
      have hprime : (RingHom.ker (β.comp (b.t i))).IsPrime := RingHom.ker_isPrime _
      have hpP : ((p : ℕ) : 𝓞 D.F) ∈ RingHom.ker (β.comp (b.t i)) := by
        rw [RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast, hp]
      have hbot : RingHom.ker (β.comp (b.t i)) ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hpP
        exact hp0 hpP
      have hmax : (RingHom.ker (β.comp (b.t i))).IsMaximal := hprime.isMaximal hbot
      have hnw : RingHom.ker (β.comp (b.t i)) ≠ w0 := by
        intro hP
        have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
          refine Ideal.span_le.mpr ?_
          rintro _ ⟨y, hy, rfl⟩
          have : y ∈ RingHom.ker (β.comp (b.t i)) := hP ▸ hy
          exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp this)
        rw [hw.2.2.1 i, top_le_iff] at hle
        exact RingHom.ker_ne_top β hle
      exact hcw _ hmax hpP hnw (RingHom.mem_ker.mpr h0)
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1
  have z2 : v2 = 0 := by
    obtain ⟨r0, hr0⟩ := D.split
    have hr0k : ((r0 : k) - ρ1) * ((r0 : k) - ρ2) = 0 := by
      have : ((r0 ^ 2 - D.tr * r0 + D.nm : ℤ) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).mpr hr0
      push_cast at this
      linear_combination this - (r0 : k) * hsum + hprod
    obtain ⟨r2, hr2⟩ : ∃ r2 : ℤ, (r2 : k) = ρ2 := by
      rcases mul_eq_zero.mp hr0k with h | h
      · exact ⟨D.tr - r0, by push_cast; rw [hρ2]; linear_combination -h⟩
      · exact ⟨r0, by linear_combination h⟩
    obtain ⟨c', hc', e', f', hcef'⟩ := exists_mem_pow_add_eq_one p D R b w0 1 hw k β r2 (by rw [hr2, hρ2, hρ1])
    rw [pow_one] at hc'
    let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), ((p : ℕ) : 𝓞 D.F)}
    have hJ : Ideal.span {c} ⊔ J = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      have hJm : J ≤ m := le_trans le_sup_right hle
      have hωm : D.ω - (r2 : 𝓞 D.F) ∈ m := hJm (Ideal.subset_span (Set.mem_insert _ _))
      have hpm : ((p : ℕ) : 𝓞 D.F) ∈ m := hJm (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      have hcm : c ∈ m := le_trans le_sup_left hle (Ideal.mem_span_singleton_self c)
      have hmw : m ≠ w0 := by
        intro hmw
        subst hmw
        have h1 : (1 : 𝓞 D.F) ∈ m := by
          rw [← hcef']
          exact m.add_mem (m.add_mem hc' (m.mul_mem_left _ hωm)) (m.mul_mem_left _ hpm)
        exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      exact hcw m hm hpm hmw hcm
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ Ideal.span {c} ⊔ J)
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
    have h := congrArg (fun g => g v2) (congrArg L haj)
    rw [← hef] at h
    simp only [map_add, map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2] at h
    rw [← hTω, e2, hr2, sub_self] at h
    simp only [hp, zero_smul, map_zero, zero_add, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanInj

namespace GlobalTheory.UPel.HT.EtLev.TanInj

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_notMem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F), c ≠ 0 → (∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) → ∀ v : epsPtR x ⟶ o.A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 → v = 1 := by
  intro p _ D R _ b N w0 hw S s o k _ _ x c hc0 hcw v hv0 hv
  set β : R →+* k := (Spec.preimage (x ≫ s)).hom with hβ
  have hx : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let L : 𝓞 D.F →+* Module.End k (Tan x o.A) := (actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  have hL : ∀ c (u : Tan x o.A), (L c u).hom = u.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := fun _ _ => rfl
  have hlie : ∀ u : Tan x o.A, L D.ω u = β b.ρ • u →
      ∃ w : Fin D.a → Tan x o.A, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ u = ∑ i, w i := by
    intro u hu
    obtain ⟨w, hw1, hw2⟩ := o.lie k β x hx u.hom
      ⟨(mem_tanSub_iff x o.A _).mp u.hom_mem, by
        have := congrArg (fun t : Tan x o.A => t.hom.left) hu
        simpa [hL, GrpTangentPt.epsScalePt_left] using this⟩
    have hmem : ∀ i, w i ∈ tanSub x o.A := fun i => (mem_tanSub_iff x o.A _).mpr (hw1 i 0).1
    refine ⟨fun i => Tan.mk (w i) (hmem i), fun i c => Tan.ext (Over.OverMorphism.ext ((hw1 i c).2)), ?_⟩
    refine Tan.ext ?_
    rw [Tan.hom_sum, hw2, List.prod_ofFn]
    rfl
  have hmv : v ∈ tanSub x o.A := (mem_tanSub_iff x o.A _).mpr hv0
  have := core_inj D b w0 hw β L hlie c hc0 hcw (Tan.mk v hmv) (Tan.ext (by rw [hL]; exact hv))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanInj
