import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanKill

theorem exists_mem_pow_forall_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] (β : R →+* k), ∃ c ∈ w0 ^ r, ∀ i, β (b.t i c) ≠ 0 := by
  intro p _ D R _ b w0 r hw k _ β
  classical
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos D.a with ha | ha
  · obtain ⟨i, -⟩ := hcon 0 (zero_mem _)
    exact (Fin.elim0 (ha ▸ i))
  let i0 : Fin D.a := ⟨0, ha⟩
  have hsub : ((w0 ^ r : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) ⊆
      ⋃ i ∈ ((Finset.univ : Finset (Fin D.a)) : Set (Fin D.a)), (RingHom.ker (β.comp (b.t i)) : Set (𝓞 D.F)) := by
    intro c hc
    obtain ⟨i, hi⟩ := hcon c hc
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) (RingHom.mem_ker.mpr hi)
  obtain ⟨i, -, hi⟩ := (Ideal.subset_union_prime i0 i0 (fun i _ _ _ => RingHom.ker_isPrime _)).mp hsub
  have hi' : w0 ≤ RingHom.ker (β.comp (b.t i)) := (RingHom.ker_isPrime _).le_of_pow_le hi
  have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp (hi' hy))
  rw [hw.2.2.1 i, top_le_iff] at hle
  exact RingHom.ker_ne_top β hle

theorem exists_mem_pow_add_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (β : R →+* k) (r2 : ℤ), (r2 : k) = (D.tr : k) - β b.ρ → ∃ c ∈ w0 ^ r, ∃ e f : 𝓞 D.F, c + e * (D.ω - (r2 : 𝓞 D.F)) + f * (p : 𝓞 D.F) = 1 := by
  intro p _ D R _ b w0 r hw k _ _ _ β r2 hr2
  haveI : w0.IsMaximal := hw.1
  letI : Field (𝓞 D.F ⧸ w0) := Ideal.Quotient.field w0

  have hpQ : ((p : 𝓞 D.F ⧸ w0)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w0), Ideal.Quotient.eq_zero_iff_mem]; exact hw.2.1
  haveI : CharP (𝓞 D.F ⧸ w0) p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hpQ
  have hne : w0 ≠ ⊥ := by
    intro h
    have h1 := hw.2.1
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1
  haveI : Finite (𝓞 D.F ⧸ w0) := Ideal.finiteQuotientOfFreeOfNeBot w0 hne
  letI : Algebra (ZMod p) (𝓞 D.F ⧸ w0) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 D.F ⧸ w0) := inferInstance
  let φ0 := IsAlgClosed.lift (M := k) (R := ZMod p) (S := 𝓞 D.F ⧸ w0)
  let φ : 𝓞 D.F →+* k := φ0.toRingHom.comp (Ideal.Quotient.mk w0)
  have hker : RingHom.ker φ = w0 := by
    ext y
    rw [RingHom.mem_ker]
    change φ0 (Ideal.Quotient.mk w0 y) = 0 ↔ y ∈ w0
    rw [map_eq_zero_iff φ0 φ0.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hφ := hw.2.2.2 k β φ hker

  let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), (p : 𝓞 D.F)}
  have hJ : w0 ⊔ J = ⊤ := by
    by_contra hsup
    have hle : J ≤ w0 := by
      have := hw.1.eq_of_le hsup le_sup_left
      exact this ▸ le_sup_right
    have hmem : D.ω - (r2 : 𝓞 D.F) ∈ w0 := hle (Ideal.subset_span (Set.mem_insert _ _))
    rw [← hker, RingHom.mem_ker, map_sub, map_intCast, hφ, hr2] at hmem
    have hρ : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
      have h := congrArg β b.ρ_root
      simpa using h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-((D.tr : k) - 2 * β b.ρ)) * hmem - 4 * hρ
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hJr : w0 ^ r ⊔ J = ⊤ := by
    have h := Ideal.isCoprime_iff_sup_eq.mpr hJ
    exact Ideal.isCoprime_iff_sup_eq.mp h.pow_left
  obtain ⟨c, hc, j, hj, hcj⟩ := Submodule.mem_sup.mp (hJr ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ w0 ^ r ⊔ J)
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
  exact ⟨c, hc, e, f, by rw [add_assoc, hef, hcj]⟩

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem sum_eq_zero_of_eigen (T : Module.End k V) {I : Type} [DecidableEq I] (s : Finset I) :
    ∀ (w : I → V) (l : I → k), (∀ i ∈ s, T (w i) = l i • w i) → (∀ i ∈ s, l i ≠ 0) →
      T (∑ i ∈ s, w i) = 0 → ∑ i ∈ s, w i = 0 := by
  induction s using Finset.induction_on with
  | empty => intros; simp
  | insert j s hj ih =>
    intro w l hw hl hT
    rw [Finset.sum_insert hj] at hT ⊢
    have e : ∑ i ∈ s, (l i - l j) • w i = T (w j + ∑ i ∈ s, w i) - l j • (w j + ∑ i ∈ s, w i) := by
      rw [map_add, map_sum, hw j (Finset.mem_insert_self j s), smul_add, Finset.smul_sum,
        Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_insert_of_mem hi))]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have key := ih (fun i => (l i - l j) • w i) l
      (fun i hi => by rw [map_smul, hw i (Finset.mem_insert_of_mem hi), smul_comm])
      (fun i hi => hl i (Finset.mem_insert_of_mem hi))
      (by rw [e, map_sub, map_smul, hT, map_zero, smul_zero, sub_zero])
    rw [key, hT, zero_sub, eq_comm, neg_eq_zero] at e
    exact (smul_eq_zero.mp e).resolve_left (hl j (Finset.mem_insert_self j s))

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

lemma L_int {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℤ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

lemma L_nat {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℕ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_natCast, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

theorem core {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (v : V) (hv : ∀ c ∈ w0 ^ r, L c v = 0) : v = 0 := by
  by_cases hp : (p : k) = 0
  swap
  · have h := hv _ (Ideal.pow_mem_pow hw.2.1 r)
    rw [← Nat.cast_pow, L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left (by rw [Nat.cast_pow]; exact pow_ne_zero _ hp)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hp
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
  have k1 : ∀ c ∈ w0 ^ r, L c v1 = 0 := by
    intro c hc
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : ∀ c ∈ w0 ^ r, L c v2 = 0 := by
    intro c hc
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have z1 : v1 = 0 := by
    obtain ⟨c, hc, hne⟩ := exists_mem_pow_forall_ne_zero p D R b w0 r hw k β
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1 c hc
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
    obtain ⟨c, hc, e, f, hcef⟩ := exists_mem_pow_add_eq_one p D R b w0 r hw k β r2 (by rw [hr2, hρ2, hρ1])
    have h := congrArg (fun g => g v2) (congrArg L hcef)
    simp only [map_add, map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2 c hc] at h
    simp only [zero_add, add_zero] at h
    rw [← hTω, e2, hr2, map_smul, sub_self, hp, zero_smul, map_zero, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_etPlace : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  intro p _ D R _ b N w0 r hw S s o k _ _ x v hv0 hv
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
  have := core D b w0 r hw β L hlie (Tan.mk v hmv) (fun c hc => Tan.ext (by rw [hL]; exact hv c hc))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanKill
