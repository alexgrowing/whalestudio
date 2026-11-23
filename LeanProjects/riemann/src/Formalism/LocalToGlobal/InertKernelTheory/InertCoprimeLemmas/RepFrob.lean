import Formalism.LocalToGlobal.InertKernelTheory.FrameInt
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.FrobeniusSqIterateTeichmuller

noncomputable section

namespace Formalism.L2.KerInert.RepFrob

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

variable {p : ℕ} [hp : Fact p.Prime]

theorem nK (x : MaximalUnramifiedExtension p) : ‖x‖ = ‖(x : ℂ_[p])‖ := rfl

theorem nadd1 {a b : ℂ_[p]} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem nsub1 {a b : ℂ_[p]} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact nadd1 ha (by rwa [norm_neg])

theorem pinv_le_one : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)

theorem unr_norm_le {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) {a : MaximalUnramifiedExtension p} (ha : ‖a‖ ≤ 1) :
    ‖σ a‖ ≤ 1 := by
  obtain ⟨-, -, -, -, h⟩ := hσ
  have h1 : ‖((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) - ((a : MaximalUnramifiedExtension p) : ℂ_[p]) ^ p‖ ≤ 1 := by
    have h0 := h a ha
    rw [nK] at h0
    push_cast at h0
    exact h0.trans pinv_le_one
  have h2 : ‖((a : MaximalUnramifiedExtension p) : ℂ_[p]) ^ p‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (by rwa [nK] at ha)
  rw [nK]
  have h3 := nadd1 h1 h2
  rwa [sub_add_cancel] at h3

theorem norm_nat_coprime {N : ℕ} (hc : Nat.Coprime N p) : ‖(N : ℂ_[p])‖ = 1 := by
  have h : (N : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) (N : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    simp
  rw [h, PadicComplex.norm_extends']
  exact Padic.norm_natCast_eq_one_iff.2 hc.symm

theorem eq_one_of_root {u : ℂ_[p]} {N : ℕ} (hc : Nat.Coprime N p) (hu : u ^ N = 1) (h1 : ‖u - 1‖ < 1) :
    u = 1 := by
  by_contra hne
  have hu1 : ‖u‖ ≤ 1 := by
    have h3 := nadd1 (a := u - 1) (b := 1) (c := 1) h1.le (by rw [norm_one])
    rwa [sub_add_cancel] at h3
  have hg : ∀ i : ℕ, ‖∑ j ∈ Finset.range i, u ^ j‖ ≤ 1 := fun i =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hu1
  have hi : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := fun i => by
    rw [← geom_sum_mul, norm_mul]
    calc ‖∑ j ∈ Finset.range i, u ^ j‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ := by
          gcongr
          exact hg i
      _ = ‖u - 1‖ := one_mul _
  have hS : ‖∑ i ∈ Finset.range N, (u ^ i - 1)‖ ≤ ‖u - 1‖ :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => hi i
  have hsum : ∑ i ∈ Finset.range N, u ^ i = (N : ℂ_[p]) + ∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hz : ∑ i ∈ Finset.range N, u ^ i = 0 := by
    have h2 : (∑ i ∈ Finset.range N, u ^ i) * (u - 1) = 0 := by
      rw [geom_sum_mul, hu, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  have hNn := norm_nat_coprime (p := p) hc
  have h4 : ‖(N : ℂ_[p]) + ∑ i ∈ Finset.range N, (u ^ i - 1)‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hNn]; exact (hS.trans_lt h1).ne'), hNn]
    exact max_eq_left (hS.trans h1.le)
  rw [← hsum, hz, norm_zero] at h4
  exact zero_ne_one h4

theorem wToC_mem_kur (x : WW p) : Formalism.L2.G.Pend.wToC p x ∈ MaximalUnramifiedExtension p := by
  have hx := Formalism.L2.G.Pend.wToC_mem_Wp p x
  have hpp : p.Prime := Fact.out
  have hle : Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1}).toSubring := by
    rw [Subring.closure_le]
    rintro ζ ⟨n, hn, hc, hz⟩
    exact Subfield.subset_closure ⟨n, hn, (Nat.Prime.coprime_iff_not_dvd hpp).1 hc.symm, hz⟩
  have hsub : ((Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} : Subring ℂ_[p]) :
      Set ℂ_[p]) ⊆ ((Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1} : Subfield ℂ_[p]) :
      Set ℂ_[p]) := fun y hy => hle hy
  exact closure_mono hsub hx

variable (p) in

def wK : WW p →+* MaximalUnramifiedExtension p := (Formalism.L2.G.Pend.wToC p).codRestrict (MaximalUnramifiedExtension p) wToC_mem_kur

theorem wK_coe (x : WW p) : ((wK p x : MaximalUnramifiedExtension p) : ℂ_[p]) = Formalism.L2.G.Pend.wToC p x := rfl

theorem norm_wK_le (x : WW p) : ‖wK p x‖ ≤ 1 := Formalism.L2.G.Pend.norm_wToC_le p x

theorem frob_teich {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) (y : Formalism.MainNotions.FormalGroupSystem.kb p) :
    σ (wK p (WittVector.teichmuller p y)) = wK p (WittVector.teichmuller p y) ^ p := by
  by_cases hy : y = 0
  · rw [hy, WittVector.teichmuller_zero, map_zero, map_zero, zero_pow hp.out.ne_zero]
  obtain ⟨m, hm, hc, h1⟩ := Formalism.L2.G.Pend.exists_coprime_pow_eq_one p hy
  set a : MaximalUnramifiedExtension p := wK p (WittVector.teichmuller p y) with ha
  have ham : a ^ m = 1 := by rw [ha, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσm : (σ a) ^ m = 1 := by rw [← map_pow, ham, map_one]
  have hz : (a : ℂ_[p]) ^ m = 1 := by
    have := congrArg (fun z : MaximalUnramifiedExtension p => (z : ℂ_[p])) ham
    push_cast at this; exact this
  have hcz : ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) ^ m = 1 := by
    have := congrArg (fun z : MaximalUnramifiedExtension p => (z : ℂ_[p])) hσm
    push_cast at this; exact this
  have hnz : ‖(a : ℂ_[p])‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  have ha0 : (a : ℂ_[p]) ≠ 0 := by intro h0; rw [h0, norm_zero] at hnz; exact zero_ne_one hnz
  have hb : ‖((σ a - a ^ p : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ := hσ.2.2.2.2 a (by rw [nK, hnz])
  set u : ℂ_[p] := ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) * ((a : ℂ_[p]) ^ p)⁻¹ with hu
  have hap0 : (a : ℂ_[p]) ^ p ≠ 0 := pow_ne_zero _ ha0
  have hum : u ^ m = 1 := by
    rw [hu, mul_pow, hcz, inv_pow, ← pow_mul, mul_comm p m, pow_mul, hz, one_pow, inv_one, mul_one]
  have hu1 : ‖u - 1‖ < 1 := by
    have e : u - 1 = ((σ a - a ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) * ((a : ℂ_[p]) ^ p)⁻¹ := by
      rw [hu]; push_cast; field_simp
    rw [e, norm_mul, norm_inv, norm_pow, hnz, one_pow, inv_one, mul_one]
    exact lt_of_le_of_lt hb (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hu' := eq_one_of_root hc hum hu1
  apply Subtype.ext
  have e2 : ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = u * (a : ℂ_[p]) ^ p := by rw [hu]; field_simp
  rw [e2, hu', one_mul]
  push_cast
  rfl

theorem frob_wK {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) (x : WW p) :
    σ (wK p x) = wK p (sigW p x) := by
  set f : WW p →+* MaximalUnramifiedExtension p := σ.comp (wK p) with hf
  set g : WW p →+* MaximalUnramifiedExtension p := (wK p).comp (sigW p) with hg
  have ht : ∀ y, f (WittVector.teichmuller p y) = g (WittVector.teichmuller p y) := by
    intro y
    rw [hf, hg, RingHom.comp_apply, RingHom.comp_apply, frob_teich hσ y, Formalism.L2.G.Pend.sigW_teich, map_pow,
      map_pow]
  have hfl : ∀ c, ‖f c‖ ≤ 1 := fun c => unr_norm_le hσ (norm_wK_le c)
  have hgl : ∀ c, ‖g c‖ ≤ 1 := fun c => norm_wK_le _
  show f x = g x
  apply Subtype.ext
  apply Formalism.L2.G.Pend.eq_of_close p
  intro N
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  set S := ∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (Formalism.MainNotions.FormalGroupSystem.kb p) p).symm ^ i) (x.coeff i)) * (p : WW p) ^ i) with hS
  have hfS : f S = g S := by
    rw [hS, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ht, map_pow, map_pow, map_natCast, map_natCast]
  have hx : x = S + (p : WW p) ^ (N + 1) * c := by rw [← hc]; ring
  have e : ((f x : MaximalUnramifiedExtension p) : ℂ_[p]) - ((g x : MaximalUnramifiedExtension p) : ℂ_[p]) =
      (p : ℂ_[p]) ^ (N + 1) * (((f c : MaximalUnramifiedExtension p) : ℂ_[p]) - ((g c : MaximalUnramifiedExtension p) : ℂ_[p])) := by
    rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hfS]
    push_cast; ring
  rw [e, norm_mul, norm_pow, Formalism.L2.G.Pend.norm_p_C]
  have h1 : ‖((f c : MaximalUnramifiedExtension p) : ℂ_[p]) - ((g c : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1 := nsub1 (hfl c) (hgl c)
  calc ((p : ℝ)⁻¹) ^ (N + 1) * ‖((f c : MaximalUnramifiedExtension p) : ℂ_[p]) - ((g c : MaximalUnramifiedExtension p) : ℂ_[p])‖
      ≤ ((p : ℝ)⁻¹) ^ (N + 1) * 1 := by gcongr
    _ ≤ ((p : ℝ)⁻¹) ^ N := by
      rw [mul_one]
      exact pow_le_pow_of_le_one (by positivity) pinv_le_one (Nat.le_succ N)

theorem finRotate_val : ∀ {n : ℕ} (s : Fin n), ((finRotate n s : Fin n) : ℕ) = (s.val + 1) % n
  | 0, s => s.elim0
  | n + 1, s => by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

section Tw

variable (X : Sys p) (E : Formalism.L2.G.Pend.CEmbC X.G)

def twT (v : X.Pl) (t : ℕ) : X.G.P.Qq v →+* ℂ_[p] :=
  E.iK.comp ((X.G.P.ι v).comp (X.G.P.σ v ^ t : X.G.P.Qq v ≃+* X.G.P.Qq v).toRingHom)

theorem twE_eq (v : X.Pl) (s : Fin (X.G.P.n' v)) : twE X E v s = twT X E v s.val := rfl

theorem twT_alg (v : X.Pl) (t : ℕ) (x : X.G.P.W v) :
    twT X E v t (algebraMap (X.G.P.W v) (X.G.P.Qq v) x) = Formalism.L2.G.Pend.wToC p ((sigW p)^[t] (E.rd v x)) := by
  rw [← Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap p]
  exact E.compat v t x

theorem twT_mem (v : X.Pl) (t : ℕ) (x : X.G.P.Qq v) : twT X E v t x ∈ MaximalUnramifiedExtension p := by
  have := (X.G.P.setting v).frac_alt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.G.P.W v) x
  rw [map_div₀, twT_alg, twT_alg]
  exact div_mem (wToC_mem_kur _) (wToC_mem_kur _)

def twTK (v : X.Pl) (t : ℕ) : X.G.P.Qq v →+* MaximalUnramifiedExtension p := (twT X E v t).codRestrict (MaximalUnramifiedExtension p) (twT_mem X E v t)

theorem twTK_alg (v : X.Pl) (t : ℕ) (x : X.G.P.W v) :
    twTK X E v t (algebraMap (X.G.P.W v) (X.G.P.Qq v) x) = wK p ((sigW p)^[t] (E.rd v x)) := Subtype.ext ((twT_alg X E v t x).trans (wK_coe _).symm)

theorem frob_twTK {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) (v : X.Pl) (t : ℕ)
    (x : X.G.P.Qq v) : σ (twTK X E v t x) = twTK X E v (t + 1) x := by
  have := (X.G.P.setting v).frac_alt
  have h : σ.comp (twTK X E v t) = twTK X E v (t + 1) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (X.G.P.W v))
    ext y
    simp only [RingHom.comp_apply]
    rw [twTK_alg, twTK_alg, frob_wK hσ, Function.iterate_succ_apply']
  exact RingHom.congr_fun h x

theorem twT_mod (v : X.Pl) (t : ℕ) : twT X E v t = twT X E v (t % X.G.P.n' v) := by
  have hs : (X.G.P.σ v ^ t : X.G.P.Qq v ≃+* X.G.P.Qq v) = X.G.P.σ v ^ (t % X.G.P.n' v) := by
    conv_lhs => rw [← Nat.div_add_mod t (X.G.P.n' v)]
    rw [pow_add, pow_mul, (X.G.P.setting v).period, one_pow, one_mul]
  unfold twT
  rw [hs]

theorem frobTw_of (h5 : 5 ≤ p) : FrobTw X E := by
  obtain ⟨σ, hσ⟩ := Formalism.L2.Th1.Top.frobExistsH p h5
  have hσ' : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ := hσ
  refine ⟨σ, fun v s => twTK X E v s.val, wK p, hσ', fun v s x => rfl, fun v s x => ?_, fun w => ?_,
    fun w => frob_wK hσ' w, fun w => norm_wK_le w⟩
  · rw [frob_twTK X E hσ']
    apply Subtype.ext
    show twT X E v (s.val + 1) x = twT X E v (finRotate _ s).val x
    rw [twT_mod X E v (s.val + 1), finRotate_val]
  · show Formalism.L2.G.Pend.wToC p w = Formalism.L2.G.Pend.k0ToC p (algebraMap _ _ w)
    exact (Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap p w).symm

end Tw

section abelian₂

variable (X : Sys p) (E : Formalism.L2.G.Pend.CEmbC X.G) (D : Formalism.BasicNotions.D7)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

end abelian₂

end Formalism.L2.KerInert.RepFrob

section
set_option pp.fullNames true
end
