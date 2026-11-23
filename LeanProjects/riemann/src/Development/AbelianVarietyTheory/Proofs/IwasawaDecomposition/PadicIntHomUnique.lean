import Mathlib
import ReciprocityTheory.DualLattices.AinfFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem theta_ker_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θ l) ∧ IsDomain (Per.Ainf l) ∧ ((l : ℕ) : Per.Ainf l) ≠ 0 ∧ ∀ e : Per.Fl l, IsEps e → RingHom.ker (Per.θ l) = Ideal.span {xi e} ∧ xi e ≠ 0 := by
  intro l _
  have hv := PadicComplexInt.integers l
  haveI : IsDomain (Per.Fl l) := PreTilt.isDomain _ _ _ hv l
  have hl : ((l : ℕ) : Per.Ainf l) ≠ 0 := fun h => by
    have h1 := congrArg (Per.θ l) h
    rw [map_natCast, map_zero] at h1
    exact GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h1)
  refine ⟨ReciprocityTheory.PGsh.Ainf.theta_surj l _ hv, inferInstance, hl, fun e he => ?_⟩
  have hε : IsPrimitiveRoot (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) l := by
    have h1 : (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) ^ l = 1 := by
      rw [← map_pow, frobeniusEquiv_symm_pow_p]; exact he.1
    have h2 := he.2
    generalize ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = y at h1 h2 ⊢
    have h3 := IsPrimitiveRoot.orderOf y
    rwa [orderOf_eq_prime h1 h2] at h3
  refine ⟨ReciprocityTheory.PGsh.Ainf.ker_theta l _ hv e hε, fun h => ?_⟩
  exact one_ne_zero (ReciprocityTheory.PGsh.Ainf.xi_nzd l _ hv e hε 1 (by rw [one_mul]; exact h))

theorem tilt_facts : ∀ (l : ℕ) [Fact l.Prime], (∀ x : ℕ → Per.OC l, (∀ n, x (n + 1) ^ l = x n) → ∃ e : Per.Fl l, ∀ n, rootT e n = x n) ∧ (∀ e : Per.Fl l, (∀ n, rootT e n = 1) → e = 1) ∧ (∀ (e : Per.Fl l) (m n : ℕ), rootT (e ^ m) n = rootT e n ^ m) := by
  intro l _
  have key : ∀ (e : Per.Fl l) (n : ℕ), Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) =
      PreTilt.coeff n e := by
    intro e n
    rw [rootT, PreTilt.mk_untilt_eq_coeff_zero]
    exact PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e |>.trans (by rw [zero_add])
  refine ⟨fun x hx => ?_, fun e he => ?_, fun e m n => ?_⟩
  · let e : Perfection (ModP (Per.OC l) l) l :=
      ⟨fun n => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (x n), fun n => by
        rw [← map_pow, hx]⟩
    have hp : ∀ n k, x (n + k) ^ l ^ k = x n := by
      intro n k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, hx, ih]
    refine ⟨e, fun n => ?_⟩
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun k => ⟨x (n + k), ?_, ?_⟩
    · refine Eq.trans ?_ (PreTilt.coeff_iterate_frobeniusEquiv_symm (O := Per.OC l) k n e).symm
      rw [add_comm]; rfl
    · rw [hp]
  · refine Perfection.ext fun n => ?_
    have := key e n
    rw [he, map_one] at this
    exact this.symm.trans (map_one (PreTilt.coeff n)).symm
  · rw [rootT, rootT, ← map_pow]
    congr 1
    exact iterate_map_pow (frobeniusEquiv (Per.Fl l) l).symm.toRingHom n e m

theorem thetaP_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θP l) ∧ RingHom.ker (Per.θP l) = Per.kerP l ∧ (∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l])) ∧ (∀ a : Per.AinfP l, Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) ∧ ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  intro l _
  obtain ⟨hs, hdom, hl, hk⟩ := theta_ker_facts l
  have hle : Submonoid.powers ((l : ℕ) : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl
  have hA : ∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l]) :=
    fun a => GlobalTheory.RingIface.fontaineTheta_algebraMap l a
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hsurj : ∀ y : Per.AinfP l, ∃ (n : ℕ) (a : Per.Ainf l),
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y => by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    exact ⟨n, a, by rwa [map_natCast] at h⟩
  have hz : ∀ y : Per.AinfP l, Per.θP l y = 0 → ∃ (n : ℕ) (a : Per.Ainf l), Per.θ l a = 0 ∧
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y hy => by
    obtain ⟨n, a, h⟩ := hsurj y
    refine ⟨n, a, Subtype.ext ?_, h⟩
    rw [← hA, ← h, map_mul, hy, zero_mul]
    rfl
  have hker : RingHom.ker (Per.θP l) = Per.kerP l := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one]))
    obtain ⟨n, a, ha, h⟩ := hz y hy
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
    exact GlobalTheory.RingIface.alg_mem_kerP l ha
  refine ⟨fun x => ?_, hker, hA, fun a => ?_, IsLocalization.isDomain_of_le_nonZeroDivisors _ hle,
    IsLocalization.injective _ hle, fun e he => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖x * ((l : ℕ) : ℂ_[l]) ^ n‖ ≤ 1 := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (GlobalTheory.RingBasics.norm_p_lt (p := l))).const_mul ‖x‖
      rw [mul_zero] at h1
      obtain ⟨n, hn⟩ := (h1.eventually (eventually_le_nhds one_pos)).exists
      exact ⟨n, by rwa [norm_mul, norm_pow]⟩
    obtain ⟨a, ha⟩ := hs ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
    obtain ⟨d, hd⟩ := (hu.pow n).exists_right_inv
    refine ⟨algebraMap _ _ a * d, ?_⟩
    have h2 := congrArg (Per.θP l) hd
    rw [map_mul, map_pow, map_natCast, map_one] at h2
    rw [map_mul, hA, ha, mul_assoc, h2, mul_one]
  · exact GlobalTheory.RingIface.thetaD_alg l a
  · obtain ⟨h1, -⟩ := hk e he
    refine le_antisymm (fun y hy => ?_) ?_
    · rw [← hker] at hy
      obtain ⟨n, a, ha, h⟩ := hz y hy
      rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
      have h2 : a ∈ Ideal.span {xi e} := h1 ▸ ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h2
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, ← hker, RingHom.mem_ker, hA, Model.theta_xi he]
      rfl

end GlobalTheory.MemLoc
