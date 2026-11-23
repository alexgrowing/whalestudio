import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapEqZeroIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSubConjNotMem
import GroundTheory.GlobalFields.LocalAtPlace
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong

noncomputable section
namespace GlobalTheory.SUCong.RingUnr

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

local notation "A" => Fv F v ⊗[F] E
local notation "O" => v.adicCompletionIntegers F

theorem sig_tmul (a : Fv F v) (x : E) : sigR (Fv F v) σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl

theorem sig_sig (h : IsCMExt F E σ) (a : A) : sigR (Fv F v) σ (sigR (Fv F v) σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [sig_tmul, sig_tmul, GlobalTheory.SelfDualLatticeCompare.conj_conj h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iota_eq (c : Fv F v) : algebraMap (Fv F v) A c = c ⊗ₜ[F] (1 : E) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem sig_iota (c : Fv F v) : sigR (Fv F v) σ (algebraMap (Fv F v) A c) = algebraMap (Fv F v) A c := by
  rw [iota_eq, sig_tmul, map_one]

theorem tmul_algebraMap (a : Fv F v) (f : F) :
    a ⊗ₜ[F] algebraMap F E f = algebraMap (Fv F v) A (a * algebraMap F (Fv F v) f) := by
  rw [iota_eq, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, mul_comm,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem tmul_mem {a : Fv F v} (ha : a ∈ O) (x : 𝓞 E) : a ⊗ₜ[F] (x : E) ∈ intA (E := E) v :=
  Subring.subset_closure ⟨a, ha, x, rfl⟩

theorem iota_mem {c : Fv F v} (hc : c ∈ O) : algebraMap (Fv F v) A c ∈ intA (E := E) v := by
  rw [iota_eq]
  exact tmul_mem v hc 1

theorem coe_mem (f : 𝓞 F) : algebraMap F (Fv F v) (f : F) ∈ O := by
  have := (algebraMap (𝓞 F) O f).2
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply] at this
  exact this

theorem inv_mem {f : 𝓞 F} (hf : f ∉ v.asIdeal) : (algebraMap F (Fv F v) (f : F))⁻¹ ∈ O := by
  have hu : IsUnit (algebraMap (𝓞 F) O f) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact hf
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : algebraMap F (Fv F v) (f : F) * (u : Fv F v) = 1 := by
    have := congrArg Subtype.val hu
    rw [Subring.coe_mul, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply] at this
    exact this
  rw [inv_eq_of_mul_eq_one_right h1]
  exact u.2

theorem sig_mem (h : IsCMExt F E σ) {s : A} (hs : s ∈ intA (E := E) v) : sigR (Fv F v) σ s ∈ intA (E := E) v := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    rw [sig_tmul]
    have hy : IsIntegral ℤ (σ (y : E)) := y.2.map (σ : E →+* E).toIntAlgHom
    exact tmul_mem v ha ⟨_, hy⟩
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_int_of_fixed (h : IsCMExt F E σ) (x : 𝓞 E) (hx : σ (x : E) = x) :
    ∃ f : 𝓞 F, algebraMap F E (f : F) = x := by
  obtain ⟨f, hf⟩ := GlobalTheory.SelfDualLatticeCompare.exists_of_conj_eq h _ hx
  have hfi : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hf]
    exact x.2
  exact ⟨⟨f, hfi⟩, hf⟩

theorem trace_mem (h : IsCMExt F E σ) {s : A} (hs : s ∈ intA (E := E) v) :
    ∃ c ∈ O, s + sigR (Fv F v) σ s = algebraMap (Fv F v) A c := by
  have hgen : ∀ y ∈ (Submonoid.closure {y : A | ∃ a ∈ O, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} : Set A),
      ∃ a ∈ O, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      obtain ⟨b, hb, x', rfl⟩ := hz
      exact ⟨a * b, mul_mem ha hb, x * x', by rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl⟩
  have hs' := Subring.mem_closure_iff.1 hs
  clear hs
  induction hs' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hgen y hy
    have hfix : σ ((x : E) + σ x) = (x : E) + σ x := by
      rw [map_add, GlobalTheory.SelfDualLatticeCompare.conj_conj h, add_comm]
    have hxi : IsIntegral ℤ (σ (x : E)) := x.2.map (σ : E →+* E).toIntAlgHom
    obtain ⟨f, hf⟩ := exists_int_of_fixed h (x + ⟨_, hxi⟩) hfix
    refine ⟨a * algebraMap F (Fv F v) f, mul_mem ha (coe_mem v f), ?_⟩
    rw [sig_tmul, ← TensorProduct.tmul_add, ← tmul_algebraMap]
    congr 1
    exact hf.symm
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, e⟩ := hx
    obtain ⟨d, hd, e'⟩ := hy
    refine ⟨c + d, add_mem hc hd, ?_⟩
    rw [map_add, map_add, ← e, ← e']; ring
  | neg x _ hx =>
    obtain ⟨c, hc, e⟩ := hx
    refine ⟨-c, neg_mem hc, ?_⟩
    rw [map_neg, map_neg, ← e]; ring

end General

section Wexist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

local notation "A" => Fv F v ⊗[F] E
local notation "O" => v.adicCompletionIntegers F

theorem algebraMap_ne_zero {f : 𝓞 F} (hf : f ∉ v.asIdeal) : algebraMap F (Fv F v) (f : F) ≠ 0 := by
  intro h0
  apply hf
  have : (f : F) = 0 := (algebraMap F (Fv F v)).injective (by rw [h0, map_zero])
  have : f = 0 := RingOfIntegers.ext (by rw [this]; rfl)
  rw [this]; exact zero_mem _

theorem exists_w (h : IsCMExt F E σ) (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) :
    ∃ w ∈ intA (E := E) v, w + sigR (Fv F v) σ w = 1 ∧
      ∃ u ∈ intA (E := E) v, (w - sigR (Fv F v) σ w) * u = 1 := by
  obtain ⟨t, d, s, hd, hs, hsv⟩ := GlobalTheory.UnramConjUnit.exists_sub_conj_notMem h v hv
  have hti : IsIntegral ℤ (σ (t : E)) := t.2.map (σ : E →+* E).toIntAlgHom
  set t' : 𝓞 E := ⟨_, hti⟩ with ht'
  have hσσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  obtain ⟨r, hr⟩ := exists_int_of_fixed h (t + t') (by
    show σ ((t : E) + σ t) = (t : E) + σ t
    rw [map_add, hσσ, add_comm])
  obtain ⟨n, hn⟩ := exists_int_of_fixed h (t * t') (by
    show σ ((t : E) * σ t) = (t : E) * σ t
    rw [map_mul, hσσ, mul_comm])
  have hr' : algebraMap F E (r : F) = (t : E) + σ t := by rw [hr]; rfl
  have hn' : algebraMap F E (n : F) = (t : E) * σ t := by rw [hn]; rfl
  have hsr' : (s : F) = (r : F) ^ 2 - 4 * (n : F) := by
    apply (algebraMap F E).injective
    rw [map_sub, map_pow, map_mul, map_ofNat, hs, hr', hn', hd]
    ring
  have hsr : s = r ^ 2 - 4 * n := RingOfIntegers.ext (by rw [hsr']; push_cast; rfl)
  set ι := algebraMap (Fv F v) A with hι
  set rF := algebraMap F (Fv F v) (r : F) with hrF
  set sF := algebraMap F (Fv F v) (s : F) with hsF
  have hs0 : sF ≠ 0 := algebraMap_ne_zero v hsv
  obtain ⟨c, hc, b, hb, b', hb', hbb, hcb⟩ :
      ∃ c ∈ O, ∃ b ∈ O, ∃ b' ∈ O, b * b' = 1 ∧ 2 * c + b * rF = 1 := by
    by_cases hrv : r ∈ v.asIdeal
    · have h2 : (2 : 𝓞 F) ∉ v.asIdeal := by
        intro h2
        apply hsv
        rw [hsr]
        refine sub_mem (Ideal.pow_mem_of_mem _ hrv 2 two_pos) ?_
        have : (4 : 𝓞 F) * n = 2 * (2 * n) := by ring
        rw [this]
        exact Ideal.mul_mem_right _ _ h2
      have h20 := algebraMap_ne_zero v h2
      refine ⟨(algebraMap F (Fv F v) ((2 : 𝓞 F) : F))⁻¹ * (1 - rF),
        mul_mem (inv_mem v h2) (sub_mem (one_mem _) (coe_mem v r)), 1, one_mem _, 1, one_mem _, one_mul 1, ?_⟩
      have e2 : algebraMap F (Fv F v) ((2 : 𝓞 F) : F) = 2 := by
        rw [show ((2 : 𝓞 F) : F) = 2 from rfl, map_ofNat]
      rw [e2] at h20 ⊢
      field_simp
      ring
    · have hr0 : rF ≠ 0 := algebraMap_ne_zero v hrv
      exact ⟨0, zero_mem _, rF⁻¹, inv_mem v hrv, rF, coe_mem v r, inv_mul_cancel₀ hr0, by
        rw [mul_zero, zero_add, inv_mul_cancel₀ hr0]⟩
  have e1 : (1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] σ t = ι rF := by
    rw [← TensorProduct.tmul_add, ← hr', tmul_algebraMap, one_mul]
  have e2 : (1 : Fv F v) ⊗ₜ[F] (t : E) - (1 : Fv F v) ⊗ₜ[F] σ t = (1 : Fv F v) ⊗ₜ[F] (d : E) := by
    rw [← TensorProduct.tmul_sub, hd]
  have e3 : (1 : Fv F v) ⊗ₜ[F] (d : E) * (1 : Fv F v) ⊗ₜ[F] (d : E) = ι sF := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hs, tmul_algebraMap, one_mul]
  have hB : ι b * ι b' = 1 := by rw [← map_mul, hbb, map_one]
  have hS : ι sF⁻¹ * ι sF = 1 := by rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
  have hC : ι 2 * ι c + ι b * ι rF = 1 := by rw [← map_mul, ← map_mul, ← map_add, hcb, map_one]
  have h2ι : ι 2 = 2 := map_ofNat ι 2
  refine ⟨ι c + ι b * (1 : Fv F v) ⊗ₜ[F] (t : E),
    add_mem (iota_mem v hc) (mul_mem (iota_mem v hb) (tmul_mem v (one_mem _) t)), ?_,
    ι (b' * sF⁻¹) * (1 : Fv F v) ⊗ₜ[F] (d : E),
    mul_mem (iota_mem v (mul_mem hb' (inv_mem v hsv))) (tmul_mem v (one_mem _) d), ?_⟩
  · rw [map_add, map_mul, sig_iota, sig_iota, sig_tmul]
    simp only [← hι]
    rw [h2ι] at hC
    linear_combination ι b * e1 + hC
  · rw [map_add, map_mul, sig_iota, sig_iota, sig_tmul, map_mul]
    simp only [← hι]
    linear_combination (ι b * ι b' * ι sF⁻¹ * (1 : Fv F v) ⊗ₜ[F] (d : E)) * e2 +
      (ι b * ι b' * ι sF⁻¹) * e3 + (ι sF⁻¹ * ι sF) * hB + hS

end Wexist

section Good

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

local notation "A" => Fv F v ⊗[F] E
local notation "O" => v.adicCompletionIntegers F

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem valued_unif {π : 𝓞 F} (hπ1 : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2) :
    Valued.v (algebraMap F (Fv F v) (π : F)) = WithZero.exp (-1 : ℤ) := by
  rw [show algebraMap F (Fv F v) (π : F) = ((algebraMap (𝓞 F) F π : F) : Fv F v) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have h1 := (v.intValuation_le_pow_iff_mem π 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation π ≤ WithZero.exp (-(2 : ℕ) : ℤ) :=
    fun h => hπ2 ((v.intValuation_le_pow_iff_mem π 2).1 h)
  have h0 : v.intValuation π ≠ 0 := fun h => h2 (by rw [h]; exact zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  push_cast at h1 h2
  rw [show WithZero.log (v.intValuation π) = -1 by omega]

theorem div_mem_of_lt {π : 𝓞 F} (hπ1 : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2) {c : Fv F v}
    (hc : Valued.v c < 1) : c * (algebraMap F (Fv F v) (π : F))⁻¹ ∈ O := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_unif v hπ1 hπ2]
  have := le_exp_neg_one hc
  calc Valued.v c * (WithZero.exp (-1 : ℤ))⁻¹ ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ :=
        by gcongr
    _ = 1 := mul_inv_cancel₀ (by simp)

theorem fixed_mem (h : IsCMExt F E σ) {w : A} (hw : w ∈ intA (E := E) v)
    (hw1 : w + sigR (Fv F v) σ w = 1) {s : A} (hs : s ∈ intA (E := E) v) (hfix : sigR (Fv F v) σ s = s) :
    ∃ c ∈ O, s = algebraMap (Fv F v) A c := by
  obtain ⟨c, hc, e⟩ := trace_mem v h (mul_mem hs hw)
  refine ⟨c, hc, ?_⟩
  rw [← e, map_mul, hfix, ← mul_add, hw1, mul_one]

end Good

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

local notation "A" => Fv F v ⊗[F] E
local notation "O" => v.adicCompletionIntegers F

theorem goodRing_of (h : IsCMExt F E σ) (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) (π : 𝓞 F)
    (hπ1 : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2) :
    GoodRing (intA (E := E) v) (sigR (Fv F v) σ) ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F))
      (Ideal.absNorm v.asIdeal) := by
  obtain ⟨w, hw, hw1, u, hu, hwu⟩ := exists_w v h hv
  have hσσ := sig_sig v h
  set πF := algebraMap F (Fv F v) (π : F) with hπF
  have hπ0 : πF ≠ 0 := by
    intro h0
    have h1 := valued_unif v hπ1 hπ2
    rw [← hπF, h0, map_zero] at h1
    exact WithZero.zero_ne_coe h1
  have hϖ : (1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F) = algebraMap (Fv F v) A πF := by
    rw [tmul_algebraMap, one_mul]
  rw [hϖ]
  have hinj : Function.Injective (algebraMap (Fv F v) A) := (algebraMap (Fv F v) A).injective
  have hϖS : algebraMap (Fv F v) A πF ∈ intA (E := E) v := iota_mem v (coe_mem v π)
  have hnzd : ∀ a : A, algebraMap (Fv F v) A πF * a = 0 → a = 0 := fun a ha => by
    have e : algebraMap (Fv F v) A πF⁻¹ * (algebraMap (Fv F v) A πF * a) = a := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hπ0, map_one, one_mul]
    rw [← e, ha, mul_zero]
  have hσw : sigR (Fv F v) σ w = 1 - w := by linear_combination hw1
  have hσu : sigR (Fv F v) σ u = -u := by
    have h' : (sigR (Fv F v) σ w - w) * sigR (Fv F v) σ u = 1 := by
      have := congrArg (sigR (Fv F v) σ) hwu
      rwa [map_mul, map_sub, hσσ, map_one] at this
    linear_combination (-sigR (Fv F v) σ u) * hwu + (-u) * h'
  refine ⟨hσσ, fun s hs => sig_mem v h hs, hϖS, sig_iota v πF, hnzd,
    ⟨w, hw, hw1, ⟨u, hu, hwu⟩, fun s hs => ?_⟩, fun a ha hfix hnot => ?_, ?_⟩
  · have hb : (s - sigR (Fv F v) σ s) * u ∈ intA (E := E) v :=
      mul_mem (sub_mem hs (sig_mem v h hs)) hu
    have hbfix : sigR (Fv F v) σ ((s - sigR (Fv F v) σ s) * u) = (s - sigR (Fv F v) σ s) * u := by
      rw [map_mul, map_sub, hσσ, hσu]; ring
    refine ⟨s - (s - sigR (Fv F v) σ s) * u * w, sub_mem hs (mul_mem hb hw),
      (s - sigR (Fv F v) σ s) * u, hb, ?_, hbfix, by ring⟩
    rw [map_sub, map_mul, hbfix, hσw]
    linear_combination (s - sigR (Fv F v) σ s) * hwu + (s - sigR (Fv F v) σ s) * u * hσw
  · obtain ⟨c, hc, rfl⟩ := fixed_mem v h hw hw1 ha hfix
    have hc1 : ¬ Valued.v c < 1 := fun hlt => hnot ⟨algebraMap (Fv F v) A (c * πF⁻¹),
      iota_mem v (div_mem_of_lt v hπ1 hπ2 hlt), by
        rw [pow_one, ← map_mul]
        congr 1
        field_simp⟩
    have hcv : Valued.v c = 1 :=
      le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 hc) (not_lt.1 hc1)
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcv
      exact zero_ne_one hcv
    refine ⟨algebraMap (Fv F v) A c⁻¹, iota_mem v ?_, by rw [← map_mul, mul_inv_cancel₀ hc0, map_one]⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hcv, inv_one]
  · let ψ : O →+* intA (E := E) v :=
      ((algebraMap (Fv F v) A).comp (v.adicCompletionIntegers F).subtype).codRestrict (intA (E := E) v)
        (fun c => iota_mem v c.2)
    let φ : O →+* Res (intA (E := E) v) (algebraMap (Fv F v) A πF) := (Ideal.Quotient.mk _).comp ψ
    have hred : ∀ c : O, red (intA (E := E) v) (algebraMap (Fv F v) A πF) (algebraMap (Fv F v) A c) = φ c := by
      intro c
      unfold red
      rw [dif_pos (iota_mem v c.2)]
      rfl
    have hset : ∀ x, (∃ a ∈ intA (E := E) v, sigR (Fv F v) σ a = a ∧
        x = red (intA (E := E) v) (algebraMap (Fv F v) A πF) a) ↔ x ∈ φ.range := by
      intro x
      constructor
      · rintro ⟨a, ha, hfix, rfl⟩
        obtain ⟨c, hc, rfl⟩ := fixed_mem v h hw hw1 ha hfix
        exact ⟨⟨c, hc⟩, (hred ⟨c, hc⟩).symm⟩
      · rintro ⟨c, rfl⟩
        exact ⟨_, iota_mem v c.2, sig_iota v _, (hred c).symm⟩
    have hker : RingHom.ker φ = IsLocalRing.maximalIdeal O := by
      ext c
      rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have hc1 : Valued.v (c : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 c.2
      show Ideal.Quotient.mk _ (ψ c) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.SUCong.LevKer.mem_piIdeal_iff _ _ hϖS]
      constructor
      · rintro ⟨t, ht, e⟩
        have e' : (ψ c : A) = algebraMap (Fv F v) A c := rfl
        rw [e'] at e
        have htfix : sigR (Fv F v) σ t = t := by
          have := congrArg (sigR (Fv F v) σ) e
          rw [sig_iota, map_mul, sig_iota, e] at this
          exact (sub_eq_zero.1 (hnzd _ (by rw [mul_sub, ← this, sub_self]))).symm
        obtain ⟨c', hc', rfl⟩ := fixed_mem v h hw hw1 ht htfix
        rw [← map_mul] at e
        have e2 := hinj e
        intro hv1
        have hle : Valued.v (c' : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 hc'
        have : Valued.v (c : Fv F v) ≤ WithZero.exp (-1 : ℤ) := by
          rw [e2, map_mul, valued_unif v hπ1 hπ2]
          calc WithZero.exp (-1 : ℤ) * Valued.v c' ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
            _ = _ := mul_one _
        rw [hv1] at this
        exact absurd this (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
      · intro hne
        have hlt : Valued.v (c : Fv F v) < 1 := lt_of_le_of_ne hc1 hne
        refine ⟨algebraMap (Fv F v) A ((c : Fv F v) * πF⁻¹), iota_mem v (div_mem_of_lt v hπ1 hπ2 hlt), ?_⟩
        show algebraMap (Fv F v) A c = _
        rw [← map_mul]
        congr 1
        field_simp
    calc Nat.card {x : Res (intA (E := E) v) (algebraMap (Fv F v) A πF) // ∃ a ∈ intA (E := E) v,
          sigR (Fv F v) σ a = a ∧ x = red (intA (E := E) v) (algebraMap (Fv F v) A πF) a}
        = Nat.card φ.range := Nat.card_congr (Equiv.subtypeEquivRight hset)
      _ = Nat.card (O ⧸ RingHom.ker φ) := Nat.card_congr (RingHom.quotientKerEquivRange φ).toEquiv.symm
      _ = Nat.card (IsLocalRing.ResidueField O) := by rw [hker]; rfl
      _ = Ideal.absNorm v.asIdeal := GroundTheory.Global.natCard_residueField_adicCompletionIntegers v

end Main

end GlobalTheory.SUCong.RingUnr

namespace GlobalTheory.SUCong

open GlobalTheory.SUCong.RingUnr

theorem goodRing_intA_of_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (π : 𝓞 (maximalRealSubfield E)),
      π ∈ v.asIdeal → π ∉ v.asIdeal ^ 2 →
      GoodRing (intA (E := E) v) (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom)
        ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E]
          algebraMap (maximalRealSubfield E) E (π : maximalRealSubfield E)) (Ideal.absNorm v.asIdeal) := by
  intro E _ _ _ hU v π hπ1 hπ2
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU
  have hcm : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  have hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt (maximalRealSubfield E) E v := by
    intro w _
    haveI := w.isPrime
    exact Ideal.ramificationIdx_eq_one w.asIdeal _
  exact goodRing_of v hcm hv π hπ1 hπ2

end GlobalTheory.SUCong
