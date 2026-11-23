import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.PsiStd

def adelicAddChar (E : Type) [Field E] [NumberField E] : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF E) ℂ :=
  Circle.coeHom.compAddChar (adelicChar E)

theorem adelicAddChar_apply (E : Type) [Field E] [NumberField E] (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF E) :
    adelicAddChar E a = (adelicChar E a : ℂ) := rfl

theorem isStdChar_adelicAddChar (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar E (adelicAddChar E) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show Continuous (fun a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF E => ((adelicChar E a : Circle) : ℂ))
    exact continuous_subtype_val.comp continuous_adelicChar
  · intro x
    rw [adelicAddChar_apply]
    have h := (adelicChar E x).2
    exact mem_sphere_zero_iff_norm.mp h
  · intro a
    rw [adelicAddChar_apply]
    have h := adelicChar_algebraMap (K := E) a
    rw [show (Algebra.algebraMap E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF E) a)
        = algebraMap E (NumberField.AdeleRing (𝓞 E) E) a from rfl, h]
    simp
  · obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp (adelicChar_ne_one (K := E))
    refine ⟨x, ?_⟩
    rw [adelicAddChar_apply]
    intro h
    apply hx
    exact Subtype.ext h
  · intro x
    show ((adelicChar E (x, 0) : Circle) : ℂ) = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf E x
    rw [adelicChar_infinite, Real.fourierChar_apply]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf
    have ht : (infiniteTrace E x) = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x := rfl
    rw [ht]
    congr 1
    push_cast
    ring

private theorem eq_one_of_norm_one_of_forall_re_pow_pos (c : ℂ) (hc : ‖c‖ = 1)
    (h : ∀ m : ℕ, 0 < (c ^ m).re) : c = 1 := by
  have hce : c = Complex.exp (↑(Complex.arg c) * Complex.I) := by
    have h' := Complex.norm_mul_exp_arg_mul_I c
    rw [hc] at h'
    simpa using h'.symm
  by_cases h0 : Complex.arg c = 0
  · rw [hce, h0]
    simp
  exfalso
  set θ := Complex.arg c with hθ
  have hpos : 0 < |θ| := abs_pos.mpr h0
  have hle : |θ| ≤ Real.pi := Complex.abs_arg_le_pi c
  set m : ℕ := ⌈Real.pi / (2 * |θ|)⌉₊ with hm
  have h2pos : 0 < 2 * |θ| := by positivity
  have h1 : Real.pi / (2 * |θ|) ≤ (m : ℝ) := Nat.le_ceil _
  have h2 : (m : ℝ) < Real.pi / (2 * |θ|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1' : Real.pi ≤ (m : ℝ) * (2 * |θ|) := (div_le_iff₀ h2pos).mp h1
  have h2' : ((m : ℝ) - 1) * (2 * |θ|) < Real.pi := by
    have : (m : ℝ) - 1 < Real.pi / (2 * |θ|) := by linarith
    exact (lt_div_iff₀ h2pos).mp this
  have hA : Real.pi / 2 ≤ (m : ℝ) * |θ| := by nlinarith
  have hB : (m : ℝ) * |θ| ≤ Real.pi + Real.pi / 2 := by nlinarith
  have hre : (c ^ m).re = Real.cos ((m : ℝ) * |θ|) := by
    rw [hce, ← Complex.exp_nat_mul]
    have hx : (↑m * (↑θ * Complex.I) : ℂ) = ↑((m : ℝ) * θ) * Complex.I := by
      push_cast
      ring
    rw [hx, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs, abs_mul, Nat.abs_cast]
  have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hA hB
  have := h m
  rw [hre] at this
  linarith

private theorem stdChar_finite_algebraMap_eq_stdInf_neg (E : Type) [Field E] [NumberField E]
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF E) ℂ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar E ψ) (k : E) :
    ψ (finiteAdeleInr (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf E (-(algebraMap E (NumberField.InfiniteAdeleRing E) k)) := by
  have hsplit : (finiteAdeleInr (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) k) :
      NumberField.AdeleRing (𝓞 E) E) =
      algebraMap E (NumberField.AdeleRing (𝓞 E) E) k +
        infiniteAdeleInl (-(algebraMap E (NumberField.InfiniteAdeleRing E) k)) := by
    rw [← infiniteAdeleInl_add_finiteAdeleInr (algebraMap E (NumberField.AdeleRing (𝓞 E) E) k),
      adeleRing_algebraMap_fst, adeleRing_algebraMap_snd, map_neg]
    abel
  rw [hsplit, AddChar.map_add_eq_mul]
  have h1 : ψ (algebraMap E (NumberField.AdeleRing (𝓞 E) E) k) = 1 := hψ.1.2.2.1 k
  rw [h1, one_mul]
  exact hψ.2 _

private theorem valued_natCast_le_one_and_lt (E : Type) [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) :
    Valued.v (m : v.adicCompletion E) ≤ 1 ∧
      ((m : 𝓞 E) ∈ v.asIdeal → Valued.v (m : v.adicCompletion E) < 1) := by
  have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) v
    ((m : ℕ) : 𝓞 E)
  simp at h2
  constructor
  · have h3 : IsDedekindDomain.HeightOneSpectrum.valuation E v ((m : ℕ) : E) ≤ 1 := by
      simpa using IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := E) v ((m : ℕ) : 𝓞 E)
    rw [h2]
    exact h3
  · intro hm
    have h4 : IsDedekindDomain.HeightOneSpectrum.valuation E v ((m : ℕ) : E) < 1 := by
      simpa using (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v _).mpr hm
    rw [h2]
    exact h4

private theorem eventually_natCast_pow_mul_mem_nhds (E : Type) [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 E)) (u : Set (v.adicCompletion E))
    (hu : u ∈ nhds (0 : v.adicCompletion E))
    (q : ℕ) (hq : Valued.v (q : v.adicCompletion E) < 1) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ∀ x : v.adicCompletion E, Valued.v x ≤ 1 →
      (q : v.adicCompletion E) ^ M * x ∈ u := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
  obtain ⟨y0, hy0⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.val
  have hy0' : Valued.v.restrict y0 = γ.val := by rw [Valuation.restrict_def]; exact hy0
  have hy0ne : Valued.v y0 ≠ 0 := by
    intro h0
    have hz : y0 = 0 := (Valuation.zero_iff _).mp h0
    rw [hz, map_zero] at hy0'
    exact γ.ne_zero hy0'.symm
  have hq1 : Valued.v (q : v.adicCompletion E) ≤ WithZero.exp (-1 : ℤ) := by
    by_cases hq0 : Valued.v (q : v.adicCompletion E) = 0
    · rw [hq0]; exact zero_le
    · have hlog : WithZero.log (Valued.v (q : v.adicCompletion E)) < 0 := by
        have h1 : WithZero.exp (WithZero.log (Valued.v (q : v.adicCompletion E))) <
            WithZero.exp (0 : ℤ) := by
          rw [WithZero.exp_log hq0, WithZero.exp_zero]; exact hq
        exact WithZero.exp_lt_exp.mp h1
      calc Valued.v (q : v.adicCompletion E)
          ≤ WithZero.exp (WithZero.log (Valued.v (q : v.adicCompletion E))) := WithZero.le_exp_log
        _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
  refine ⟨(-(WithZero.log (Valued.v y0))).toNat + 1, fun M hM x hx => hγ ?_⟩
  show Valued.v.restrict ((q : v.adicCompletion E) ^ M * x) < γ.val
  rw [← hy0', Valuation.restrict_lt_iff, map_mul, Valuation.map_pow]
  calc Valued.v (q : v.adicCompletion E) ^ M * Valued.v x
      ≤ Valued.v (q : v.adicCompletion E) ^ M := by
        exact mul_le_of_le_one_right' hx
    _ ≤ WithZero.exp (-1 : ℤ) ^ M := pow_le_pow_left' hq1 M
    _ = WithZero.exp (M • (-1 : ℤ)) := (WithZero.exp_nsmul M (-1)).symm
    _ < Valued.v y0 := by
        rw [← WithZero.exp_log hy0ne, WithZero.exp_lt_exp, nsmul_eq_mul]
        omega

private theorem stdChar_finiteAdele_eq (E : Type) [Field E] [NumberField E]
    (ψ ψ' : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF E) ℂ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar E ψ)
    (hψ' : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar E ψ') (a : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) :
    ψ (finiteAdeleInr a) = ψ' (finiteAdeleInr a) := by
  classical
  set h : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E → ℂ :=
    fun b => ψ (finiteAdeleInr b) * (ψ' (finiteAdeleInr b))⁻¹ with hh
  have hne : ∀ b, ψ' (finiteAdeleInr b) ≠ 0 := by
    intro b h0
    have h1 := hψ'.1.2.1 (finiteAdeleInr b)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hmul : ∀ b c, h (b + c) = h b * h c := by
    intro b c
    simp only [hh, map_add, AddChar.map_add_eq_mul, mul_inv]
    ring
  have h0 : h 0 = 1 := by simp [hh]
  have hpow : ∀ (n : ℕ) b, h (n • b) = h b ^ n := by
    intro n b
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, hmul, ih, pow_succ]
  have hnorm : ∀ b, ‖h b‖ = 1 := by
    intro b
    simp only [hh, norm_mul, norm_inv, hψ.1.2.1, hψ'.1.2.1, inv_one, mul_one]
  have hF : ∀ k : E, h (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) k) = 1 := by
    intro k
    simp only [hh]
    rw [stdChar_finite_algebraMap_eq_stdInf_neg E ψ hψ k, stdChar_finite_algebraMap_eq_stdInf_neg E ψ' hψ' k]
    apply mul_inv_cancel₀
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf
    exact Complex.exp_ne_zero _
  have hinr : Continuous (fun b : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E =>
      (finiteAdeleInr b : NumberField.AdeleRing (𝓞 E) E)) := by
    show Continuous (fun b => ((0 : NumberField.InfiniteAdeleRing E), b))
    exact continuous_const.prodMk continuous_id
  have hcont : Continuous h := by
    have c1 : Continuous (fun b => ψ (finiteAdeleInr b)) := hψ.1.1.comp hinr
    have c2 : Continuous (fun b => ψ' (finiteAdeleInr b)) := hψ'.1.1.comp hinr
    exact c1.mul (c2.inv₀ hne)
  set U : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) := {b | 0 < (h b).re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hcont)
  have h0U : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) ∈ U := by
    show 0 < (h 0).re
    rw [h0]
    simp
  obtain ⟨n, hn0, hnU⟩ : ∃ n : ℕ, n ≠ 0 ∧
      ∀ z ∈ integralFiniteAdeles (𝓞 E) E, n • z ∈ U := by
    let ι : (∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) →
        IsDedekindDomain.FiniteAdeleRing (𝓞 E) E :=
      RestrictedProduct.structureMap _ _ Filter.cofinite
    have hιc : Continuous ι := RestrictedProduct.isEmbedding_structureMap.continuous
    have hι0 : ι 0 = 0 := by
      apply RestrictedProduct.ext
      intro v
      rfl
    have hV : ι ⁻¹' U ∈ nhds (0 : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) :=
      hιc.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hι0]; exact h0U))
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨I, t, ht, hIt⟩ := hV
    have hloc : ∀ v : HeightOneSpectrum (𝓞 E), ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
        ∀ y : v.adicCompletionIntegers E, ∀ x : v.adicCompletion E, Valued.v x ≤ 1 →
          (y : v.adicCompletion E) =
            ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion E) ^ M * x → y ∈ t v := by
      intro v
      obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht v)
      obtain ⟨N, hN⟩ := eventually_natCast_pow_mul_mem_nhds E v u hu (Ideal.absNorm v.asIdeal)
        ((valued_natCast_le_one_and_lt E v _).2 (Ideal.absNorm_mem v.asIdeal))
      refine ⟨N, fun M hM y x hx hyx => hut ?_⟩
      show (y : v.adicCompletion E) ∈ u
      rw [hyx]
      exact hN M hM x hx
    choose Nf hNf using hloc
    set S : ℕ := ∑ u ∈ I, Nf u with hS
    refine ⟨∏ u ∈ I, (Ideal.absNorm u.asIdeal) ^ S, ?_, ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro u _
      exact pow_ne_zero _ (fun h0 => u.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
    · intro z hz
      rw [mem_integralFiniteAdeles] at hz
      let z' : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E :=
        fun v => ⟨(∏ u ∈ I, (Ideal.absNorm u.asIdeal) ^ S) • z v, nsmul_mem (hz v) _⟩
      have hz' : ι z' = (∏ u ∈ I, (Ideal.absNorm u.asIdeal) ^ S) • z := by
        apply RestrictedProduct.ext
        intro v
        first
          | rfl
          | (rw [RestrictedProduct.nsmul_apply]; rfl)
      have hz'' : z' ∈ (↑I : Set (HeightOneSpectrum (𝓞 E))).pi t := by
        intro v hv
        have hvI : v ∈ I := Finset.mem_coe.mp hv
        have hprod : (Ideal.absNorm v.asIdeal) ^ S *
            ∏ u ∈ I.erase v, (Ideal.absNorm u.asIdeal) ^ S =
            ∏ u ∈ I, (Ideal.absNorm u.asIdeal) ^ S :=
          Finset.mul_prod_erase I (fun u => (Ideal.absNorm u.asIdeal) ^ S) hvI
        apply hNf v S (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hvI) (z' v)
          (((∏ u ∈ I.erase v, (Ideal.absNorm u.asIdeal) ^ S : ℕ) : v.adicCompletion E) * z v)
        · rw [map_mul]
          calc _ ≤ Valued.v (((∏ u ∈ I.erase v, (Ideal.absNorm u.asIdeal) ^ S : ℕ) :
                v.adicCompletion E)) :=
                mul_le_of_le_one_right'
                  ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hz v))
            _ ≤ 1 := (valued_natCast_le_one_and_lt E v _).1
        · show ((∏ u ∈ I, (Ideal.absNorm u.asIdeal) ^ S) • z v : v.adicCompletion E) = _
          rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_pow, ← Nat.cast_mul, hprod]
      rw [← hz']
      exact hIt hz''
  have hone : ∀ z ∈ integralFiniteAdeles (𝓞 E) E, h (n • z) = 1 := by
    intro z hz
    apply eq_one_of_norm_one_of_forall_re_pow_pos _ (hnorm _)
    intro m
    rw [← hpow, smul_smul, mul_comm, ← smul_smul]
    exact hnU _ (nsmul_mem hz m)
  have hint : ∀ y ∈ integralFiniteAdeles (𝓞 E) E, h y = 1 := by
    intro y hy
    set w := algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) ((n : E)⁻¹) * y with hw
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 E) (K := E) w
    have hyw : y = n • w := by
      rw [hw, nsmul_eq_mul, ← mul_assoc,
        ← map_natCast (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) n, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn0), map_one, one_mul]
    have hsplit : y = algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) ((n : E) * k) +
        n • (w - algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) k) := by
      rw [smul_sub, ← hyw, map_mul, map_natCast, ← nsmul_eq_mul]
      abel
    rw [hsplit, hmul, hF, hone _ hk, one_mul]
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 E) (K := E) a
  have ha : h a = 1 := by
    have hsum : a = algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) k +
        (a - algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) k) := by abel
    rw [hsum, hmul, hF, hint _ hk, one_mul]
  simp only [hh] at ha
  exact (mul_inv_eq_one₀ (hne a)).mp ha

theorem psiAt_eq_localAdelicChar : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E), psiAt w x = (localAdelicChar E w x : ℂ) := by
  intro E _ _ w x
  have h := stdChar_finiteAdele_eq E (GlobalTheory.HeckeEps.stdChar E) (adelicAddChar E)
    (GlobalTheory.HeckeEps.isStdChar_stdChar E) (isStdChar_adelicAddChar E w) (finiteAdeleSingleAdd w x)
  rw [localAdelicChar_apply, finitePlaceIncl_apply, ← adelicAddChar_apply]
  exact h

end GlobalTheory.CompanionTheory.PsiStd

end
