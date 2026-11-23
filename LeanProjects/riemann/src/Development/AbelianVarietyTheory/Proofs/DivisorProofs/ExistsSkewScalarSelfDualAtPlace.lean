import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section
namespace GlobalTheory.SkewSelfDualInert
open Formalism.UG
open scoped nonZeroDivisors

theorem latLoc_le_of_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F), m ∉ v.asIdeal → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)),
    (∀ x ∈ L, algebraMap (𝓞 F) (𝓞 E) m • x ∈ L') → latLoc F L v ≤ latLoc F L' v := by
  intro F E _ _ _ _ _ n v m hm L L' h y hy
  have hval : v.valuation F (m : F) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one m) (not_lt.1 fun h => hm ((v.intValuation_lt_one_iff_mem m).1 h))
  have hm0 : (m : F) ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  set c : Fv F v := (algebraMap F (Fv F v) (m : F))⁻¹ with hcdef
  have hv1 : Valued.v (algebraMap F (Fv F v) (m : F)) = 1 := by
    rw [← hval]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)
  have hc : c ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hcdef, map_inv₀, hv1, inv_one]
  have hmc : algebraMap F (Fv F v) (m : F) * c = 1 :=
    mul_inv_cancel₀ ((map_ne_zero _).2 hm0)
  have hco : ((algebraMap (𝓞 F) (𝓞 E) m : 𝓞 E) : E) = algebraMap F E (m : F) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]; rfl
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have e : (fun i => a ⊗ₜ[F] x i) = fun i => (a * c) ⊗ₜ[F] (algebraMap (𝓞 F) (𝓞 E) m • x) i := by
    funext i
    have : (algebraMap (𝓞 F) (𝓞 E) m • x) i = (m : F) • x i := by
      rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
      exact congrArg (· * x i) hco
    rw [this, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm, mul_assoc, mul_comm c, hmc, mul_one]
  rw [e]
  exact tmul_mem_latLoc (mul_mem ha hc) (h x hx)

theorem exists_local_generator : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I p : Ideal R), I ≠ ⊥ → p ≠ ⊤ →
    ∃ g ∈ I, g ≠ 0 ∧ ∃ s : R, s ∉ p ∧ ∀ x ∈ I, s * x ∈ Ideal.span {g} := by
  intro R _ _ I p hI hp
  have hne : ¬ I ≤ p * I := by
    intro hle
    have h1 : p * I = I := le_antisymm (Ideal.mul_le.2 fun a _ b hb => Ideal.mul_mem_left _ _ hb) hle
    have h2 : p = 1 := mul_right_cancel₀ hI (h1.trans (one_mul I).symm)
    exact hp (h2.trans Ideal.one_eq_top)
  obtain ⟨g, hgI, hgp⟩ := Set.not_subset.1 hne
  have hg0 : g ≠ 0 := fun h => hgp (h ▸ zero_mem _)
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgI)
  have hCp : ¬ C ≤ p := fun hCp => hgp (by
    have : Ideal.span {g} ≤ p * I := by
      rw [hC, mul_comm]; exact Ideal.mul_mono_left hCp
    exact this (Ideal.mem_span_singleton_self g))
  obtain ⟨s, hsC, hsp⟩ := Set.not_subset.1 hCp
  exact ⟨g, hgI, hg0, s, hsp, fun x hx => by rw [hC, mul_comm s]; exact Ideal.mul_mem_mul hx hsC⟩

theorem exists_smul_unit_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal → ∀ δ₁ : 𝓞 E, δ₁ ≠ 0 →
    ∃ f : F, f ≠ 0 ∧ ∃ u : 𝓞 E, (u : E) = algebraMap F E f * (δ₁ : E) ∧ u ∉ w.asIdeal := by
  intro F E _ _ _ _ _ v w hw δ₁ hδ₁
  classical
  obtain ⟨π, hπv, hπ0, s, hs, hsπ⟩ := exists_local_generator (𝓞 F) v.asIdeal v.asIdeal v.ne_bot v.isPrime.ne_top
  set P := w.asIdeal
  have hex : ∃ i, δ₁ ∉ P ^ i := by
    by_contra h
    push_neg at h
    have : δ₁ ∈ ⨅ i, P ^ i := Submodule.mem_iInf _ |>.2 h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain P w.isPrime.ne_top] at this
    exact hδ₁ this
  let i := Nat.find hex
  have hi : δ₁ ∉ P ^ i := Nat.find_spec hex
  have hi0 : i ≠ 0 := fun h => hi (by rw [h, pow_zero, Ideal.one_eq_top]; trivial)
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi0
  have hδj : δ₁ ∈ P ^ j := by
    by_contra h; exact Nat.find_min hex (by omega : j < i) h

  have hle1 : Ideal.span {s} * v.asIdeal ≤ Ideal.span {π} := Ideal.mul_le.2 fun a ha b hb => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [mul_assoc]; exact Ideal.mul_mem_left _ _ (hsπ b hb)
  have hle2 : Ideal.span {s ^ j} * v.asIdeal ^ j ≤ Ideal.span {π ^ j} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    exact Ideal.pow_right_mono hle1 j
  have hle3 := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 E)) hle2
  rw [Ideal.map_mul, Ideal.map_pow, hw, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton] at hle3
  have hmem := hle3 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hδj)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
  have hco : ∀ a : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = algebraMap F E (a : F) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]; rfl
  have hπF : (π : F) ≠ 0 := by exact_mod_cast hπ0
  refine ⟨(s : F) ^ j / (π : F) ^ j, ?_, t, ?_, ?_⟩
  · have hsF : (s : F) ≠ 0 := by
      intro h0
      have : s = 0 := by exact_mod_cast h0
      exact hs (this ▸ zero_mem _)
    exact div_ne_zero (pow_ne_zero _ hsF) (pow_ne_zero _ hπF)
  · have e1 : (t : E) * algebraMap F E ((π : F) ^ j) = algebraMap F E ((s : F) ^ j) * (δ₁ : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ht
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow] at h2
      have h3 : ∀ a : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap F E (a : F) := hco
      rw [h3, h3] at h2
      rw [map_pow, map_pow]
      exact h2
    have hπE : algebraMap F E ((π : F) ^ j) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hπF)
    rw [map_div₀, div_mul_eq_mul_div, eq_div_iff hπE, e1]
  · intro htP
    have hπP : algebraMap (𝓞 F) (𝓞 E) π ∈ P := hw ▸ Ideal.mem_map_of_mem _ hπv
    have h1 : algebraMap (𝓞 F) (𝓞 E) (s ^ j) * δ₁ ∈ P ^ (j + 1) := by
      rw [← ht, pow_succ', map_pow]
      exact Ideal.mul_mem_mul htP (Ideal.pow_mem_pow hπP j)
    have hsP : algebraMap (𝓞 F) (𝓞 E) s ∉ P := by
      intro h
      have hc : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) P = v.asIdeal :=
        ((v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top)
          (by show v.asIdeal ≤ Ideal.comap _ P; rw [← hw]; exact Ideal.le_comap_map))).symm
      exact hs (hc ▸ Ideal.mem_comap.2 h)
    have hcop : IsCoprime (P ^ (j + 1)) (Ideal.span {algebraMap (𝓞 F) (𝓞 E) (s ^ j)}) := by
      rw [map_pow, ← Ideal.span_singleton_pow]
      refine IsCoprime.pow ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have := w.isMaximal.eq_of_le hne le_sup_left
      apply hsP
      show _ ∈ w.asIdeal
      rw [this]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hdvd : P ^ (j + 1) ∣ Ideal.span {algebraMap (𝓞 F) (𝓞 E) (s ^ j)} * Ideal.span {δ₁} := by
      rw [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact h1
    have := hcop.dvd_of_dvd_mul_left hdvd
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at this
    exact hi (hj ▸ this)

theorem exists_mem_span_not_mem_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal → ∀ c : 𝓞 E, c ∉ w.asIdeal →
    ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) s ∈ Ideal.span {c} := by
  intro F E _ _ _ _ _ v w hw c hc
  by_contra hcon
  push_neg at hcon
  have hle : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {c}) ≤ v.asIdeal := fun s hs =>
    by_contra fun h => hcon s h hs
  obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal _ hle
  have hwQ : w.asIdeal ≤ Q := hw ▸ Ideal.map_le_iff_le_comap.2 hQc.ge
  have hQw : w.asIdeal = Q := w.isMaximal.eq_of_le hQp.ne_top hwQ
  exact hc (hQw ▸ hQ (Ideal.mem_span_singleton_self c))

theorem differentIdeal_eq_map_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) →
    differentIdeal ℤ (𝓞 E) = Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) := by
  intro F E _ _ _ _ _ hU
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]
  have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hPd⟩ := Ideal.exists_le_maximal _ h
    have := hP.isPrime
    exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hPd)
  rw [htop, Ideal.top_mul]

theorem traceDual_iff_mul_different : ∀ (E : Type) [Field E] [NumberField E] (z : E),
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * z))) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 E), IsIntegral ℤ ((d : E) * z) := by
  intro E _ _ z
  have hD := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1
  have hint : ∀ q : ℚ, IsIntegral ℤ q ↔ q ∈ (algebraMap ℤ ℚ).range := fun q => IsIntegrallyClosed.isIntegral_iff
  have hintE : ∀ e : E, IsIntegral ℤ e ↔ e ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := fun e =>
    ⟨fun h => FractionalIdeal.mem_one_iff _ |>.2 ⟨⟨e, h⟩, rfl⟩, fun h => by
      obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 h; exact x.isIntegral_coe⟩
  have hmem : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * z)) := by
    rw [FractionalIdeal.mem_dual h1]
    constructor
    · intro h o
      rw [hint, mul_comm]
      exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [Algebra.traceForm_apply, ← hint, mul_comm]
      exact h o
  rw [← hmem]
  constructor
  · intro hz d hd
    rw [hintE]
    have hd' : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
    rw [hD] at hd'
    have := FractionalIdeal.mul_mem_mul hd' hz
    rwa [inv_mul_cancel₀ hdual0] at this
  · intro h
    have : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
        (((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by rw [hD, inv_inv]
    rw [this, FractionalIdeal.mem_inv_iff (by rw [hD]; exact inv_ne_zero hdual0)]
    intro y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [mul_comm, ← hintE]
    exact h d hd

theorem exists_delta_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ ∧ ∃ m : 𝓞 F, m ∉ v.asIdeal ∧
      (∀ z : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * z))) →
        IsIntegral ℤ (((algebraMap (𝓞 F) (𝓞 E) m : 𝓞 E) : E) * δ * z)) ∧
      ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (((algebraMap (𝓞 F) (𝓞 E) m : 𝓞 E) : E) / δ))) := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 E), Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := by
    rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with h | h
    · exact (hv.false h.some).elim
    · exact h
  have hco : ∀ a : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = algebraMap F E (a : F) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]; rfl
  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  set δ₁ : 𝓞 E := 2 * θ - 1 with hδ₁
  have hδ₁E : (δ₁ : E) = 2 * (θ : E) - 1 := by
    show algebraMap (𝓞 E) E (2 * θ - 1) = _
    rw [map_sub, map_mul, map_ofNat, map_one]
  have hδ₁σ : σ (δ₁ : E) = -(δ₁ : E) := by
    rw [hδ₁E, map_sub, map_mul, map_ofNat, map_one]; linear_combination 2 * hθ
  have hδ₁0 : δ₁ ≠ 0 := by
    intro h0
    have h1 : (θ : E) = algebraMap ℚ E (1 / 2) := by
      have : (δ₁ : E) = 0 := by rw [h0]; rfl
      rw [hδ₁E] at this
      rw [map_div₀, map_one, map_ofNat]; linear_combination this / 2
    have h2 : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := h1 ▸ θ.isIntegral_coe
    rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective, IsIntegrallyClosed.isIntegral_iff] at h2
    obtain ⟨y, hy⟩ := h2
    have : (2 : ℚ) * (y : ℚ) = 1 := by rw [eq_intCast] at hy; rw [hy]; norm_num
    have : (2 * y : ℤ) = 1 := by exact_mod_cast this
    omega
  obtain ⟨f, hf0, u, hu, huw⟩ := exists_smul_unit_at_inert F E v w hw δ₁ hδ₁0
  obtain ⟨s₂, hs₂, hs₂u⟩ := exists_mem_span_not_mem_of_inert F E v w hw u huw
  have hd := differentIdeal_eq_map_of_unramified F E hB.unram
  obtain ⟨g, hg, hg0, s, hs, hsg⟩ := exists_local_generator (𝓞 F) (differentIdeal ℤ (𝓞 F)) v.asIdeal
    differentIdeal_ne_bot v.isPrime.ne_top
  have hu0 : u ≠ 0 := fun h => huw (h ▸ zero_mem _)
  have hgE : ((algebraMap (𝓞 F) (𝓞 E) g : 𝓞 E) : E) ≠ 0 := by
    rw [hco]; exact (map_ne_zero _).2 (by exact_mod_cast hg0)
  have huE : (u : E) ≠ 0 := by exact_mod_cast hu0
  refine ⟨((algebraMap (𝓞 F) (𝓞 E) g : 𝓞 E) : E) * u, mul_ne_zero hgE huE, ?_, s * s₂, ?_, ?_, ?_⟩
  · rw [map_mul, hco, AlgHom.commutes, hu, map_mul, AlgHom.commutes, hδ₁σ]; ring
  · intro h
    rcases v.isPrime.mem_or_mem h with h | h
    · exact hs h
    · exact hs₂ h
  · intro z hz
    have hdm : algebraMap (𝓞 F) (𝓞 E) (s * s₂) * (algebraMap (𝓞 F) (𝓞 E) g * u) ∈ differentIdeal ℤ (𝓞 E) := by
      rw [hd]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hg))
    have := (traceDual_iff_mul_different E z).1 hz _ hdm
    convert this using 2
    push_cast; ring
  · refine (traceDual_iff_mul_different E _).2 fun d hdd => ?_
    have hsd : algebraMap (𝓞 F) (𝓞 E) s * d ∈ Ideal.span {algebraMap (𝓞 F) (𝓞 E) g} := by
      have hle : Ideal.span {s} * differentIdeal ℤ (𝓞 F) ≤ Ideal.span {g} := by
        refine Ideal.mul_le.2 fun a ha b hb => ?_
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
        rw [mul_assoc]; exact Ideal.mul_mem_left _ _ (hsg b hb)
      have := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 E)) hle
      rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at this
      exact this (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hd ▸ hdd))
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hsd
    obtain ⟨t₂, ht₂⟩ := Ideal.mem_span_singleton'.1 hs₂u
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) s : 𝓞 E) : E) * d = (t : E) * ((algebraMap (𝓞 F) (𝓞 E) g : 𝓞 E) : E) := by
      exact_mod_cast ht.symm
    have e2 : ((algebraMap (𝓞 F) (𝓞 E) s₂ : 𝓞 E) : E) = (t₂ : E) * u := by exact_mod_cast ht₂.symm
    have : (d : E) * (((algebraMap (𝓞 F) (𝓞 E) (s * s₂) : 𝓞 E) : E) / (((algebraMap (𝓞 F) (𝓞 E) g : 𝓞 E) : E) * u))
        = ((t * t₂ : 𝓞 E) : E) := by
      rw [map_mul]; push_cast
      rw [show (d : E) * (((algebraMap (𝓞 F) (𝓞 E) s : 𝓞 E) : E) * ((algebraMap (𝓞 F) (𝓞 E) s₂ : 𝓞 E) : E) /
        (((algebraMap (𝓞 F) (𝓞 E) g : 𝓞 E) : E) * u)) = (((algebraMap (𝓞 F) (𝓞 E) s : 𝓞 E) : E) * d) *
          ((algebraMap (𝓞 F) (𝓞 E) s₂ : 𝓞 E) : E) / (((algebraMap (𝓞 F) (𝓞 E) g : 𝓞 E) : E) * u) by ring,
        e1, e2]
      field_simp
    rw [this]; exact (t * t₂).isIntegral_coe

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hE_smul_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : E) (x y : Fin n → E) :
    hE σ (δ • Jᵀ) x y = δ * form σ J y x := by
  rw [← GlobalTheory.HermSelfDualLoc.hE_transpose]
  simp only [hE, Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    form σ J (c • y) x = c * form σ J y x := by
  simp [form, smul_dotProduct]

theorem skew_isSelfDualAt_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → ∀ v : Pl F,
    IsEmpty (E →ₐ[F] Fv F v) → ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ ∧ IsSelfDualAt σ (δ • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d r s W hB hW v hv
  obtain ⟨δ, hδ0, hσδ, m, hm, ha, hb⟩ := exists_delta_inert F E σ B hB v hv
  refine ⟨δ, hδ0, hσδ, ?_⟩
  have hJ : (δ • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hδ0) (GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B d r s W hW)
  set M : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) m
  have hM : ∀ y : Fin d → E, M • y = (M : E) • y := fun y => rfl
  have h1 : ∀ y ∈ W.L, M • y ∈ GlobalTheory.AdelicU.SelfDual.dualGlob σ (δ • W.Jᵀ) W.L := by
    intro y hy x hx
    rw [hE_smul_transpose, hM, form_smul_left, ← GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]
    have := ha _ ((hW.dual y).1 hy x hx)
    convert this using 1; ring
  have h2 : ∀ y ∈ GlobalTheory.AdelicU.SelfDual.dualGlob σ (δ • W.Jᵀ) W.L, M • y ∈ W.L := by
    intro y hy
    refine (hW.dual _).2 fun x hx o => ?_
    obtain ⟨e, he⟩ := hy x hx
    rw [hE_smul_transpose] at he
    rw [hM, form_smul_left]
    have key : (o : E) * ((M : E) * form σ W.J y x) = ((o * e : 𝓞 E) : E) * ((M : E) / δ) := by
      have he' : ((o * e : 𝓞 E) : E) = (o : E) * (δ * form σ W.J y x) := by rw [← he]; rfl
      rw [he']; field_simp
    rw [key]; exact hb _
  unfold IsSelfDualAt
  rw [← GlobalTheory.AdelicU.SelfDual.latLoc_dualGlob hJ hW.lat]
  exact le_antisymm (latLoc_le_of_smul F E d v m hm _ _ h1) (latLoc_le_of_smul F E d v m hm _ _ h2)

end GlobalTheory.SkewSelfDualInert
