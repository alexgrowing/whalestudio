import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.LocalDiamondOfSplitIdempotent
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial Filter Topology
open Formalism.UG Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Hens

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem valuation_le_of_pow_dvd {ϖ x : v.adicCompletionIntegers K} {n : ℕ} (h : ϖ ^ n ∣ x) :
    Valued.v (x : v.adicCompletion K) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := by
  obtain ⟨y, rfl⟩ := h
  have hy : Valued.v (y : v.adicCompletion K) ≤ 1 := by
    first
      | exact y.2
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K).1 y.2
      | simpa using y.2
  have hc : ((ϖ ^ n * y : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (ϖ : v.adicCompletion K) ^ n * (y : v.adicCompletion K) := by
    first
      | rfl
      | (push_cast; rfl)
      | simp
  rw [hc, map_mul, map_pow]
  exact mul_le_of_le_one_right' hy

theorem completion_integers_precomplete {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    IsPrecomplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by
  have hI : ∀ (n : ℕ) (x : v.adicCompletionIntegers K),
      x ∈ ((maximalIdeal (v.adicCompletionIntegers K)) ^ n • ⊤ :
        Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K)) ↔ ϖ ^ n ∣ x := by
    intro n x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hϖ0 : (ϖ : v.adicCompletion K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hlt : Valued.v (ϖ : v.adicCompletion K) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ N a b, N ≤ a → N ≤ b → ϖ ^ N ∣ f a - f b := by
    intro N a b ha hb
    rcases le_total a b with h | h
    · have := hf h
      rw [SModEq.sub_mem, hI] at this
      exact (pow_dvd_pow ϖ ha).trans this
    · have := hf h
      rw [SModEq.sub_mem, hI] at this
      exact (pow_dvd_pow ϖ hb).trans (dvd_sub_comm.1 this)
  set g : ℕ → v.adicCompletion K := fun n => (f n : v.adicCompletion K) with hg
  have hC : CauchySeq g := by
    rw [(Valued.hasBasis_uniformity (v.adicCompletion K) (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro y _
    obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt
      (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (.ofClass (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))))) y)
    refine ⟨N, fun m hm n hn => ?_⟩
    show Valued.v.restrict (g n - g m) < y.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt ?_ hN
    have := valuation_le_of_pow_dvd v (hd N n m hn hm)
    exact this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hC
  have hO : IsClosed ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    Valued.isClosed_valuationSubring (v.adicCompletion K)
  have hLm : L ∈ v.adicCompletionIntegers K :=
    hO.mem_of_tendsto hL (Eventually.of_forall fun n => (f n).2)
  refine ⟨⟨L, hLm⟩, fun n => ?_⟩
  rw [SModEq.sub_mem, hI]
  have hpn : (ϖ : v.adicCompletion K) ^ n ≠ 0 := pow_ne_zero _ hϖ0
  have hS : IsClosed ((fun x => (x - g n) * ((ϖ : v.adicCompletion K) ^ n)⁻¹) ⁻¹'
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hLS := hS.mem_of_tendsto hL (by
    rw [eventually_atTop]
    refine ⟨n, fun m hm => ?_⟩
    obtain ⟨c, hc⟩ := hd n m n hm le_rfl
    show (g m - g n) * ((ϖ : v.adicCompletion K) ^ n)⁻¹ ∈ v.adicCompletionIntegers K
    have : g m - g n = (ϖ : v.adicCompletion K) ^ n * (c : v.adicCompletion K) := by
      simp only [hg]
      exact congrArg Subtype.val hc
    rw [this, mul_comm, ← mul_assoc, inv_mul_cancel₀ hpn, one_mul]
    exact c.2)
  refine ⟨-⟨_, hLS⟩, Subtype.ext ?_⟩
  show g n - L = (ϖ : v.adicCompletion K) ^ n * -((L - g n) * ((ϖ : v.adicCompletion K) ^ n)⁻¹)
  field_simp
  ring

theorem hensel_sqrt_completion_integers (a b : v.adicCompletionIntegers K) (hab : b * b - a ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hu : IsUnit (2 * b)) :
    ∃ r : v.adicCompletionIntegers K, r * r = a ∧ r - b ∈ maximalIdeal (v.adicCompletionIntegers K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := completion_integers_precomplete v hϖ
  have : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := {}
  have hm : (X ^ 2 - C a : (v.adicCompletionIntegers K)[X]).Monic := monic_X_pow_sub_C a two_ne_zero
  have hd : eval b (derivative (X ^ 2 - C a : (v.adicCompletionIntegers K)[X])) = 2 * b := by
    simp [one_add_one_eq_two]
  obtain ⟨r, hr, hrb⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K))
    (X ^ 2 - C a) hm b (by simpa [sq] using hab) (by rw [hd]; exact hu.map _)
  refine ⟨r, ?_, hrb⟩
  have h0 : r ^ 2 - a = 0 := by simpa using hr
  linear_combination h0

theorem mem_maximal_ideal_completion_iff (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈ maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  obtain ⟨x, hx⟩ : ∃ x, x = algebraMap R (v.adicCompletionIntegers K) r := ⟨_, rfl⟩
  rw [← hx]
  have hval : Valued.v (x : v.adicCompletion K) = v.intValuation r := by
    rw [hx]
    first
      | simp [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      | simp
  have hle : ∀ y : v.adicCompletionIntegers K, Valued.v (y : v.adicCompletion K) ≤ 1 := fun y => y.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hr
    apply hnu
    have h1 : Valued.v (x : v.adicCompletion K) = 1 := by
      rw [hval]
      first
        | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff v).2 hr
        | exact (v.intValuation_eq_one_iff).2 hr
        | exact (v.intValuation_eq_one_iff r).2 hr
    have hx0 : (x : v.adicCompletion K) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
      show Valued.v ((x : v.adicCompletion K)⁻¹) ≤ 1
      rw [map_inv₀, h1, inv_one]
    first
      | exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : v.adicCompletionIntegers K) (Subtype.ext (mul_inv_cancel₀ hx0))
      | exact IsUnit.of_mul_eq_one (a := x) (⟨_, hinv⟩ : v.adicCompletionIntegers K) (Subtype.ext (mul_inv_cancel₀ hx0))
      | exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
  · intro hr hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : Valued.v (x : v.adicCompletion K) < 1 := by
      rw [hval]
      first
        | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
        | exact (v.intValuation_lt_one_iff_mem r).2 hr
        | exact (v.intValuation_lt_one_iff_mem).2 hr
    have h3 : Valued.v ((x : v.adicCompletion K) * (y : v.adicCompletion K)) = 1 := by
      rw [show (x : v.adicCompletion K) * (y : v.adicCompletion K) =
        ((x * y : v.adicCompletionIntegers K) : v.adicCompletion K) from rfl, hy]
      simp
    rw [map_mul] at h3
    exact (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' (hle y)) h1)) h3

end Hens

section Idem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_ne_zero_odd_prime_field {G : Type} [Field G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) (h2 : p ≠ 2) :
    (2 : G) ≠ 0 := by
  intro h
  have hd2 : addOrderOf (1 : G) ∣ 2 := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [two_nsmul, one_add_one_eq_two]
    exact h
  have hdp : addOrderOf (1 : G) ∣ p := by
    rw [← hG]
    exact addOrderOf_dvd_natCard _
  rcases hp.eq_one_or_self_of_dvd _ hdp with h3 | h3
  · have h4 := addOrderOf_nsmul_eq_zero (1 : G)
    rw [h3, one_nsmul] at h4
    exact one_ne_zero h4
  · rw [h3] at hd2
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd2)

theorem split_idempotent_of_square_root (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (α : 𝓞 E) (a b : 𝓞 F)
    (hσ : σ (α : E) = -(α : E)) (ha : (α : E) * α = algebraMap F E (a : F))
    (hab : b * b - a ∈ v.asIdeal) (hb : b ∉ v.asIdeal) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ e ∈ intV E v, e * e = e ∧ sigR σ (v.adicCompletion F) e = 1 - e := by
  have hm := mem_maximal_ideal_completion_iff (K := F) v
  have hab' : algebraMap (𝓞 F) (v.adicCompletionIntegers F) b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) b -
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← map_mul, ← map_sub, hm]
    exact hab
  have h2b : (2 : 𝓞 F) * b ∉ v.asIdeal := fun h => (v.isPrime.mem_or_mem h).elim h2 hb
  have hu : IsUnit (2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) b) := by
    rw [← notMem_maximalIdeal]
    have : (2 : v.adicCompletionIntegers F) * algebraMap (𝓞 F) (v.adicCompletionIntegers F) b =
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) (2 * b) := by rw [map_mul, map_ofNat]
    rw [this, hm]
    exact h2b
  obtain ⟨r, hr, hrb⟩ := hensel_sqrt_completion_integers v _ _ hab' hu
  have hur : IsUnit (2 * r) := by
    rw [← notMem_maximalIdeal]
    intro h
    apply notMem_maximalIdeal.2 hu
    have : 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) b =
        2 * r - 2 * (r - algebraMap (𝓞 F) (v.adicCompletionIntegers F) b) := by ring
    rw [this]
    exact sub_mem h (Ideal.mul_mem_left _ _ hrb)
  obtain ⟨s, hs⟩ := hur.exists_right_inv
  set φ := (v.adicCompletionIntegers F).subtype
  set H : v.adicCompletion F := φ (r * s)
  set Y : v.adicCompletion F := φ s
  set A : v.adicCompletion F := algebraMap F (v.adicCompletion F) (a : F)
  have hA : φ (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) = A := rfl
  have hH2 : 2 * H = 1 := by
    have : (2 : v.adicCompletionIntegers F) * (r * s) = 1 := by rw [← hs]; ring
    have := congrArg φ this
    rwa [map_mul, map_ofNat, map_one] at this
  have hAY : A * (Y * Y) = H * H := by
    have : algebraMap (𝓞 F) (v.adicCompletionIntegers F) a * (s * s) = (r * s) * (r * s) := by
      rw [← hr]; ring
    have := congrArg φ this
    rwa [map_mul, map_mul, hA] at this
  have hR : ∀ y : v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] (φ y)) ∈ intV E v := fun y =>
    Subring.subset_closure (Or.inr ⟨⟨y, y.2⟩, rfl⟩)
  have hL : ((α : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ intV E v :=
    Subring.subset_closure (Or.inl ⟨⟨(α : E), ⟨α, rfl⟩⟩, rfl⟩)
  have hαα : ((α : E) * α) ⊗ₜ[F] (Y * Y) = (1 : E) ⊗ₜ[F] (A * (Y * Y)) := by
    rw [ha, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
  refine ⟨(1 : E) ⊗ₜ[F] H + (α : E) ⊗ₜ[F] Y, ?_, ?_, ?_⟩
  · refine add_mem (hR _) ?_
    have : (α : E) ⊗ₜ[F] Y = ((α : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] Y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact mul_mem hL (hR _)
  · have h1 : H * H + A * (Y * Y) = H := by linear_combination H * hH2 + hAY
    have h3 : H * Y + Y * H = Y := by linear_combination Y * hH2
    simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hαα]
    calc _ = (1 : E) ⊗ₜ[F] (H * H + A * (Y * Y)) + (α : E) ⊗ₜ[F] (H * Y + Y * H) := by
          simp only [TensorProduct.tmul_add]; abel
      _ = _ := by rw [h1, h3]
  · have h1 : (1 : v.adicCompletion F) = H + H := by linear_combination -hH2
    have hs1 : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] H + (α : E) ⊗ₜ[F] Y) =
        (1 : E) ⊗ₜ[F] H - (α : E) ⊗ₜ[F] Y := by
      simp only [sigR, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, map_add, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.id_apply, hσ, TensorProduct.neg_tmul, sub_eq_add_neg]
    rw [hs1, Algebra.TensorProduct.one_def]
    conv_rhs => rw [h1]
    rw [TensorProduct.tmul_add]
    abel

end Idem

section Tied

variable {D : D7} {u : D.what₂.Word}

theorem forms_involution_eq_host_conj (x : D.host.E) : sigD D x = D.host.conj x := by
  first
    | rfl
    | (unfold sigD; rfl)
    | (unfold sigD Formalism.BasicNotions.CMData.sig; rfl)
    | (simp only [sigD, Formalism.BasicNotions.CMData.sig]; rfl)
    | (unfold sigD Formalism.BasicNotions.CMData.sig; exact Formalism.L2.Herm.star_conj x)
    | (unfold sigD Formalism.BasicNotions.CMData.sig; simp only [starRingEnd_apply]; exact Formalism.L2.Herm.star_conj x)
    | (unfold sigD Formalism.BasicNotions.CMData.sig; simp; rfl)
    | (unfold sigD Formalism.BasicNotions.CMData.sig; simp [Formalism.BasicNotions.Host.cmStar])
    | (unfold sigD Formalism.BasicNotions.CMData.sig; simp only [starRingEnd_apply]; unfold Formalism.BasicNotions.Host.cmStar; simp)

theorem host_conj_involutive (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  first
    | simp
    | (rw [← forms_involution_eq_host_conj, ← forms_involution_eq_host_conj]; simp)
    | (letI := D.host.cmStar; rw [← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star])
    | (letI := D.host.cmStar; rw [← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj]; exact star_star x)

set_option maxHeartbeats 1000000 in

theorem splitAtT_of_tied (A : AtTTied u) : SplitAtT A := by
  intro v
  obtain ⟨pb, hpb⟩ : ∃ pb : 𝓞 D.host.E, (pb : D.host.E) = D.host.conj (A.piU : D.host.E) :=
    ⟨⟨_, map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe A.piU)⟩, rfl⟩
  have hres_pb := A.res_conj v pb hpb
  obtain ⟨α, hαd⟩ : ∃ α : 𝓞 D.host.E, α = A.piU - pb := ⟨_, rfl⟩
  have hαE : (α : D.host.E) = (A.piU : D.host.E) - D.host.conj (A.piU : D.host.E) := by
    rw [hαd, ← hpb]
    rfl
  have hσα : sigD D (α : D.host.E) = -(α : D.host.E) := by
    rw [hαE, map_sub, forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]
    ring
  have hfix : (α : D.host.E) * α ∈ (algebraMap D.host.F D.host.E).range := by
    letI := D.host.cmStar
    rw [← D.sp.cm.fixed]
    have h1 : star (α : D.host.E) = -(α : D.host.E) := hσα
    rw [star_mul, h1]
    ring
  obtain ⟨a0, ha0⟩ := hfix
  have ha0i : IsIntegral ℤ a0 := by
    have h1 : IsIntegral ℤ (algebraMap D.host.F D.host.E a0) := by
      rw [ha0]
      exact RingOfIntegers.isIntegral_coe (α * α)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
      (algebraMap D.host.F D.host.E).injective).1 h1
  obtain ⟨a, had⟩ : ∃ a : 𝓞 D.host.F, (a : D.host.F) = a0 := ⟨⟨a0, ha0i⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 D.host.F →+* (D.mem u).A.Fv v,
      ∀ x, ρ x = A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) :=
    ⟨(A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), fun _ => rfl⟩
  have hmem : ∀ x : 𝓞 D.host.F, x ∈ (A.eV v).1.asIdeal ↔ ρ x = 0 := fun x => by
    rw [A.res_v v, hρ]
  have hT := (D.mem u).A.T_prime
  have hcard : Nat.card ((D.mem u).A.Fv v) = (D.mem u).A.T := by
    rw [Nat.card_eq_fintype_card, (D.mem u).A.card_Fv v]
  have hsurj : Function.Surjective ρ := by
    have htop := subgroup_prime_card_eq_top hT hcard (ρ : 𝓞 D.host.F →+ (D.mem u).A.Fv v).range ⟨1, map_one ρ⟩ one_ne_zero
    intro y
    have hy : y ∈ (ρ : 𝓞 D.host.F →+ (D.mem u).A.Fv v).range := by rw [htop]; exact AddSubgroup.mem_top y
    exact AddMonoidHom.mem_range.1 hy
  obtain ⟨b, hb⟩ := hsurj (A.res v α)
  have hresα : A.res v α = -(A.res v pb) := by
    rw [hαd, map_sub, A.res_pi v, zero_sub]
  have hαa : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = α * α := by
    apply RingOfIntegers.ext
    show algebraMap D.host.F D.host.E (a : D.host.F) = (α : D.host.E) * α
    rw [had, ha0]
  have hbv : b ∉ (A.eV v).1.asIdeal := by
    rw [hmem, hb, hresα, neg_eq_zero]
    exact hres_pb
  have h2v : (2 : 𝓞 D.host.F) ∉ (A.eV v).1.asIdeal := by
    rw [hmem, map_ofNat]
    exact two_ne_zero_odd_prime_field hT hcard (D.T_ne_two u)
  have habv : b * b - a ∈ (A.eV v).1.asIdeal := by
    rw [hmem, map_sub, map_mul, hb, hρ, hαa, map_mul, sub_self]
  exact split_idempotent_of_square_root (sigD D) (A.eV v).1 α a b hσα (by rw [had, ha0]) habv hbv h2v

theorem diamond_elements_exist_all (Tf : Forms0 D u) : DiamondElementsExist Tf :=
  diamond_elements_of_split Tf (splitAtT_of_tied Tf.atT)

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0
