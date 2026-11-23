import Formalism.LocalToGlobal.GlobalTheory.GL6.AdmissibleOfSplitAndRoundTrips
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial Filter Topology
open Formalism.UG Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Hens

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem valuation_le_of_pow_dvd {ϖ x : v.adicCompletionIntegers K} {n : ℕ} (h : ϖ ^ n ∣ x) :
    Valued.v (x : v.adicCompletion K) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := by
  obtain ⟨y, rfl⟩ := h
  have hy : Valued.v (y : v.adicCompletion K) ≤ 1 := y.2
  push_cast
  rw [map_mul, map_pow]
  calc Valued.v (ϖ : v.adicCompletion K) ^ n * Valued.v (y : v.adicCompletion K)
      ≤ Valued.v (ϖ : v.adicCompletion K) ^ n * 1 := by gcongr
    _ = Valued.v (ϖ : v.adicCompletion K) ^ n := mul_one _

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
  rw [ValuationSubring.valuation_lt_one_iff]
  have hE := Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))
  have key : ∀ x : v.adicCompletion K, (v.adicCompletionIntegers K).valuation x < 1 ↔ Valued.v x < 1 := by
    intro x
    have := (hE.lt_iff_lt (x := x) (y := 1)).symm
    rwa [map_one, map_one] at this
  rw [key, algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
  exact valuation_lt_one_iff_mem v r

end Hens

section Idem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_ne_zero_odd_prime_field {G : Type} [Field G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) (h2 : p ≠ 2) :
    (2 : G) ≠ 0 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.ne_zero)
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP G p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hG)
  intro h
  have h' : ((2 : ℕ) : G) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff G p] at h'
  have h3 := Nat.le_of_dvd (by norm_num) h'
  have h4 := hp.two_le
  omega

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
  letI := D.host.cmStar
  exact bridge_star_holds D.R D.host x

theorem host_conj_involutive (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  exact D.host.conj_conj x

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

theorem local_diamonds_exist_all (Tf : FormsTied D u) : LocalDiamondElementsExist Tf :=
  local_diamonds_of_split Tf (splitAtT_of_tied Tf.atT)

theorem diamond_elements_exist_all (Tf : FormsTied D u) : DiamondElementsExist Tf := by
  exact diamond_elements_of_local Tf (local_diamonds_exist_all Tf)

theorem DiaMul_tied (Tf : FormsTied D u) : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u := by
  exact diamond_mul_of_local_diamonds Tf (local_diamonds_exist_all Tf)

theorem TrIso_tied (Tf : FormsTied D u) : Formalism.MainNotions.product_first_zeroth_parts.TrIso D u := by
  exact transport_iso_of_diamond_elements Tf (diamond_elements_exist_all Tf)

end Tied

theorem admissible_of_round_trips
    (hR : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u ∧ Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u) :
    LinkAdmT := by
  exact admissible_of_diamonds_and_round_trips (fun _ _ Tf _ => diamond_elements_exist_all Tf) hR

theorem hecke_identities_no_kernel_of_split
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u →
      (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
        Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ)) ∧
      (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
        Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) ∧
      (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
        (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
          ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ)) :
    FrobeniusNoKernelFamily := by
  exact frobenius_no_kernel_of_frobenius_similitude (fun _ _ Tf _ => diamond_elements_exist_all Tf) h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
