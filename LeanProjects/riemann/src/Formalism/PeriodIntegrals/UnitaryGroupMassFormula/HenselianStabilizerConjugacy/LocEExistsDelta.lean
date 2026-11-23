import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.IsSelfDual

noncomputable section

open scoped Classical
set_option linter.style.haveILetI false
open ValuativeRel

namespace PI.SelfDualHermitianLattices.Hd

open Formalism.MainNotions.S.Loc

section Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem locE_nontrivial (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega

theorem locE_cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

theorem locE_algMap_mem (L : LocE F E) [IsNonarchimedeanLocalField F] {f : F} :
    algebraMap F E f ∈ L.O ↔ f ∈ 𝒪[F] := by
  haveI := locE_nontrivial L
  rw [L.O_def]
  constructor
  · intro h
    have h' : IsIntegral 𝒪[F] f :=
      (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F])
        (algebraMap F E).injective).mp h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
    rw [← hy]; exact y.2
  · intro h
    have : algebraMap F E f = algebraMap 𝒪[F] E ⟨f, h⟩ := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
    rw [this]; exact isIntegral_algebraMap

theorem locE_exists_nonF (L : LocE F E) : ∃ s : E, s ∉ Set.range (algebraMap F E) := by
  by_contra h
  push Not at h
  have h1 : Module.finrank F E ≤ 1 := by
    apply finrank_le_one (1 : E)
    intro w
    obtain ⟨c, hc⟩ := h w
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩
  have := L.rank
  omega

theorem locE_exists_delta (L : LocE F E) [IsNonarchimedeanLocalField F] :
    ∃ δ : E, δ ∈ L.O ∧ δ ≠ 0 ∧ L.cj δ = -δ ∧ ∃ d : F, d ≠ 0 ∧ δ * δ = algebraMap F E d := by
  haveI := locE_nontrivial L
  haveI := L.reduced
  obtain ⟨s, hs⟩ := locE_exists_nonF L
  set δ0 := s - L.cj s with hδ0
  have hcj0 : L.cj δ0 = -δ0 := by rw [hδ0, map_sub, L.cj_cj]; ring
  have hne0 : δ0 ≠ 0 := by
    intro h0
    apply hs
    have : L.cj s = s := by rw [hδ0, sub_eq_zero] at h0; exact h0.symm
    obtain ⟨a, ha⟩ := (L.cj_fix s).mp this
    exact ⟨a, ha⟩
  have hfix : L.cj (δ0 * δ0) = δ0 * δ0 := by rw [map_mul, hcj0]; ring
  obtain ⟨d0, hd0⟩ := (L.cj_fix _).mp hfix
  have hd0ne : d0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd0
    apply hne0
    have : IsNilpotent δ0 := ⟨2, by rw [pow_two]; exact hd0.symm⟩
    exact this.eq_zero
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝒪[F]) d0
  have hb0 : (b : F) ≠ 0 := by
    intro h
    have : b = 0 := Subtype.ext h
    exact (nonZeroDivisors.ne_zero hb) this
  have hmem : (b : F) * (b : F) * d0 ∈ 𝒪[F] := by
    rw [← hab]
    have : (b : F) * (b : F) * (algebraMap 𝒪[F] F a / algebraMap 𝒪[F] F b) = (b : F) * (a : F) := by
      change (b : F) * (b : F) * ((a : F) / (b : F)) = (b : F) * (a : F)
      field_simp
    rw [this]; exact mul_mem b.2 a.2
  refine ⟨algebraMap F E (b : F) * δ0, ?_, ?_, ?_, (b : F) * (b : F) * d0, ?_, ?_⟩
  · rw [L.O_def]
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    have : (algebraMap F E (b : F) * δ0) ^ 2 = algebraMap F E ((b : F) * (b : F) * d0) := by
      rw [map_mul, map_mul, hd0]; ring
    rw [this, ← L.O_def]
    exact (locE_algMap_mem L).mpr hmem
  · intro h
    apply hne0
    have : algebraMap F E (b : F)⁻¹ * (algebraMap F E (b : F) * δ0) = δ0 := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hb0, map_one, one_mul]
    rw [← this, h, mul_zero]
  · rw [map_mul, hcj0, AlgEquiv.commutes]; ring
  · exact mul_ne_zero (mul_ne_zero hb0 hb0) hd0ne
  · rw [map_mul, map_mul, hd0]; ring

end Alg

section Alg2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem locE_decomp (L : LocE F E) [CharZero F] {δ : E} (hcj : L.cj δ = -δ) {d : F} (hd0 : d ≠ 0)
    (hd : δ * δ = algebraMap F E d) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
  have h1 : L.cj (x + L.cj x) = x + L.cj x := by rw [map_add, L.cj_cj, add_comm]
  obtain ⟨A, hA⟩ := (L.cj_fix _).mp h1
  have h2 : L.cj ((x - L.cj x) * δ) = (x - L.cj x) * δ := by
    rw [map_mul, map_sub, L.cj_cj, hcj]; ring
  obtain ⟨Bc, hB⟩ := (L.cj_fix _).mp h2
  refine ⟨A / 2, Bc / (2 * d), ?_⟩
  have h2ne : (2 : F) ≠ 0 := two_ne_zero
  have hu : IsUnit (algebraMap F E (2 * d)) := (IsUnit.mk0 _ (mul_ne_zero h2ne hd0)).map _
  apply hu.mul_left_cancel
  rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul]
  have e1 : 2 * d * (A / 2) = d * A := by field_simp
  have e2 : 2 * d * (Bc / (2 * d)) = Bc := by field_simp
  rw [e1, e2, map_mul, map_mul, hA, hB, map_ofNat]
  linear_combination (-(x - L.cj x)) * hd

structure QBasis (L : LocE F E) where
  ω : E
  hω : ω ∈ L.O
  hnot : ω ∉ Set.range (algebraMap F E)
  t : 𝒪[F]
  n : 𝒪[F]
  hcj : L.cj ω = algebraMap F E (t : F) - ω
  hn : ω * L.cj ω = algebraMap F E (n : F)
  span : ∀ x ∈ L.O, ∃ a b : 𝒪[F], x = algebraMap F E (a : F) + algebraMap F E (b : F) * ω

theorem QBasis.sq {L : LocE F E} (Q : QBasis L) :
    Q.ω * Q.ω = algebraMap F E (Q.t : F) * Q.ω - algebraMap F E (Q.n : F) := by
  have := Q.hn; rw [Q.hcj] at this; rw [← this]; ring

theorem locE_qbasis (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] : Nonempty (QBasis L) := by
  obtain ⟨δ, hδO, hδ0, hcj, d, hd0, hd⟩ := locE_exists_delta L
  set e : F := (2 * d)⁻¹ with he
  have he0 : e ≠ 0 := inv_ne_zero (mul_ne_zero two_ne_zero hd0)
  let I : Ideal 𝒪[F] :=
    { carrier := {c | ∃ a : F, algebraMap F E a + algebraMap F E ((c : F) * e) * δ ∈ L.O}
      add_mem' := by
        rintro c1 c2 ⟨a1, h1⟩ ⟨a2, h2⟩
        refine ⟨a1 + a2, ?_⟩
        have : algebraMap F E (a1 + a2) + algebraMap F E (((c1 + c2 : 𝒪[F]) : F) * e) * δ =
            (algebraMap F E a1 + algebraMap F E ((c1 : F) * e) * δ) +
              (algebraMap F E a2 + algebraMap F E ((c2 : F) * e) * δ) := by
          push_cast; simp only [map_add, add_mul, map_mul]; ring
        rw [this]; exact add_mem h1 h2
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, h⟩
        refine ⟨(c : F) * a, ?_⟩
        have : algebraMap F E ((c : F) * a) + algebraMap F E (((c • x : 𝒪[F]) : F) * e) * δ =
            algebraMap F E (c : F) * (algebraMap F E a + algebraMap F E ((x : F) * e) * δ) := by
          simp only [smul_eq_mul]; push_cast; ring
        rw [this]; exact mul_mem ((locE_algMap_mem L).mpr c.2) h }

  have hcoord : ∀ x ∈ L.O, ∀ a b : F, x = algebraMap F E a + algebraMap F E b * δ →
      ∃ c : 𝒪[F], c ∈ I ∧ (c : F) * e = b := by
    intro x hx a b hxab
    have hm : (x - L.cj x) * δ = algebraMap F E (2 * b * d) := by
      rw [hxab, map_add, map_mul, hcj, AlgEquiv.commutes, AlgEquiv.commutes, map_mul, map_mul, ← hd,
        map_ofNat]; ring
    have hmem : 2 * b * d ∈ 𝒪[F] := by
      rw [← locE_algMap_mem L, ← hm]
      exact mul_mem (sub_mem hx (locE_cj_mem L hx)) hδO
    refine ⟨⟨2 * b * d, hmem⟩, ⟨a, ?_⟩, ?_⟩
    · have : (2 * b * d) * e = b := by rw [he]; field_simp
      simp only [this]; rw [← hxab]; exact hx
    · show 2 * b * d * e = b
      rw [he]; field_simp
  set c0 := Submodule.IsPrincipal.generator I with hc0
  have hI : I = Ideal.span {c0} := (Ideal.span_singleton_generator I).symm
  obtain ⟨a0, ha0⟩ : c0 ∈ I := Submodule.IsPrincipal.generator_mem I
  have hc0ne : (c0 : F) ≠ 0 := by
    intro h
    have hc : c0 = 0 := Subtype.ext h
    rw [← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hc
    obtain ⟨c, hcI, hce⟩ := hcoord δ hδO 0 1 (by simp)
    rw [hc] at hcI
    have : c = 0 := (Submodule.mem_bot _).mp hcI
    rw [this] at hce; simp at hce
  set ω := algebraMap F E a0 + algebraMap F E ((c0 : F) * e) * δ with hωdef
  have hnot : ω ∉ Set.range (algebraMap F E) := by
    rintro ⟨f, hf⟩
    have hce : (c0 : F) * e ≠ 0 := mul_ne_zero hc0ne he0
    have hδF : δ = algebraMap F E ((f - a0) / ((c0 : F) * e)) := by
      have hu : IsUnit (algebraMap F E ((c0 : F) * e)) := (IsUnit.mk0 _ hce).map _
      apply hu.mul_left_cancel
      rw [← map_mul, mul_div_cancel₀ _ hce, map_sub, hf, hωdef]; ring
    apply hδ0
    have h2 : L.cj δ = δ := by rw [hδF, AlgEquiv.commutes]
    rw [hcj] at h2
    have : (2 : E) * δ = 0 := by linear_combination (-1 : E) * h2
    have h2u : IsUnit (2 : E) := by
      have := ((IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F E)); rwa [map_ofNat] at this
    exact (h2u.mul_right_eq_zero).mp this
  have hfixT : L.cj (ω + L.cj ω) = ω + L.cj ω := by rw [map_add, L.cj_cj, add_comm]
  obtain ⟨T, hT⟩ := (L.cj_fix _).mp hfixT
  have hfixN : L.cj (ω * L.cj ω) = ω * L.cj ω := by rw [map_mul, L.cj_cj, mul_comm]
  obtain ⟨Nn, hN⟩ := (L.cj_fix _).mp hfixN
  have hTm : T ∈ 𝒪[F] := by rw [← locE_algMap_mem L, hT]; exact add_mem ha0 (locE_cj_mem L ha0)
  have hNm : Nn ∈ 𝒪[F] := by rw [← locE_algMap_mem L, hN]; exact mul_mem ha0 (locE_cj_mem L ha0)
  refine ⟨⟨ω, ha0, hnot, ⟨T, hTm⟩, ⟨Nn, hNm⟩, ?_, hN.symm, ?_⟩⟩
  · show L.cj ω = algebraMap F E T - ω
    rw [hT]; ring
  · intro x hx
    obtain ⟨a, b, hab⟩ := locE_decomp L hcj hd0 hd x
    obtain ⟨c, hcI, hce⟩ := hcoord x hx a b hab
    rw [hI] at hcI
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hcI
    have hrest : x - algebraMap F E (m : F) * ω = algebraMap F E (a - (m : F) * a0) := by
      rw [hab, hωdef, ← hce, ← hm]; push_cast; ring
    have hmem : a - (m : F) * a0 ∈ 𝒪[F] := by
      rw [← locE_algMap_mem L, ← hrest]
      exact sub_mem hx (mul_mem ((locE_algMap_mem L).mpr m.2) ha0)
    refine ⟨⟨_, hmem⟩, m, ?_⟩
    show x = algebraMap F E (a - (m : F) * a0) + algebraMap F E (m : F) * ω
    rw [← hrest]; ring

end Alg2

section Alg3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_a_mod [IsNonarchimedeanLocalField F] (t n : 𝒪[F]) (hΔ : t * t - 4 * n ∈ 𝓂[F]) :
    ∃ a : 𝒪[F], t + 2 * a ∈ 𝓂[F] ∧ a * a - n ∈ 𝓂[F] := by
  by_cases h2 : IsUnit (2 : 𝒪[F])
  · obtain ⟨u, hu⟩ := h2
    have hmul : (u : 𝒪[F]) * ↑u⁻¹ = 1 := u.mul_inv
    refine ⟨-(t * ↑u⁻¹), ?_, ?_⟩
    · have : t + 2 * -(t * ↑u⁻¹) = 0 := by
        linear_combination (-t) * hmul + (t * ↑u⁻¹) * hu
      rw [this]; exact zero_mem _
    · have : -(t * ↑u⁻¹) * -(t * ↑u⁻¹) - n = ↑u⁻¹ * ↑u⁻¹ * (t * t - 4 * n) := by
        linear_combination (n * ((u : 𝒪[F]) * ↑u⁻¹ + 1)) * hmul +
          (-(n * ↑u⁻¹ * ↑u⁻¹ * ((u : 𝒪[F]) + 2))) * hu
      rw [this]; exact Ideal.mul_mem_left _ _ hΔ
  · have h2m : (2 : 𝒪[F]) ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr h2
    have htt : t * t ∈ 𝓂[F] := by
      have : t * t = (t * t - 4 * n) + 2 * (2 * n) := by ring
      rw [this]; exact add_mem hΔ (Ideal.mul_mem_right _ _ h2m)
    have ht : t ∈ 𝓂[F] := by
      rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem htt with h | h <;> exact h
    have h2k : (2 : 𝓀[F]) = 0 := by
      have := (IsLocalRing.residue_eq_zero_iff (2 : 𝒪[F])).mpr h2m
      rwa [map_ofNat] at this
    have hinj : Function.Injective (fun x : 𝓀[F] => x * x) := by
      intro x y hxy
      simp only at hxy
      have h1 : (x + y) * (x + y) = 0 := by
        linear_combination (-1 : 𝓀[F]) * hxy + (x * x + x * y) * h2k
      have h3 : x + y = 0 := mul_self_eq_zero.mp h1
      linear_combination h3 - y * h2k
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) (IsLocalRing.residue 𝒪[F] n)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
    refine ⟨a, add_mem ht (Ideal.mul_mem_right _ _ h2m), ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, ha]
    simp only at hr; rw [hr, sub_self]

variable (L : LocE F E) [IsNonarchimedeanLocalField F]

theorem QBasis.normE {L : LocE F E} (Q : QBasis L) (a b : F) :
    (algebraMap F E a + algebraMap F E b * Q.ω) * L.cj (algebraMap F E a + algebraMap F E b * Q.ω) =
      algebraMap F E (a * a + (Q.t : F) * a * b + (Q.n : F) * b * b) := by
  have hn := Q.hn
  rw [Q.hcj] at hn
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
  simp only [map_add, map_mul]
  linear_combination (algebraMap F E b * algebraMap F E b) * hn

theorem QBasis.disc_unit {L : LocE F E} (Q : QBasis L) : IsUnit (Q.t * Q.t - 4 * Q.n) := by
  by_contra hΔ
  have hΔm : Q.t * Q.t - 4 * Q.n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr hΔ
  obtain ⟨a, h1, h2⟩ := exists_a_mod Q.t Q.n hΔm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq] at h1 h2
  obtain ⟨p1, hp1⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨p2, hp2⟩ := Ideal.mem_span_singleton'.mp h2
  have e1 : algebraMap F E (p1 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (Q.t : F) + 2 * algebraMap F E (a : F) := by
    have e1F : (p1 : F) * (ϖ : F) = (Q.t : F) + 2 * (a : F) := by
      have := congrArg Subtype.val hp1; push_cast at this; exact this
    rw [← map_mul, e1F, map_add, map_mul, map_ofNat]
  have e2 : algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (a : F) * algebraMap F E (a : F) - algebraMap F E (Q.n : F) := by
    have e2F : (p2 : F) * (ϖ : F) = (a : F) * (a : F) - (Q.n : F) := by
      have := congrArg Subtype.val hp2; push_cast at this; exact this
    rw [← map_mul, e2F, map_sub, map_mul]
  set y := Q.ω + algebraMap F E (a : F) with hy
  have hyO : y ∈ L.O := add_mem Q.hω ((locE_algMap_mem L).mpr a.2)
  have hsq : y * y = algebraMap F E (p1 : F) * Q.ω * algebraMap F E (ϖ : F) +
      algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) := by
    rw [hy]; linear_combination Q.sq - Q.ω * e1 - e2
  have hmemO : algebraMap F E (p1 : F) * Q.ω + algebraMap F E (p2 : F) ∈ L.O :=
    add_mem (mul_mem ((locE_algMap_mem L).mpr p1.2) Q.hω) ((locE_algMap_mem L).mpr p2.2)
  have hspan : y * y ∈ Submodule.span L.O {algebraMap F E ((ϖ : 𝒪[F]) : F)} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨_, hmemO⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul, hsq]; simp only; ring
  have hyd := L.unram ϖ hϖ y hyO (by simpa using hspan)
  obtain ⟨⟨w, hw⟩, hwy⟩ := Submodule.mem_span_singleton.mp hyd
  rw [Subring.smul_def, smul_eq_mul] at hwy
  obtain ⟨a', b', hab'⟩ := Q.span w hw
  have hwy' : w * algebraMap F E (ϖ : F) = y := hwy
  rw [hab'] at hwy'
  apply Q.hnot
  have hne : (1 : F) - (ϖ : F) * (b' : F) ≠ 0 := by
    intro h
    apply hϖ.not_isUnit
    have hm : ϖ * b' = 1 := Subtype.ext (by push_cast; linear_combination -h)
    exact ⟨⟨ϖ, b', hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  refine ⟨((ϖ : F) * (a' : F) - (a : F)) / (1 - (ϖ : F) * (b' : F)), ?_⟩
  have hu : IsUnit (algebraMap F E (1 - (ϖ : F) * (b' : F))) := (IsUnit.mk0 _ hne).map _
  apply hu.mul_left_cancel
  rw [← map_mul, mul_div_cancel₀ _ hne]
  simp only [map_sub, map_mul, map_one]
  rw [hy] at hwy'
  linear_combination hwy'

theorem QBasis.trace_nondeg {L : LocE F E} (Q : QBasis L) {ϖ : 𝒪[F]} {x : E} (hx : x ∈ L.O)
    (h : ∀ c ∈ L.O, ∃ z : 𝒪[F], c * x + L.cj (c * x) = algebraMap F E ((ϖ : F) * (z : F))) :
    ∃ w ∈ L.O, x = algebraMap F E (ϖ : F) * w := by
  haveI := locE_nontrivial L
  obtain ⟨a, b, hab⟩ := Q.span x hx
  obtain ⟨z1, hz1⟩ := h 1 (one_mem _)
  obtain ⟨z2, hz2⟩ := h Q.ω Q.hω
  have hn := Q.hn
  rw [Q.hcj] at hn
  have i1 : (2 * (a : F) + (b : F) * (Q.t : F)) = (ϖ : F) * (z1 : F) := by
    apply (algebraMap F E).injective
    rw [← hz1, one_mul, hab, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_ofNat]; ring
  have i2 : ((a : F) * (Q.t : F) + (b : F) * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) =
      (ϖ : F) * (z2 : F) := by
    apply (algebraMap F E).injective
    rw [← hz2, hab, map_mul L.cj, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_sub, map_ofNat]
    linear_combination (2 * algebraMap F E (b : F)) * hn
  obtain ⟨u, hu⟩ := Q.disc_unit
  have hinv : ((u⁻¹ : (𝒪[F])ˣ) : F) * ((Q.t : F) * (Q.t : F) - 4 * (Q.n : F)) = 1 := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) (u.inv_mul)
    rw [hu] at this; push_cast at this; exact this
  set v : F := ((u⁻¹ : (𝒪[F])ˣ) : F)
  have hv : v ∈ 𝒪[F] := ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2
  set al : F := v * (((Q.t : F) * (Q.t : F) - 2 * (Q.n : F)) * (z1 : F) - (Q.t : F) * (z2 : F))
  set be : F := v * (2 * (z2 : F) - (Q.t : F) * (z1 : F))
  have hal : al ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (sub_mem (mul_mem Q.t.2 Q.t.2)
    (mul_mem (by simpa using (2 : 𝒪[F]).2) Q.n.2)) z1.2) (mul_mem Q.t.2 z2.2))
  have hbe : be ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (by simpa using (2 : 𝒪[F]).2) z2.2)
    (mul_mem Q.t.2 z1.2))
  have ha : (a : F) = (ϖ : F) * al := by
    linear_combination (v * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) * i1 + (-(v * (Q.t : F))) * i2 +
      (-(a : F)) * hinv
  have hb : (b : F) = (ϖ : F) * be := by
    linear_combination (-(v * (Q.t : F))) * i1 + (2 * v) * i2 + (-(b : F)) * hinv
  refine ⟨algebraMap F E al + algebraMap F E be * Q.ω,
    add_mem ((locE_algMap_mem L).mpr hal) (mul_mem ((locE_algMap_mem L).mpr hbe) Q.hω), ?_⟩
  rw [hab, ha, hb]; simp only [map_mul]; ring

end Alg3

end PI.SelfDualHermitianLattices.Hd
