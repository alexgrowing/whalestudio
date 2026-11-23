import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open ValuativeRel

namespace PI.IntegralDiscriminantMembership

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem algebraMap_inj {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) : Function.Injective (algebraMap F E) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [M.L.rank]; norm_num)
  exact (algebraMap F E).injective

theorem mem_integer_of_isIntegral {F : Type} [Field F] [ValuativeRel F] {s : F}
    (hs : IsIntegral 𝒪[F] s) : s ∈ 𝒪[F] := by
  have h := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral hs
  first
    | exact h
    | simpa using h
    | (obtain ⟨y, hy⟩ := h; rw [← hy]; exact y.2)

theorem mem_integer_of_isIntegral_map {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {s : F}
    (hs : IsIntegral 𝒪[F] (algebraMap F E s)) : s ∈ 𝒪[F] := by
  apply mem_integer_of_isIntegral
  exact (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F]) (algebraMap_inj M)).mp hs

theorem cj_alg {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (a : F) : M.L.cj (algebraMap F E a) = algebraMap F E a := M.L.cj.commutes a

theorem mem_O_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (x : E) :
    x ∈ M.L.O ↔ (∃ a : 𝒪[F], algebraMap F E a = x + M.L.cj x) ∧
      ∃ b : 𝒪[F], algebraMap F E b = x * M.L.cj x := by
  constructor
  · intro hx
    have hcx : M.L.cj x ∈ M.L.O := by
      rw [M.L.O_def] at hx ⊢
      exact hx.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
    have ht : x + M.L.cj x ∈ M.L.O := M.L.O.add_mem hx hcx
    have hn : x * M.L.cj x ∈ M.L.O := M.L.O.mul_mem hx hcx
    obtain ⟨t, htd⟩ := (M.L.cj_fix (x + M.L.cj x)).mp (by rw [map_add, M.L.cj_cj, add_comm])
    obtain ⟨n, hnd⟩ := (M.L.cj_fix (x * M.L.cj x)).mp (by rw [map_mul, M.L.cj_cj, mul_comm])
    refine ⟨⟨⟨t, mem_integer_of_isIntegral_map M ((M.L.O_def _).mp (htd ▸ ht))⟩, htd⟩,
      ⟨⟨n, mem_integer_of_isIntegral_map M ((M.L.O_def _).mp (hnd ▸ hn))⟩, hnd⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [M.L.O_def]
    have hdeg : (Polynomial.C b - Polynomial.C a * Polynomial.X : Polynomial 𝒪[F]).degree < 2 :=
      lt_of_le_of_lt (by compute_degree) (by norm_num)
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C b - Polynomial.C a * Polynomial.X),
      Polynomial.monic_X_pow_add hdeg, ?_⟩
    have h1 : algebraMap 𝒪[F] E a = x + M.L.cj x := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
      exact ha
    have h2 : algebraMap 𝒪[F] E b = x * M.L.cj x := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
      exact hb
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_sub, Polynomial.eval₂_C,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, h1, h2]
    ring

theorem alg_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {a : F} : algebraMap F E a ∈ M.L.O ↔ a ∈ 𝒪[F] := by
  rw [M.L.O_def]
  constructor
  · exact mem_integer_of_isIntegral_map M
  · intro ha
    have h : algebraMap F E a = algebraMap 𝒪[F] E ⟨a, ha⟩ := IsScalarTower.algebraMap_apply 𝒪[F] F E ⟨a, ha⟩
    rw [h]
    exact isIntegral_algebraMap

theorem exists_not_mem_range {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) : ∃ y : E, y ∉ Set.range (algebraMap F E) := by
  by_contra hc
  push_neg at hc
  have hs : Function.Surjective (Algebra.linearMap F E) := fun y => hc y
  have h := LinearMap.finrank_range_le (Algebra.linearMap F E)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self, M.L.rank] at h
  norm_num at h

theorem exists_mul_mem_integer {F : Type} [Field F] [ValuativeRel F] (s : F) :
    ∃ c : F, c ∈ 𝒪[F] ∧ c ≠ 0 ∧ c * s ∈ 𝒪[F] := by
  by_cases hs : s ∈ 𝒪[F]
  · exact ⟨1, one_mem _, one_ne_zero, by simpa using hs⟩
  · have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs (zero_mem _)
    refine ⟨s⁻¹, ?_, inv_ne_zero hs0, by rw [inv_mul_cancel₀ hs0]; exact one_mem _⟩
    rw [Valuation.mem_integer_iff] at hs ⊢
    rw [map_inv₀]
    push_neg at hs
    exact inv_le_one_of_one_le₀ hs.le

theorem exists_omega0 {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) :
    ∃ w : E, w ∈ M.L.O ∧ w ∉ Set.range (algebraMap F E) := by
  obtain ⟨y, hy⟩ := exists_not_mem_range M
  obtain ⟨t, ht⟩ := (M.L.cj_fix (y + M.L.cj y)).mp (by rw [map_add, M.L.cj_cj, add_comm])
  obtain ⟨n, hn⟩ := (M.L.cj_fix (y * M.L.cj y)).mp (by rw [map_mul, M.L.cj_cj, mul_comm])
  obtain ⟨c1, hc1, hc10, hc1t⟩ := exists_mul_mem_integer t
  obtain ⟨c2, hc2, hc20, hc2n⟩ := exists_mul_mem_integer n
  refine ⟨algebraMap F E (c1 * c2) * y, ?_, ?_⟩
  · rw [mem_O_iff]
    refine ⟨⟨⟨c1 * c2 * t, ?_⟩, ?_⟩, ⟨⟨(c1 * c2) ^ 2 * n, ?_⟩, ?_⟩⟩
    · have e : c1 * c2 * t = c2 * (c1 * t) := by ring
      rw [e]
      exact mul_mem hc2 hc1t
    · simp only [map_mul, ht, cj_alg M]
      ring
    · have e : (c1 * c2) ^ 2 * n = c1 ^ 2 * c2 * (c2 * n) := by ring
      rw [e]
      exact mul_mem (mul_mem (pow_mem hc1 2) hc2) hc2n
    · simp only [map_mul, map_pow, hn, cj_alg M]
      ring
  · rintro ⟨a, ha⟩
    apply hy
    refine ⟨a / (c1 * c2), ?_⟩
    have hc : c1 * c2 ≠ 0 := mul_ne_zero hc10 hc20
    rw [div_eq_inv_mul, map_mul, ha, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]

theorem disc_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {w : E} (hwn : w ∉ Set.range (algebraMap F E)) {t n0 : F}
    (ht : algebraMap F E t = w + M.L.cj w) (hn : algebraMap F E n0 = w * M.L.cj w) : t ^ 2 - 4 * n0 ≠ 0 := by
  intro h0
  apply hwn
  have hsq : (w - M.L.cj w) ^ 2 = 0 := by
    have h1 : algebraMap F E (t ^ 2 - 4 * n0) = (w - M.L.cj w) ^ 2 := by
      rw [map_sub, map_mul, map_pow, ht, hn, map_ofNat]
      ring
    rw [← h1, h0, map_zero]
  haveI := M.L.reduced
  have hz : w - M.L.cj w = 0 := IsReduced.eq_zero _ ⟨2, hsq⟩
  have hfix : M.L.cj w = w := (sub_eq_zero.mp hz).symm
  obtain ⟨a, ha⟩ := (M.L.cj_fix w).mp hfix
  exact ⟨a, ha⟩

theorem coords_unique {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {w : E} (hwn : w ∉ Set.range (algebraMap F E)) {a b a' b' : F}
    (h : algebraMap F E a + algebraMap F E b * w = algebraMap F E a' + algebraMap F E b' * w) :
    a = a' ∧ b = b' := by
  have h1 : algebraMap F E (b - b') * w = algebraMap F E (a' - a) := by
    rw [map_sub, map_sub, sub_mul]
    linear_combination h
  by_cases hb : b = b'
  · subst hb
    exact ⟨algebraMap_inj M (add_right_cancel h), rfl⟩
  · exfalso
    apply hwn
    refine ⟨(b - b')⁻¹ * (a' - a), ?_⟩
    rw [map_mul, ← h1, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hb), map_one, one_mul]

theorem coords_exist {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {w : E} (hwn : w ∉ Set.range (algebraMap F E)) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * w := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  have hli : LinearIndependent F ![(1 : E), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : algebraMap F E s + algebraMap F E t * w = algebraMap F E 0 + algebraMap F E 0 * w := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      simpa using hst
    exact coords_unique M hwn h2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [M.L.rank]; simp)
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), w]) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

theorem mem_of_sq_mem {F : Type} [Field F] [ValuativeRel F] {y : F} (h : y ^ 2 ∈ 𝒪[F]) : y ∈ 𝒪[F] := by
  rw [Valuation.mem_integer_iff] at h ⊢
  rw [map_pow] at h
  by_contra hy
  push_neg at hy
  have h2 : 1 < (ValuativeRel.valuation F) y ^ 2 := one_lt_pow₀ hy two_ne_zero
  exact absurd h (not_le.mpr h2)

theorem four_mem {F : Type} [Field F] [ValuativeRel F] : (4 : F) ∈ 𝒪[F] := by
  have h := natCast_mem (𝒪[F]) 4
  simpa using h

theorem bD_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {w : E} {t n0 : F} (ht : algebraMap F E t = w + M.L.cj w)
    (hn : algebraMap F E n0 = w * M.L.cj w) (htO : t ∈ 𝒪[F]) (hnO : n0 ∈ 𝒪[F]) {a b : F}
    (hx : algebraMap F E a + algebraMap F E b * w ∈ M.L.O) : b * (t ^ 2 - 4 * n0) ∈ 𝒪[F] := by
  obtain ⟨⟨T, hT⟩, ⟨N, hN⟩⟩ := (mem_O_iff M _).mp hx
  set x := algebraMap F E a + algebraMap F E b * w with hxdef
  have hcx : M.L.cj x = algebraMap F E a + algebraMap F E b * M.L.cj w := by
    rw [hxdef, map_add, map_mul, cj_alg M, cj_alg M]
  have hE : algebraMap F E ((T : F) ^ 2 - 4 * (N : F)) = algebraMap F E (b ^ 2 * (t ^ 2 - 4 * n0)) := by
    have h1 : algebraMap F E ((T : F) ^ 2 - 4 * (N : F)) = (x - M.L.cj x) ^ 2 := by
      rw [map_sub, map_mul, map_pow, hT, hN, map_ofNat]
      ring
    have h2 : algebraMap F E (b ^ 2 * (t ^ 2 - 4 * n0)) = (x - M.L.cj x) ^ 2 := by
      rw [map_mul, map_sub, map_mul, map_pow, map_pow, ht, hn, map_ofNat, hcx, hxdef]
      ring
    rw [h1, h2]
  have hb2 : b ^ 2 * (t ^ 2 - 4 * n0) ∈ 𝒪[F] := by
    rw [← algebraMap_inj M hE]
    exact sub_mem (pow_mem T.2 2) (mul_mem four_mem N.2)
  have hD : t ^ 2 - 4 * n0 ∈ 𝒪[F] := sub_mem (pow_mem htO 2) (mul_mem four_mem hnO)
  apply mem_of_sq_mem
  have e : (b * (t ^ 2 - 4 * n0)) ^ 2 = (b ^ 2 * (t ^ 2 - 4 * n0)) * (t ^ 2 - 4 * n0) := by ring
  rw [e]
  exact mul_mem hb2 hD

theorem oBasis {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (hOK : M.OK) :
    ∃ ω ∈ M.L.O, ω ∉ Set.range (algebraMap F E) ∧
      ∀ x ∈ M.L.O, ∃! p : 𝒪[F] × 𝒪[F], x = algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * ω := by
  have := hOK.loc
  obtain ⟨w, hw, hwn⟩ := exists_omega0 M
  obtain ⟨⟨t, ht⟩, ⟨n0, hn⟩⟩ := (mem_O_iff M w).mp hw
  have hD0 : (t : F) ^ 2 - 4 * n0 ≠ 0 := disc_ne_zero M hwn ht hn
  have hDO : (t : F) ^ 2 - 4 * n0 ∈ 𝒪[F] := sub_mem (pow_mem t.2 2) (mul_mem four_mem n0.2)
  let D : F := (t : F) ^ 2 - 4 * n0
  let J : Ideal 𝒪[F] :=
    { carrier := {c | ∃ a : F, algebraMap F E a + algebraMap F E ((c : F) / D) * w ∈ M.L.O}
      add_mem' := by
        rintro c1 c2 ⟨a1, h1⟩ ⟨a2, h2⟩
        refine ⟨a1 + a2, ?_⟩
        convert add_mem h1 h2 using 1
        simp only [Subring.coe_add, add_div, map_add]
        ring
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r c ⟨a, h⟩
        refine ⟨r * a, ?_⟩
        convert mul_mem ((alg_mem_O M).mpr r.2) h using 1
        simp only [smul_eq_mul, Subring.coe_mul, mul_div_assoc, map_mul]
        ring }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  have hDJ : (⟨D, hDO⟩ : 𝒪[F]) ∈ J := ⟨0, by
    show algebraMap F E 0 + algebraMap F E (D / D) * w ∈ M.L.O
    rw [div_self hD0, map_zero, map_one, zero_add, one_mul]; exact hw⟩
  have hgJ : g ∈ J := hg ▸ Submodule.mem_span_singleton_self g
  have hg0 : (g : F) ≠ 0 := by
    intro h0
    have h1 := hDJ
    rw [hg, Ideal.mem_span_singleton'] at h1
    obtain ⟨r, hr⟩ := h1
    have h2 := congrArg Subtype.val hr
    rw [Subring.coe_mul, h0, mul_zero] at h2
    exact hD0 h2.symm
  obtain ⟨ag, hag⟩ := hgJ
  refine ⟨_, hag, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have h1 := coords_unique M hwn (a := c) (b := 0) (a' := ag) (b' := (g : F) / D)
      (by rw [map_zero, zero_mul, add_zero, hc])
    rcases div_eq_zero_iff.mp h1.2.symm with h | h
    · exact hg0 h
    · exact hD0 h
  · intro x hx
    obtain ⟨a, b, rfl⟩ := coords_exist M hwn x
    have hbD : b * D ∈ 𝒪[F] := bD_mem M ht hn t.2 n0.2 hx
    have hcJ : (⟨b * D, hbD⟩ : 𝒪[F]) ∈ J := ⟨a, by
      show algebraMap F E a + algebraMap F E (b * D / D) * w ∈ M.L.O
      rwa [mul_div_cancel_right₀ b hD0]⟩
    rw [hg, Ideal.mem_span_singleton'] at hcJ
    obtain ⟨r, hr⟩ := hcJ
    have hr' : (r : F) * g = b * D := congrArg Subtype.val hr
    have hb : b = r * ((g : F) / D) := by
      rw [← mul_div_assoc, hr', mul_div_cancel_right₀ b hD0]
    have hp1 : a - r * ag ∈ 𝒪[F] := by
      have hmem := sub_mem hx (mul_mem ((alg_mem_O M).mpr r.2) hag)
      have e : algebraMap F E a + algebraMap F E b * w - algebraMap F E (r : F) *
          (algebraMap F E ag + algebraMap F E ((g : F) / D) * w) = algebraMap F E (a - r * ag) := by
        rw [hb]; simp only [map_sub, map_mul]; ring
      rw [e] at hmem
      exact (alg_mem_O M).mp hmem
    refine ⟨(⟨a - r * ag, hp1⟩, r), ?_, ?_⟩
    · show algebraMap F E a + algebraMap F E b * w = algebraMap F E (a - r * ag) +
        algebraMap F E (r : F) * (algebraMap F E ag + algebraMap F E ((g : F) / D) * w)
      rw [hb]; simp only [map_sub, map_mul]; ring
    · rintro ⟨p1, p2⟩ hp
      have e : algebraMap F E (p1 : F) + algebraMap F E (p2 : F) *
          (algebraMap F E ag + algebraMap F E ((g : F) / D) * w) =
          algebraMap F E ((p1 : F) + p2 * ag) + algebraMap F E ((p2 : F) * ((g : F) / D)) * w := by
        simp only [map_add, map_mul]; ring
      have hp' := hp
      simp only at hp'
      rw [e] at hp'
      obtain ⟨h1, h2⟩ := coords_unique M hwn hp'
      rw [hb] at h2
      have hp2 : (p2 : F) = r := (mul_right_cancel₀ (div_ne_zero hg0 hD0) h2).symm
      have hp1' : (p1 : F) = a - r * ag := by rw [h1, hp2]; ring
      exact Prod.ext (Subtype.ext hp1') (Subtype.ext hp2)

theorem card_quot_pi {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (hOK : M.OK) (π : 𝒪[F]) (hπ : Irreducible π) :
    Nat.card (M.L.O ⧸ Ideal.span {(⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ : M.L.O)}) = qF F ^ 2 := by
  have := hOK.loc
  obtain ⟨ω, hω, -, hb⟩ := oBasis M hOK
  set πO : M.L.O := ⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ with hπO
  let ψ : 𝒪[F] × 𝒪[F] →+ M.L.O :=
    { toFun := fun p => ⟨algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * ω,
        add_mem ((alg_mem_O M).mpr p.1.2) (mul_mem ((alg_mem_O M).mpr p.2.2) hω)⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by
        intro p p'
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, map_add]
        ring }
  have hψ : ∀ p, (ψ p : E) = algebraMap F E (p.1 : F) + algebraMap F E (p.2 : F) * ω := fun p => rfl
  have hinj : Function.Injective ψ := by
    intro p p' h
    have h' := congrArg Subtype.val h
    obtain ⟨q, -, hq⟩ := hb _ (ψ p).2
    exact (hq p (hψ p)).trans (hq p' (h'.trans (hψ p'))).symm
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hp, -⟩ := hb x hx
    exact ⟨p, Subtype.ext (hp.symm)⟩
  have hmul : ∀ q : 𝒪[F] × 𝒪[F], ψ q * πO = ψ (q.1 * π, q.2 * π) := by
    intro q
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hψ, hψ, hπO]
    simp only [MulMemClass.coe_mul, map_mul]
    ring
  let e := AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  let res : 𝒪[F] →+ 𝓀[F] := (IsLocalRing.residue 𝒪[F]).toAddMonoidHom
  let Φ : M.L.O →+ 𝓀[F] × 𝓀[F] := (res.prodMap res).comp e.symm.toAddMonoidHom
  have hΦ : ∀ p, Φ (ψ p) = (res p.1, res p.2) := by
    intro p
    have : e.symm (ψ p) = p := e.symm_apply_apply p
    simp only [Φ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, this]
    rfl
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hres : ∀ c : 𝒪[F], res c = 0 ↔ ∃ d, d * π = c := by
    intro c
    show IsLocalRing.residue _ c = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton']
  have hker : Φ.ker = (Ideal.span {πO}).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    obtain ⟨p, rfl⟩ := hsurj x
    rw [hΦ, Prod.mk_eq_zero, hres, hres]
    constructor
    · rintro ⟨⟨d1, hd1⟩, ⟨d2, hd2⟩⟩
      refine ⟨ψ (d1, d2), ?_⟩
      rw [hmul]
      simp only [hd1, hd2]
    · rintro ⟨y, hy⟩
      obtain ⟨q, rfl⟩ := hsurj y
      rw [hmul] at hy
      have := hinj hy
      exact ⟨⟨q.1, congrArg Prod.fst this⟩, ⟨q.2, congrArg Prod.snd this⟩⟩
  have hΦs : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨c1, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c2, rfl⟩ := IsLocalRing.residue_surjective b
    exact ⟨ψ (c1, c2), hΦ _⟩
  calc Nat.card (M.L.O ⧸ Ideal.span {πO}) = (Ideal.span {πO}).toAddSubgroup.index := rfl
    _ = Φ.ker.index := by rw [hker]
    _ = Nat.card Φ.range := AddSubgroup.index_ker Φ
    _ = Nat.card (𝓀[F] × 𝓀[F]) := by
      rw [AddMonoidHom.range_eq_top.mpr hΦs]
      exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
    _ = qF F ^ 2 := by rw [Nat.card_prod, sq]; rfl

end PI.IntegralDiscriminantMembership

end
