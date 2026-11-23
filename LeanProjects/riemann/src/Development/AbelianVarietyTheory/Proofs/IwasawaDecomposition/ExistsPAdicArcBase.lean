import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.ArcBaseFactor

theorem exists_extend {S K O' : Type} [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    [CommRing O'] [Nontrivial O'] (b : S →+* O') (V : ValuationSubring K) (hS : ∀ x : S, algebraMap S K x ∈ V)
    (h : ∀ v ∈ V, ∃ a s : S, IsUnit (b s) ∧ v * algebraMap S K s = algebraMap S K a) :
    ∃ b' : V →+* O', ∀ x : S, b' ⟨algebraMap S K x, hS x⟩ = b x := by
  let M : Submonoid S := (IsUnit.submonoid O').comap b
  have hM : M ≤ nonZeroDivisors S := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    have : IsUnit (b 0) := hs
    simp at this
  have hK : ∀ s : M, IsUnit (algebraMap S K s) := fun s =>
    IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hM s.2))
  let g : Localization M →+* O' := IsLocalization.lift (M := M) (g := b) (fun s => s.2)
  let φ : Localization M →+* K := IsLocalization.lift (M := M) (g := algebraMap S K) hK
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun z hz => ?_
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
    have h1 : algebraMap S K a = 0 := by
      have := IsLocalization.lift_mk'_spec (S := Localization M) (M := M) (g := algebraMap S K) (hg := hK) a (0 : K) s
      have h2 : φ (IsLocalization.mk' (Localization M) a s) = 0 := hz
      exact (this.1 h2).trans (by simp)
    have h3 : a = 0 := (IsFractionRing.injective S K) (by simpa using h1)
    simp [h3]
  let e : Localization M ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y hxy => hφ (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
  have hV : ∀ v : V, (v : K) ∈ φ.range := by
    intro v
    obtain ⟨a, s, hs, hv⟩ := h v v.2
    have hs' : s ∈ M := hs
    refine ⟨IsLocalization.mk' (Localization M) a (⟨s, hs'⟩ : M), ?_⟩
    have := IsLocalization.lift_mk'_spec (S := Localization M) (M := M) (g := algebraMap S K) (hg := hK) a (v : K) ⟨s, hs'⟩
    exact this.2 (by simpa [mul_comm] using hv.symm)
  let ι : V →+* φ.range := RingHom.codRestrict V.subtype φ.range hV
  refine ⟨g.comp (e.symm.toRingHom.comp ι), fun x => ?_⟩
  have h5 : e.symm (ι ⟨algebraMap S K x, hS x⟩) = algebraMap S (Localization M) x := by
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    change algebraMap S K x = φ (algebraMap S (Localization M) x)
    simp [φ, IsLocalization.lift_eq]
  change g (e.symm (ι ⟨algebraMap S K x, hS x⟩)) = b x
  rw [h5]
  exact IsLocalization.lift_eq _ _

theorem exists_fraction {S K : Type} [CommRing S] [IsDedekindDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    (V : ValuationSubring K) (hS : ∀ x : S, algebraMap S K x ∈ V) (P : Ideal S) [hp : P.IsPrime] (hP : P ≠ ⊥)
    (hV : ∀ x ∈ P, V.valuation (algebraMap S K x) < 1) (v : K) (hv : v ∈ V) :
    ∃ a s : S, s ∉ P ∧ v * algebraMap S K s = algebraMap S K a := by
  have hmax : P.IsMaximal := hp.isMaximal hP
  have hle : ∀ x : S, V.valuation (algebraMap S K x) ≤ 1 := fun x => (V.valuation_le_one_iff _).2 (hS x)
  have hunit : ∀ s, s ∉ P → V.valuation (algebraMap S K s) = 1 := by
    intro s hs
    obtain ⟨t, r, hr, htr⟩ := hmax.exists_inv hs
    have h1 : V.valuation (algebraMap S K (t * s)) = 1 := by
      have h2 : t * s = 1 - r := by rw [← htr]; ring
      rw [h2, map_sub, map_one]
      exact Valuation.map_one_sub_of_lt _ (hV r hr)
    rw [map_mul, map_mul] at h1
    refine le_antisymm (hle s) ?_
    calc (1 : _) = V.valuation (algebraMap S K t) * V.valuation (algebraMap S K s) := h1.symm
      _ ≤ 1 * V.valuation (algebraMap S K s) := by gcongr; exact hle t
      _ = _ := one_mul _
  let A := Localization.AtPrime P
  haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP A
  have hinj : Function.Injective (algebraMap S A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap S K y ≠ 0 := by
    simpa using (IsFractionRing.injective S K).ne hy0
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap S A x) (algebraMap S A y)
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl c
  have hsK : algebraMap S K s ≠ 0 := by
    have : (s : S) ≠ 0 := fun h0 => s.2 (h0 ▸ P.zero_mem)
    simpa using (IsFractionRing.injective S K).ne this
  have hK1 : ∀ {a s : S}, x * a = y * s → algebraMap S K x / algebraMap S K y * algebraMap S K a = algebraMap S K s := by
    intro a s h
    have h' : algebraMap S K x * algebraMap S K a = algebraMap S K y * algebraMap S K s := by
      rw [← map_mul, ← map_mul, h]
    field_simp
    exact h'
  have hK2 : ∀ {a s : S}, y * a = x * s → algebraMap S K x / algebraMap S K y * algebraMap S K s = algebraMap S K a := by
    intro a s h
    have h' : algebraMap S K y * algebraMap S K a = algebraMap S K x * algebraMap S K s := by
      rw [← map_mul, ← map_mul, h]
    field_simp
    exact h'.symm
  rcases hc with hc | hc
  · have h1 : x * a = y * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    by_cases ha : a ∈ P
    · exfalso
      have h2 : algebraMap S K x / algebraMap S K y * algebraMap S K a = algebraMap S K s := hK1 h1
      have h3 := congrArg V.valuation h2
      rw [map_mul, hunit _ s.2] at h3
      have h4 : V.valuation (algebraMap S K x / algebraMap S K y) ≤ 1 := (V.valuation_le_one_iff _).2 hv
      have h5 := hV a ha
      have h6 : V.valuation (algebraMap S K x / algebraMap S K y) * V.valuation (algebraMap S K a) <
          1 := lt_of_le_of_lt (mul_le_of_le_one_left' h4) h5
      exact h6.ne h3
    · exact ⟨s, a, ha, hK1 h1⟩
  · have h1 : y * a = x * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    exact ⟨a, s, s.2, hK2 h1⟩

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩

theorem valuation_comap_lt_one {K : Type} [Field K] (i : K →+* ℂ) (W : ValuationSubring ℂ) (z : K)
    (hz : i z ∈ W.nonunits) : (W.comap i).valuation z < 1 := by
  by_cases h0 : z = 0
  · simp [h0]
  by_contra hn
  have hn' := not_lt.1 hn
  have h1 : (W.comap i).valuation z⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
  have h2 : z⁻¹ ∈ W.comap i := ((W.comap i).valuation_le_one_iff _).1 h1
  have h3 : (i z)⁻¹ ∈ W := by simpa using h2
  have h4 : W.valuation (i z)⁻¹ ≤ 1 := (W.valuation_le_one_iff _).2 h3
  have h5 : W.valuation (i z) < 1 := W.mem_nonunits_iff.1 hz
  rw [map_inv₀] at h4
  have h6 : W.valuation (i z) ≠ 0 := by simpa using h0
  exact absurd h5 (not_lt.2 ((inv_le_one₀ (zero_lt_iff.2 h6)).1 h4))

theorem ringOfIntegers_mem {K : Type} [Field K] (i : K →+* ℂ) (W : ValuationSubring ℂ) (x : 𝓞 K) :
    algebraMap (𝓞 K) K x ∈ W.comap i := by
  have h : IsIntegral ℤ (i (x : K)) := (RingOfIntegers.isIntegral_coe x).map i.toIntAlgHom
  have h' : IsIntegral W (i (x : K)) := h.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  change i (x : K) ∈ W
  have hy' : (y : ℂ) = i (x : K) := hy
  rw [← hy']; exact y.2

theorem exists_prime_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (h : (n : R) ∈ P) : ∃ q : ℕ, q.Prime ∧ (q : R) ∈ P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
    obtain ⟨q, hq, m, rfl⟩ := Nat.exists_prime_and_dvd h1
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨q, hq, h⟩
    · have hm : m ≠ 0 := right_ne_zero_of_mul hn
      exact ih m (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hq.one_lt) hm h

theorem exists_factor (K : Type) [Field K] [NumberField K] (i : K →+* ℂ) {O' : Type} [CommRing O'] [IsDomain O']
    [CharZero O'] (b : 𝓞 K →+* O') (ϖ : O') (hO : IsArcBase O' ϖ) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (bV : 𝓞 K →+* W.comap i)
      (b' : W.comap i →+* O'), (∀ x, ((bV x : W.comap i) : K) = (x : K)) ∧ b'.comp bV = b := by
  suffices H : ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      ∀ hS : (∀ x : 𝓞 K, algebraMap (𝓞 K) K x ∈ W.comap i),
        ∃ b' : W.comap i →+* O', ∀ x, b' ⟨algebraMap (𝓞 K) K x, hS x⟩ = b x by
    obtain ⟨p, W, hp, hW, h⟩ := H
    have hS : ∀ x : 𝓞 K, algebraMap (𝓞 K) K x ∈ W.comap i := fun x => ringOfIntegers_mem i W x
    obtain ⟨b', hb'⟩ := h hS
    exact ⟨p, W, hp, hW, RingHom.codRestrict (algebraMap (𝓞 K) K) (W.comap i) hS, b', fun x => rfl, RingHom.ext hb'⟩
  by_cases hU : ∀ n : ℕ, n ≠ 0 → IsUnit (n : O')
  · obtain ⟨W, hW⟩ := exists_place 2 Nat.prime_two
    refine ⟨2, W, Nat.prime_two, hW, fun hS => exists_extend b (W.comap i) hS fun v _ => ?_⟩
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) v
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hyK : algebraMap (𝓞 K) K y ≠ 0 := by
      simpa using (IsFractionRing.injective (𝓞 K) K).ne hy0
    refine ⟨x, y, ?_, by field_simp⟩
    have hN : ((Ideal.absNorm (Ideal.span {y}) : ℕ) : 𝓞 K) ∈ Ideal.span {y} := Ideal.absNorm_mem _
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hN
    have hN0 : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hy0
    have h1 := hU _ hN0
    rw [← map_natCast b, ← hz, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  · push_neg at hU
    obtain ⟨n, hn, hnu⟩ := hU
    rcases hO with ⟨hf, -⟩ | ⟨hd, -, -⟩
    · exfalso
      obtain ⟨c, hc⟩ := hf.mul_inv_cancel (Nat.cast_ne_zero.2 hn : (n : O') ≠ 0)
      exact hnu (IsUnit.of_mul_eq_one _ hc)
    haveI := hd
    have hnm : (n : O') ∈ maximalIdeal O' := (mem_maximalIdeal _).2 hnu
    obtain ⟨q, hq, hqm⟩ := exists_prime_mem (maximalIdeal O') n hn hnm
    let P : Ideal (𝓞 K) := (maximalIdeal O').comap b
    haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
    have hqP : (q : 𝓞 K) ∈ P := by
      change b (q : 𝓞 K) ∈ maximalIdeal O'
      simpa using hqm
    have hP : P ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.mem_bot] at hqP
      exact hq.ne_zero (by exact_mod_cast hqP)
    let f : 𝓞 K →+* ℂ := i.comp (algebraMap (𝓞 K) K)
    have hfi : Function.Injective f := i.injective.comp (IsFractionRing.injective (𝓞 K) K)
    have hne : P.map f.rangeRestrict ≠ ⊤ := by
      intro ht
      have h1 : (1 : f.range) ∈ P.map f.rangeRestrict := ht ▸ Submodule.mem_top
      obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ f.rangeRestrict_surjective).1 h1
      have hx2 : x = 1 := hfi (by simpa using congrArg Subtype.val hx1)
      exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (hx2 ▸ hx))
    obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
    have hPW : ∀ x ∈ P, f x ∈ W.nonunits := fun x hx =>
      hW ⟨f.rangeRestrict x, Ideal.mem_map_of_mem _ hx, rfl⟩
    refine ⟨q, W, hq, by simpa [f] using hPW _ hqP, fun hS => exists_extend b (W.comap i) hS fun v hv => ?_⟩
    obtain ⟨a, s, hs, hvs⟩ := exists_fraction (W.comap i) hS P hP
      (fun x hx => valuation_comap_lt_one i W _ (hPW x hx)) v hv
    refine ⟨a, s, ?_, hvs⟩
    by_contra hn'
    exact hs ((mem_maximalIdeal _).2 hn')

theorem factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O' : Type)
    [CommRing O'] [IsDomain O'] [CharZero O'] (b : 𝓞 c.F →+* O') (ϖ : O'), IsArcBase O' ϖ →
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (bV : 𝓞 c.F →+* c.V W)
      (b' : c.V W →+* O'), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) ∧ b'.comp bV = b := by
  intro E _ _ _ H l c O' _ _ _ b ϖ hO
  haveI := c.fin
  haveI : NumberField c.F := ⟨⟩
  exact exists_factor c.F c.F.val.toRingHom b ϖ hO

end GlobalTheory.ArcBaseFactor
