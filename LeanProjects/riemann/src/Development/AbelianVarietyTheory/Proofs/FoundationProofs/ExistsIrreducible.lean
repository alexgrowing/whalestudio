import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel

namespace GlobalTheory.LocSplit

theorem val_eq_of {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (g : R)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) : w.intValuation g = WithZero.exp (-1 : ℤ) := by
  have a1 := (w.intValuation_le_pow_iff_mem g 1).2 (by simpa using h1)
  have a2 := mt (w.intValuation_le_pow_iff_mem g 2).1 h2
  have h0 : w.intValuation g ≠ 0 := fun h => a2 (by rw [h]; exact zero_le)
  rw [← WithZero.exp_log h0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  rw [WithZero.exp_inj]
  push_cast at a1 a2
  omega

theorem split_prime {E : Type} [Field E] [NumberField E] {g : ℕ} (hg : g.Prime)
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hgP : (g : 𝓞 E) ∈ P) :
    (g : 𝓞 E) ∉ P ^ 2 ∧ ∀ x : 𝓞 E, ∃ m : ℤ, x - m ∈ P := by
  classical
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hle0 : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hgP
  haveI hPl : P.LiesOver (Ideal.span {(g : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle0⟩
  have hs := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(g : ℤ)}) hne
  rw [← h, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset,
    Finset.card_eq_sum_ones] at hs
  have hle : ∀ q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 E),
      1 ≤ (Ideal.span {(g : ℤ)}).ramificationIdx' q * (Ideal.span {(g : ℤ)}).inertiaDeg' q := by
    intro q hq
    rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
    haveI := hq.1
    haveI := hq.2
    exact Nat.mul_pos (Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q hne))
      (Ideal.inertiaDeg'_pos ..)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hs.symm P
    ((IsDedekindDomain.mem_primesOverFinset_iff hne _).2 ⟨hP, hPl⟩)
  have he := Nat.eq_one_of_mul_eq_one_right heq.symm
  have hf := Nat.eq_one_of_mul_eq_one_left heq.symm
  refine ⟨fun h2 => ?_, fun x => ?_⟩
  · refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hgP
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using h2
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    letI : Field (ℤ ⧸ Ideal.span {(g : ℤ)}) := Ideal.Quotient.field _
    haveI : Nontrivial (𝓞 E ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 E ⧸ P) one_ne_zero).1 hf
      (Ideal.Quotient.mk P x)
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨m, ?_⟩
    rw [← Ideal.Quotient.eq, ← hc, ← Algebra.algebraMap_eq_smul_one]
    simp

theorem int_dense {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (g : ℕ)
    (h1 : (g : R) ∈ w.asIdeal) (h2 : (g : R) ∉ w.asIdeal ^ 2)
    (h3 : ∀ x : R, ∃ m : ℤ, x - m ∈ w.asIdeal) (x : R) (n : ℕ) :
    ∃ m : ℤ, x - m ∈ w.asIdeal ^ n := by
  have hv := val_eq_of w _ h1 h2
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    have hn : (g : R) ^ n ∉ w.asIdeal ^ (n + 1) := by
      rw [← w.intValuation_le_pow_iff_mem, map_pow, hv, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
      simp
    haveI := w.isPrime
    obtain ⟨d, e, he, hde⟩ := Ideal.exists_mul_add_mem_pow_succ w.ne_bot ((g : R) ^ n) (x - m)
      (Ideal.pow_mem_pow h1 n) hn hm
    obtain ⟨c, hc⟩ := h3 d
    refine ⟨m + g ^ n * c, ?_⟩
    have : x - ((m + g ^ n * c : ℤ) : R) = (g : R) ^ n * (d - c) + e := by
      push_cast; linear_combination -hde
    rw [this]
    refine Ideal.add_mem _ ?_ he
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow h1 n) hc

theorem exists_sqrt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hs : sig ≠ AlgHom.id F E) :
    ∃ (α : 𝓞 E) (a : 𝓞 F), (α : E) ≠ 0 ∧ sig α = -α ∧ algebraMap (𝓞 F) (𝓞 E) a = α ^ 2 ∧
      ∀ y : E, ∃ u v : F, y = algebraMap F E u + algebraMap F E v * α := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  let σ : E ≃ₐ[F] E := AlgEquiv.ofBijective sig (AlgHom.bijective sig)
  have hσ : ∀ x, σ x = sig x := fun _ => rfl
  have hσ1 : σ ≠ 1 := fun h => hs (AlgHom.ext fun x => by rw [← hσ, h]; rfl)
  have hc : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ f : E ≃ₐ[F] E, f = 1 ∨ f = σ := by
    intro f
    by_contra hf
    rw [not_or] at hf
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    exact hf.2 ((hy f hf.1).trans (hy σ hσ1).symm)
  have hss : ∀ x, sig (sig x) = x := by
    intro x
    have : σ ^ 2 = 1 := by rw [← hc]; exact pow_card_eq_one'
    have h := congrArg (fun f : E ≃ₐ[F] E => f x) this
    simpa [pow_two, hσ] using h
  have hfix : ∀ x, sig x = x → ∃ u, algebraMap F E u = x := by
    intro x hx
    refine (IsGalois.mem_range_algebraMap_iff_fixed x).2 fun f => ?_
    rcases hall f with rfl | rfl
    · rfl
    · exact hx
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, sig x ≠ x := by
    by_contra hcon
    push Not at hcon
    refine hs (AlgHom.ext fun y => ?_)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
    have ha := hcon a
    have hb := hcon b
    rw [map_div₀]
    exact congrArg₂ (· / ·) ha hb
  have hint : IsIntegral ℤ ((x : E) - sig x) :=
    x.isIntegral_coe.sub (map_isIntegral_int sig x.isIntegral_coe)
  set α : E := (x : E) - sig x with hα
  have hα0 : α ≠ 0 := sub_ne_zero.2 hx.symm
  have hαs : sig α = -α := by rw [hα, map_sub, hss]; ring
  obtain ⟨a, ha⟩ := hfix (α ^ 2) (by rw [map_pow, hαs]; ring)
  have hai : IsIntegral ℤ a := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, ha]
    exact hint.pow 2
  refine ⟨⟨α, hint⟩, ⟨a, hai⟩, hα0, hαs, ?_, fun y => ?_⟩
  · ext; exact ha
  · obtain ⟨u, hu⟩ := hfix ((y + sig y) / 2) (by simp [map_div₀, hss, add_comm, map_ofNat])
    obtain ⟨v, hv⟩ := hfix ((y - sig y) / (2 * α)) (by
      rw [map_div₀, map_mul, map_sub, hss, hαs, map_ofNat]; field_simp; ring)
    refine ⟨u, v, ?_⟩
    rw [hu, hv]
    change y = _ + _ * α
    field_simp; ring

theorem exists_equiv {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    (hr : Module.finrank K A = 2) (cj : A ≃ₐ[K] A) (t : A) (β : K) (hβ : β ≠ 0)
    (ht : t ^ 2 = algebraMap K A (β ^ 2)) (hc : cj t = -t)
    (hsp : ∀ y : A, ∃ u v : K, y = algebraMap K A u + algebraMap K A v * t) :
    ∃ e : A ≃ₐ[K] K × K, ∀ x, e (cj x) = (e x).swap := by
  haveI : FiniteDimensional K A := Module.finite_of_finrank_pos (by omega)
  let gl : K × K →ₗ[K] A :=
    { toFun := fun z => algebraMap K A ((z.1 + z.2) / 2) +
        algebraMap K A ((z.1 - z.2) / (2 * β)) * t
      map_add' := fun x y => by
        have h1 : ((x + y).1 + (x + y).2) / 2 = (x.1 + x.2) / 2 + (y.1 + y.2) / 2 := by
          simp; ring
        have h2 : ((x + y).1 - (x + y).2) / (2 * β) =
            (x.1 - x.2) / (2 * β) + (y.1 - y.2) / (2 * β) := by simp; ring
        rw [h1, h2, map_add, map_add]; ring
      map_smul' := fun c x => by
        have h1 : ((c • x).1 + (c • x).2) / 2 = c * ((x.1 + x.2) / 2) := by simp; ring
        have h2 : ((c • x).1 - (c • x).2) / (2 * β) = c * ((x.1 - x.2) / (2 * β)) := by simp; ring
        rw [h1, h2, map_mul, map_mul, RingHom.id_apply, Algebra.smul_def]; ring }
  have hgl : ∀ z : K × K, gl z = algebraMap K A ((z.1 + z.2) / 2) +
        algebraMap K A ((z.1 - z.2) / (2 * β)) * t := fun _ => rfl
  let g : K × K →ₐ[K] A := AlgHom.ofLinearMap gl (by rw [hgl]; simp) (fun x y => by
    have h1 : ((x * y).1 + (x * y).2) / 2 = ((x.1 + x.2) / 2) * ((y.1 + y.2) / 2) +
      ((x.1 - x.2) / (2 * β)) * ((y.1 - y.2) / (2 * β)) * β ^ 2 := by
      simp only [Prod.fst_mul, Prod.snd_mul]; field_simp; ring
    have h2 : ((x * y).1 - (x * y).2) / (2 * β) = ((x.1 + x.2) / 2) * ((y.1 - y.2) / (2 * β)) +
      ((x.1 - x.2) / (2 * β)) * ((y.1 + y.2) / 2) := by
      simp only [Prod.fst_mul, Prod.snd_mul]; field_simp; ring
    rw [hgl, hgl, hgl, h1, h2]
    simp only [map_add, map_mul, ← ht]
    ring)
  have hsurj : Function.Surjective gl := by
    intro y
    obtain ⟨u, v, rfl⟩ := hsp y
    refine ⟨(u + v * β, u - v * β), ?_⟩
    rw [hgl]
    congr 2
    · ring
    · congr 1; field_simp; ring
  have hinj : Function.Injective gl :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).2 hsurj
  let e := AlgEquiv.ofBijective g ⟨hinj, hsurj⟩
  refine ⟨e.symm, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective x
  rw [e.symm_apply_apply, AlgEquiv.symm_apply_eq]
  change cj (gl z) = gl z.swap
  rw [hgl, hgl, map_add, map_mul, cj.commutes, cj.commutes, hc]
  have h2 : (z.swap.1 - z.swap.2) / (2 * β) = -((z.1 - z.2) / (2 * β)) := by simp; ring
  rw [h2, map_neg, Prod.fst_swap, Prod.snd_swap, add_comm z.2]
  ring

section Local
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K) (hd : DenseRange ι)
  (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)

include hd in

theorem exists_val_eq (x : K) (hx : x ≠ 0) :
    ∃ y : F, y ≠ 0 ∧ valuation K (ι y) = valuation K x := by
  have h0 : valuation K x ≠ 0 := by simpa using hx
  obtain ⟨y, hy⟩ := hd.mem_nhds ((valuation K).locally_const h0)
  refine ⟨y, ?_, hy⟩
  rintro rfl
  exact h0 (by simpa using (show valuation K (ι 0) = valuation K x from hy).symm)

include hd hv in

theorem exists_irreducible (g : F) (hg : p.valuation F g = WithZero.exp (-1 : ℤ)) :
    ∃ q : 𝒪[K], Irreducible q ∧ (q : K) = ι g := by
  have hlt : ∀ x y : F, valuation K (ι x) < valuation K (ι y) ↔
      p.valuation F x < p.valuation F y := fun x y => by rw [← not_le, ← not_le, hv]
  have h1 : valuation K (ι g) < 1 := by
    have := (hlt g 1).2 (by rw [hg, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using this
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg; exact WithZero.exp_ne_zero hg.symm
  have hI := Valuation.integer.integers (valuation K)
  refine ⟨⟨ι g, h1.le⟩, ⟨fun hu => h1.ne (hI.one_of_isUnit hu), fun a b hab => ?_⟩, rfl⟩
  have hab' : ι g = (a : K) * b := congrArg Subtype.val hab
  have hne : (a : K) * b ≠ 0 := by rw [← hab']; simpa using hg0
  by_contra hcon
  rw [not_or] at hcon
  have key : ∀ c : 𝒪[K], (c : K) ≠ 0 → ¬ IsUnit c → ∃ y : F, valuation K (ι y) = valuation K c ∧
      p.valuation F y ≤ WithZero.exp (-1 : ℤ) := by
    intro c hc hu
    obtain ⟨y, hy0, hy⟩ := exists_val_eq ι hd c hc
    refine ⟨y, hy, ?_⟩
    have h2 : valuation K (c : K) < 1 :=
      lt_of_le_of_ne c.2 fun h => hu (hI.isUnit_of_one' h)
    have h3 : p.valuation F y < 1 := by
      have := (hlt y 1).1 (by simpa [hy] using h2)
      simpa using this
    have h0 : p.valuation F y ≠ 0 := by simpa using hy0
    rw [← WithZero.exp_log h0] at h3 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
    rw [WithZero.exp_le_exp]
    omega
  obtain ⟨y, hy, hy1⟩ := key a (left_ne_zero_of_mul hne) hcon.1
  obtain ⟨z, hz, hz1⟩ := key b (right_ne_zero_of_mul hne) hcon.2
  have h4 := (hv g (y * z)).1 (by rw [hab', map_mul, map_mul, map_mul, hy, hz])
  rw [map_mul, hg] at h4
  have h5 := h4.trans (mul_le_mul' hy1 hz1)
  rw [← WithZero.exp_add, WithZero.exp_le_exp] at h5
  omega

include hd hv in

theorem exists_sq_eq (a : 𝓞 F) (ha : ∀ n : ℕ, ∃ m : ℤ, a - (m : 𝓞 F) ^ 2 ∈ p.asIdeal ^ n) :
    ∃ β : K, β ^ 2 = ι a := by
  haveI : T2Space K := IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx =>
    ⟨{y | valuation K y < valuation K x},
      (IsValuativeTopology.hasBasis_nhds_zero' K).mem_of_mem (by simpa using hx), by simp⟩
  have hc : IsCompact (Set.range fun x : 𝒪[K] => (x : K) ^ 2) :=
    isCompact_range (by fun_prop)
  have hm : ι a ∈ closure (Set.range fun x : 𝒪[K] => (x : K) ^ 2) := by
    rw [mem_closure_iff_nhds_basis (IsValuativeTopology.hasBasis_nhds' (ι a))]
    intro γ hγ
    obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
    obtain ⟨y, hy0, hy⟩ := exists_val_eq ι hd z (by simpa using hγ)
    have h0 : p.valuation F y ≠ 0 := by simpa using hy0
    obtain ⟨m, hm⟩ := ha ((WithZero.log (p.valuation F y)).natAbs + 1)
    refine ⟨_, ⟨(m : 𝒪[K]), rfl⟩, ?_⟩
    rw [← p.intValuation_le_pow_iff_mem, ← p.valuation_of_algebraMap (K := F)] at hm
    have h1 : p.valuation F (algebraMap (𝓞 F) F (a - (m : 𝓞 F) ^ 2)) < p.valuation F y := by
      refine lt_of_le_of_lt hm ?_
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_lt_exp]
      omega
    rw [← not_le, ← hv, not_le, hy] at h1
    rw [Set.mem_setOf_eq, Valuation.map_sub_swap]
    simpa using h1
  rw [hc.isClosed.closure_eq] at hm
  obtain ⟨β, hβ⟩ := hm
  exact ⟨β, hβ⟩

end Local

theorem nonempty_splitAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (sig : E →ₐ[F] E), Module.finrank F E = 2 → sig ≠ AlgHom.id F E →
    ∀ (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p),
    ((Ideal.span {(resChar p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E →
    Nonempty (SplitAt L.Fp L.Ep L.cj (resChar p)) := by
  intro F E _ _ _ _ _ sig h2 hs p L h
  haveI := L.lf
  haveI := L.char0
  have hg : (resChar p).Prime := L.ellPrime.out
  have hv : ∀ x y : F, valuation L.Fp (L.ιF x) ≤ valuation L.Fp (L.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← L.val, Valuation.Compatible.vle_iff_le (v := valuation L.Fp)]
  have hgp : (resChar p : 𝓞 F) ∈ p.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  haveI := p.isPrime
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver (𝓞 E)))
  let w : HeightOneSpectrum (𝓞 E) := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  haveI : w.asIdeal.LiesOver p.asIdeal := hPl
  have hgP : (resChar p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P p.asIdeal (resChar p : 𝓞 F)).1 hgp
  obtain ⟨hP2, hP3⟩ := split_prime hg h P hgP
  have hw := val_eq_of w _ hgP hP2
  have hrel := p.intValuation_liesOver w
  have hp2 : (resChar p : 𝓞 F) ∉ p.asIdeal ^ 2 := fun h2 => hP2 (by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this)
  have hpv := val_eq_of p _ hgp hp2
  have he : p.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    have := hrel (resChar p)
    rw [map_natCast (algebraMap (𝓞 F) (𝓞 E)), hw, hpv, ← WithZero.exp_nsmul, WithZero.exp_inj] at this
    simpa using this
  simp only [he, pow_one] at hrel
  obtain ⟨q, hq, hq'⟩ := exists_irreducible p L.ιF L.dense hv (resChar p) (by
    rw [← hpv, ← p.valuation_of_algebraMap (K := F)]; simp)
  obtain ⟨α, a, hα0, hαs, ha, hsp⟩ := exists_sqrt F E sig h2 hs
  obtain ⟨β, hβ⟩ := exists_sq_eq p L.ιF L.dense hv a fun n => by
    obtain ⟨m, hm⟩ := int_dense w _ hgP hP2 hP3 α n
    refine ⟨m, ?_⟩
    rw [← p.intValuation_le_pow_iff_mem, hrel, w.intValuation_le_pow_iff_mem, map_sub, ha,
      map_pow, map_intCast, sq_sub_sq]
    exact Ideal.mul_mem_left _ _ hm
  have ha' : algebraMap F E a = (α : E) ^ 2 := congrArg (fun x : 𝓞 E => (x : E)) ha
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have : (a : F) = 0 := by simpa using hβ.symm
    rw [this, map_zero] at ha'
    exact pow_ne_zero 2 hα0 ha'.symm
  obtain ⟨e, he⟩ := exists_equiv L.rank L.cj (L.ιE α) β hβ0
    (by rw [hβ, ← L.compat, ha', map_pow]) (by rw [L.cj_ιE, hαs, map_neg]) (fun y => by
      have hy : y ∈ Submodule.span L.Fp (Set.range L.ιE) := by rw [L.span]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨u, v, rfl⟩ := hsp x
        exact ⟨L.ιF u, L.ιF v, by rw [map_add, map_mul, L.compat, L.compat]⟩
      | zero => exact ⟨0, 0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨u, v, rfl⟩ := hx
        obtain ⟨u', v', rfl⟩ := hy
        exact ⟨u + u', v + v', by rw [map_add, map_add]; ring⟩
      | smul c x _ hx =>
        obtain ⟨u, v, rfl⟩ := hx
        exact ⟨c * u, c * v, by rw [map_mul, map_mul, Algebra.smul_def]; ring⟩)
  exact ⟨⟨e, he, q, hq, by rw [hq', map_natCast]⟩⟩

end GlobalTheory.LocSplit
