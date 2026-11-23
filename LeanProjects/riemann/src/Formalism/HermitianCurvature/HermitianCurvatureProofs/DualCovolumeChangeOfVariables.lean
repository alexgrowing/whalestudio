import Formalism.HermitianCurvature.StatementJ
import Lemmata.FiberEquations.FiberEq

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P.Jx3

open InfinitePlace in

theorem trace_places (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding x).re := by
  first | exact Bl.FiberEquations.goal1 .. | (apply Bl.FiberEquations.goal1 <;> assumption) | (intros; apply Bl.FiberEquations.goal1 <;> assumption)

theorem t_TracePairing : TracePairing := by
  intro E _ _ _ g c l t hg hc
  have hg' : (g : ℝ) ≠ 0 := by positivity
  rw [trace_places, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dm, semb, cemb, AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply, LinearMap.id_apply, Complex.inner,
    PiLp.smul_apply, map_mul, map_div₀, map_natCast, Complex.conj_ofReal, Complex.conj_conj,
    Complex.real_smul]
  have : (↑c * w.embedding t) * (((2 / ((g : ℝ) * c) : ℝ) : ℂ) * w.embedding l) =
      ((2 / (g : ℝ) : ℝ) : ℂ) * (w.embedding l * w.embedding t) := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    push_cast; field_simp
  have h2 : w.embedding l * w.embedding t / (g : ℂ) =
      ((1 / (g : ℝ) : ℝ) : ℂ) * (w.embedding l * w.embedding t) := by
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    push_cast; field_simp
  rw [this, h2, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem semb_apply (E : Type) [Field E] [NumberField E] (c : ℝ) (t : E) : semb E c t = c • cemb E t := by
  simp [semb]

theorem t_BlockFrame : BlockFrame := by
  intro hL hE E _ _ _ hU g ν s hg
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, h11, h12⟩ := hL E hU g ν s hg
  obtain ⟨a, b, c⟩ := hE E (S6.perLat E g ν s) (S6.rd E ^ (-ν)) h10 h11
  exact ⟨a, b, c.trans h12⟩

open InfinitePlace in
theorem orth_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : CV E)
    (h : ∀ t : E, inner ℝ z (cemb E t) = 0) : z = 0 := by
  classical
  let v : InfinitePlace E × Bool → (E →* ℂ) := fun p =>
    if p.2 then (p.1.embedding : E →* ℂ) else ((ComplexEmbedding.conjugate p.1.embedding : E →+* ℂ) : E →* ℂ)
  have hne : ∀ w : InfinitePlace E, w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro w
    have hw : ¬ IsReal w := not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
  have hmk : ∀ p, ∃ φ : E →+* ℂ, (φ : E →* ℂ) = v p ∧ InfinitePlace.mk φ = p.1 ∧
      (φ = if p.2 then p.1.embedding else ComplexEmbedding.conjugate p.1.embedding) := by
    rintro ⟨w, b⟩
    cases b
    · exact ⟨ComplexEmbedding.conjugate w.embedding, by simp [v], by simp, by simp⟩
    · exact ⟨w.embedding, by simp [v], by simp, by simp⟩
  have hinj : Function.Injective v := by
    intro p q hpq
    obtain ⟨φ, h1, h2, h3⟩ := hmk p
    obtain ⟨φ', h1', h2', h3'⟩ := hmk q
    have hφ : φ = φ' := by
      apply RingHom.coe_monoidHom_injective
      show (φ : E →* ℂ) = (φ' : E →* ℂ)
      rw [h1, h1', hpq]
    have hw : p.1 = q.1 := by rw [← h2, ← h2', hφ]
    obtain ⟨w, b⟩ := p
    obtain ⟨w', b'⟩ := q
    simp only at hw
    subst hw
    rw [h3, h3'] at hφ
    cases b <;> cases b' <;> simp_all
    · exact absurd hφ.symm (hne w)
  have hli := (linearIndependent_monoidHom E ℂ).comp v hinj
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun p => if p.2 then conj (z p.1) else z p.1) (by
    ext t
    have ht := h t
    rw [PiLp.inner_apply] at ht
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_apply, Pi.smul_apply,
      Function.comp, v, smul_eq_mul, Pi.zero_apply]
    simp only [if_true, Bool.false_eq_true, if_false]
    have h2 : ∀ w : InfinitePlace E, conj (z w) * w.embedding t + z w * conj (w.embedding t) =
        ((2 * inner ℝ (z w) (cemb E t w) : ℝ) : ℂ) := by
      intro w
      have : cemb E t w = w.embedding t := rfl
      rw [this, Complex.inner]
      have h3 : z w * conj (w.embedding t) = conj (conj (z w) * w.embedding t) := by simp
      rw [h3, Complex.add_conj]
      congr 3
      ring
    have h4 : ∀ w : InfinitePlace E,
        conj (z w) * (w.embedding : E →* ℂ) t + z w * ((ComplexEmbedding.conjugate w.embedding : E →+* ℂ) : E →* ℂ) t
          = ((2 * inner ℝ (z w) (cemb E t w) : ℝ) : ℂ) := fun w => by
      rw [← h2 w]; rfl
    rw [Finset.sum_congr rfl (fun w _ => h4 w), ← Complex.ofReal_sum, ← Finset.mul_sum, ht]
    simp)
  ext w
  simpa using this (w, false)

theorem t_TraceDual : TraceDual := by
  have hT := t_TracePairing
  intro E _ _ _ L g c hg hc hL μ
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hμ

    let R : E →ₗ[ℚ] ℝ := ((innerₗ (CV E) μ).toAddMonoidHom.comp (semb E c)).toRatLinearMap
    have hR : ∀ x, R x = inner ℝ μ (semb E c x) := fun x => rfl
    let b := Module.finBasis ℚ E
    have hq : ∀ j, ∃ q : ℚ, R (b j) = (q : ℝ) := by
      intro j
      obtain ⟨n, hn, hnL⟩ := hL (b j)
      have h1 := hμ (semb E c ((n : E) * b j)) (Submodule.mem_map_of_mem (f := (semb E c).toIntLinearMap) hnL)
      obtain ⟨m, hm⟩ := Submodule.mem_one.mp h1
      have h2 : R ((n : E) * b j) = (n : ℝ) * R (b j) := by
        have : (n : E) * b j = (n : ℚ) • b j := by rw [Algebra.smul_def]; simp
        rw [this, map_smul]; simp [Rat.smul_def]
      refine ⟨(m : ℚ) / n, ?_⟩
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have h3 : (n : ℝ) * R (b j) = (m : ℝ) := by
        rw [← h2, hR]; exact hm.symm.trans (by simp)
      push_cast
      field_simp
      linarith
    choose q hq using hq
    let lam : E →ₗ[ℚ] ℚ := b.constr ℚ q
    have hlam : ∀ x, R x = ((lam x : ℚ) : ℝ) := by
      intro x
      have : R = (Algebra.linearMap ℚ ℝ).comp lam := by
        apply b.ext
        intro j
        simp [lam, hq]
      rw [this]; simp
    have hnd := traceForm_nondegenerate ℚ E
    let l' : E := (LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm lam
    have hl' : ∀ x, Algebra.trace ℚ E (l' * x) = lam x := by
      intro x
      have := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm ℚ E) (hB := hnd) lam x
      rw [Algebra.traceForm_apply] at this
      exact this
    have hl : ∀ x, Algebra.trace ℚ E ((g : E) * l' * x / g) = lam x := by
      intro x
      rw [← hl' x]; congr 1; field_simp
    refine ⟨(g : E) * l', ?_, ?_⟩
    · intro y hy
      have h1 := hμ (semb E c y) (Submodule.mem_map_of_mem (f := (semb E c).toIntLinearMap) hy)
      obtain ⟨m, hm⟩ := Submodule.mem_one.mp h1
      refine ⟨m, ?_⟩
      rw [hl y]
      have : ((lam y : ℚ) : ℝ) = (m : ℝ) := by
        rw [← hlam, hR]; exact hm.symm.trans (by simp)
      have h5 : (lam y : ℚ) = (m : ℚ) := by exact_mod_cast this
      rw [h5]; simp
    · have : dm E g c ((g : E) * l') - μ = 0 := by
        apply orth_zero
        intro t
        have h1 := hT E g c ((g : E) * l') t hg hc
        rw [hl t, ← hlam, hR] at h1
        have h2 : inner ℝ (dm E g c ((g : E) * l') - μ) (semb E c t) = 0 := by
          rw [inner_sub_left, h1, sub_self]
        rw [semb_apply E c t, inner_smul_right] at h2
        exact (mul_eq_zero.mp h2).resolve_left hc
      exact sub_eq_zero.mp this
  · rintro ⟨l, hl, rfl⟩ y hy
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨m, hm⟩ := hl t ht
    rw [Submodule.mem_one]
    refine ⟨m, ?_⟩
    have := hT E g c l t hg hc
    show _ = inner ℝ (dm E g c l) (semb E c t)
    rw [this, ← hm]; simp

lemma rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
  exact_mod_cast this

lemma idl_ne_zero (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by
  intro h
  have h1 := hN E g k ν hg
  rw [h] at h1
  have hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E := by
    have := rd_pos E
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  simp at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos

lemma idl_zero_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (hg : 0 < g) :
    S6.idl E g 0 (-(ν + 1)) = S6.dualIdl E g ν * FractionalIdeal.spanSingleton _ (g : E) := by
  have hg' : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  unfold S6.dualIdl S6.idl
  rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
  congr 2
  rw [zpow_zero, zpow_neg_one, inv_mul_cancel₀ hg']

lemma sqrt_disc (hD : S6.DegreeFacts) (E : Type) [Field E] [NumberField E] [IsCMField E] :
    √((|discr E| : ℤ) : ℝ) = S6.rd E ^ S6.deg E := by
  obtain ⟨h1, -, h3⟩ := hD E
  have hd : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  unfold S6.rd
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd, h1, Real.sqrt_eq_rpow]
  congr 1
  have : (S6.deg E : ℝ) ≠ 0 := by exact_mod_cast h3.ne'
  push_cast
  field_simp

lemma norm_B (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ)
    (hg : 0 < g) : (FractionalIdeal.absNorm (S6.idl E g 0 (-(ν + 1))) : ℝ) =
      ((S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 := by
  have h := hN E g 0 (-(ν + 1)) hg
  rw [zpow_zero, one_mul] at h
  rw [← h, Real.sq_sqrt]
  exact_mod_cast (FractionalIdeal.absNorm_nonneg _)

open scoped Classical in
theorem t_DualCovolume : DualCovolume := by
  intro hDeg hConj hUnr hBet hIdx hSub hSup hNorm hCov E _ _ _ hU g ν s hg
  have hrd := rd_pos E
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hdual : S6.dualLat E g (S6.perLat E g ν s) =
      S6.twLat E (S6.dualIdl E g ν) (S6.idl E g 0 (-(ν + 1))) (s + 1) :=
    le_antisymm (hSub E g ν s hg) (hSup E hU g ν s hg)
  have hB := idl_zero_eq E g ν hg
  have hA0 : S6.dualIdl E g ν ≠ 0 := idl_ne_zero hNorm E g _ _ hg
  have hB0 : S6.idl E g 0 (-(ν + 1)) ≠ 0 := idl_ne_zero hNorm E g _ _ hg
  have hi := (hIdx E (S6.dualIdl E g ν) g (s + 1) hA0 (hConj E g _ _) hg ((hUnr E hU).2 g)).2
  rw [← hB, ← hdual] at hi
  have hle : S6.zsub E (S6.idl E g 0 (-(ν + 1))) ≤ S6.dualLat E g (S6.perLat E g ν s) := by
    rw [hdual]
    refine (hBet E _ _ (s + 1) ?_ (hConj E g _ _)).1
    rw [hB]
    have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ≤ 1 := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]
      exact ⟨(g : 𝓞 E), by simp⟩
    calc S6.dualIdl E g ν * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)
        ≤ S6.dualIdl E g ν * 1 := by gcongr
      _ = S6.dualIdl E g ν := mul_one _
  have hc : S6.rd E ^ (ν + 1) ≠ 0 := (zpow_pos hrd _).ne'
  have hidx0 : S6.idx E (S6.zsub E (S6.idl E g 0 (-(ν + 1)))) (S6.dualLat E g (S6.perLat E g ν s)) ≠ 0 := by
    rw [hi]; positivity
  obtain ⟨-, -, h3⟩ := hCov E _ _ (S6.rd E ^ (ν + 1)) hB0 hc hle hidx0
  rw [h3, hi, norm_B hNorm E g ν hg, sqrt_disc hDeg E, abs_of_pos (zpow_pos hrd _)]
  have e1 : (S6.rd E ^ (ν + 1)) ^ (2 * S6.deg E) * ((S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (S6.deg E) 2, ← mul_pow, ← zpow_add₀ hrd.ne']
    simp
  rw [e1, one_mul]
  push_cast
  rw [div_pow, div_pow, inv_pow]
  field_simp

open scoped Classical in
theorem t_DualMeasureBound : DualMeasureBound := by
  intro hDeg hConj hUnr hBet hIdx hSub hSup hNorm hCov E _ _ _ hU g ν s hg
  have hrd := rd_pos E
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hdual : S6.dualLat E g (S6.perLat E g ν s) =
      S6.twLat E (S6.dualIdl E g ν) (S6.idl E g 0 (-(ν + 1))) (s + 1) :=
    le_antisymm (hSub E g ν s hg) (hSup E hU g ν s hg)
  have hB := idl_zero_eq E g ν hg
  have hA0 : S6.dualIdl E g ν ≠ 0 := idl_ne_zero hNorm E g _ _ hg
  have hB0 : S6.idl E g 0 (-(ν + 1)) ≠ 0 := idl_ne_zero hNorm E g _ _ hg
  have hi := (hIdx E (S6.dualIdl E g ν) g (s + 1) hA0 (hConj E g _ _) hg ((hUnr E hU).2 g)).2
  rw [← hB, ← hdual] at hi
  have hle : S6.zsub E (S6.idl E g 0 (-(ν + 1))) ≤ S6.dualLat E g (S6.perLat E g ν s) := by
    rw [hdual]
    refine (hBet E _ _ (s + 1) ?_ (hConj E g _ _)).1
    rw [hB]
    have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ≤ 1 := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]
      exact ⟨(g : 𝓞 E), by simp⟩
    calc S6.dualIdl E g ν * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)
        ≤ S6.dualIdl E g ν * 1 := by gcongr
      _ = S6.dualIdl E g ν := mul_one _
  have hidx0 : S6.idx E (S6.zsub E (S6.idl E g 0 (-(ν + 1)))) (S6.dualLat E g (S6.perLat E g ν s)) ≠ 0 := by
    rw [hi]; positivity
  obtain ⟨-, -, h3⟩ := hCov E _ _ 1 hB0 one_ne_zero hle hidx0
  have hx : 0 < S6.rd E ^ (-(ν + 1)) := zpow_pos hrd _
  have hNA : (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) =
      (((g : ℝ) ^ (-1 : ℤ) * S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 := by
    have h := hNorm E g (-1) (-(ν + 1)) hg
    unfold S6.dualIdl
    rw [← h, Real.sq_sqrt]
    exact_mod_cast (FractionalIdeal.absNorm_nonneg _)
  have hval : ZLattice.covolume (E := mixedEmbedding.mixedSpace E)
      (S6.frameLat E (S6.dualLat E g (S6.perLat E g ν s)) 1) =
      ((g : ℝ) * (S6.rd E / 2)) ^ S6.deg E * (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) := by
    rw [h3, hi, norm_B hNorm E g ν hg, sqrt_disc hDeg E, hNA, abs_one, one_pow, one_mul]
    set x := S6.rd E ^ (-(ν + 1)) with hxdef
    push_cast
    rw [zpow_neg_one, mul_pow, mul_pow, div_pow, inv_pow, inv_pow, mul_pow]
    field_simp
  refine ⟨hval, fun h2 => ?_⟩
  rw [hval]
  have hn : 0 < (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) := by
    rw [hNA]; positivity
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have ha : 1 ≤ ((g : ℝ) * (S6.rd E / 2)) ^ S6.deg E := by
    apply one_le_pow₀
    nlinarith
  apply inv_anti₀ hn
  nlinarith

theorem t_DualCovolumeCV : DualCovolumeCV := by
  intro hL hE hB E _ _ _ hDL hCD hU g ν s hg
  obtain ⟨a, b, c⟩ := hB hL hE E hU g ν s hg
  have := a
  have : IsZLattice ℝ (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν))) := ⟨b⟩
  obtain ⟨d1, d2⟩ := hDL (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν)))
  have := d1
  have := d2
  rw [hCD (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν))), c]

section Poisson

open Formalism.H MeasureTheory
open scoped FourierTransform

theorem t_PoissonJoint : PoissonJoint := by
  intro h0 V _ _ _ _ _ ι _ π hπ Λ _ _ E _ emb dmap La Lad φ Cφ nh hinj hLa hd0 hcov hc hdec hpos hnh t₀ B hB S hS
  classical
  set F : V → ℂ := 𝓕 (fun v => (φ v : ℂ)) with hF
  have hcv : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos Λ volume
  choose σ hσL hσ using fun μ : dual Λ => hcov μ.1 μ.2
  have hσinj : Function.Injective σ := fun a b h => Subtype.ext (by rw [← hσ a, ← hσ b, h])
  have hσ0 : ∀ μ : dual Λ, μ ≠ 0 → σ μ ≠ 0 := by
    intro μ hμ h; apply hμ; apply Subtype.ext; rw [← hσ μ, h, hd0]; rfl
  have hnorm : ∀ μ : dual Λ, ‖nh (σ μ)‖ = (ZLattice.covolume Λ)⁻¹ * ‖F μ‖ := by
    intro μ; rw [hnh, hσ, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcv.le]
  have hfin : ∀ T : Finset {μ : dual Λ // μ ≠ 0},
      ∑ μ ∈ T, ‖F (μ : dual Λ)‖ ≤ ZLattice.covolume Λ * B := by
    intro T
    have := hB (T.image (fun μ => σ μ.1)) (by
      intro l hl; obtain ⟨μ, _, rfl⟩ := Finset.mem_image.1 hl; exact ⟨hσL _, hσ0 _ μ.2⟩)
    rw [Finset.sum_image (fun a _ b _ h => Subtype.ext (hσinj h))] at this
    simp_rw [hnorm, ← Finset.mul_sum] at this
    rwa [inv_mul_le_iff₀ hcv] at this
  have hsum' : Summable (fun μ : {μ : dual Λ // μ ≠ 0} => ‖F (μ : dual Λ)‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin
  have hts : ∑' μ : {μ : dual Λ // μ ≠ 0}, ‖F (μ : dual Λ)‖ ≤ ZLattice.covolume Λ * B :=
    hsum'.tsum_le_of_sum_le hfin
  have hsum : Summable (fun μ : dual Λ => ‖F μ‖) := by
    refine (Finset.summable_compl_iff ({0} : Finset (dual Λ))).1 ?_
    have e : {x : dual Λ // x ∉ ({0} : Finset (dual Λ))} ≃ {μ : dual Λ // μ ≠ 0} :=
      Equiv.subtypeEquivRight (fun x => by simp)
    refine (summable_of_sum_le (fun _ => norm_nonneg _) (c := ZLattice.covolume Λ * B) ?_)
    intro T
    have := hfin (T.map ⟨fun x => ⟨x.1, by simpa using x.2⟩, fun a b h => by
      have := congrArg (fun z => z.1) h; exact Subtype.ext this⟩)
    rw [Finset.sum_map] at this
    exact this
  obtain ⟨_, hP⟩ := h0 V ι π hπ Λ φ Cφ (emb t₀) hc hdec hsum (fun l => hpos _)
  have hmem : ∀ t ∈ S, emb (t - t₀) ∈ Λ := fun t ht => hLa _ (hS t ht)
  let S' : Finset Λ := S.attach.image (fun t => ⟨emb (t.1 - t₀), hmem t.1 t.2⟩)
  have h1 : ∑ t ∈ S, φ (emb t) = ∑ l ∈ S', φ ((l : V) + emb t₀) := by
    rw [Finset.sum_image]
    · rw [← Finset.sum_attach]; refine Finset.sum_congr rfl (fun t _ => ?_); simp [map_sub]
    · intro a _ b _ h
      have h2 : emb (a.1 - t₀) = emb (b.1 - t₀) := congrArg Subtype.val h
      have h3 := hinj h2
      exact Subtype.ext (by simpa using h3)
  rw [h1]
  refine (hP S').trans ?_
  unfold F7.poissonBound
  have hre : (F 0).re ≤ ‖F 0‖ := Complex.re_le_norm _
  have hn0 : ‖nh 0‖ = (ZLattice.covolume Λ)⁻¹ * ‖F 0‖ := by
    rw [hnh, hd0, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcv.le]
  rw [hn0, mul_add]
  refine add_le_add (mul_le_mul_of_nonneg_left hre (inv_nonneg.2 hcv.le)) ?_
  rw [inv_mul_le_iff₀ hcv]
  exact hts

end Poisson

end Formalism.FourierDecayAlt.P.Jx3

namespace Formalism.FourierDecayAlt.P

theorem trace_pairing : Formalism.FourierDecayAlt.J.TracePairing := Jx3.t_TracePairing

theorem trace_dual_alt : Formalism.FourierDecayAlt.J.TraceDual := Jx3.t_TraceDual

theorem block_frame : Formalism.FourierDecayAlt.J.BlockFrame := Jx3.t_BlockFrame

theorem dual_covolume : Formalism.FourierDecayAlt.J.DualCovolume := Jx3.t_DualCovolume

theorem dual_measure_bound : Formalism.FourierDecayAlt.J.DualMeasureBound := Jx3.t_DualMeasureBound

theorem dual_covolume_change_of_variables : Formalism.FourierDecayAlt.J.DualCovolumeCV := Jx3.t_DualCovolumeCV

theorem poisson_joint : Formalism.FourierDecayAlt.J.PoissonJoint := Jx3.t_PoissonJoint

end Formalism.FourierDecayAlt.P
